/* $OpenBSD: auth.c,v 1.160 2023/03/05 05:34:09 dtucker Exp $ */
/*
 * Copyright (c) 2000 Markus Friedl.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/wait.h>

#include <stdlib.h>
#include <errno.h>
#include <fcntl.h>
#include <pwd.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>
#include <netdb.h>
#include <time.h>

#include "xmalloc.h"
#include "match.h"
#include "groupaccess.h"
#include "log.h"
#include "sshbuf.h"
#include "misc.h"
#include "servconf.h"
#include "sshkey.h"
#include "hostfile.h"
#include "auth.h"
#include "auth-options.h"
#include "canohost.h"
#include "packet.h"
#ifdef GSSAPI
#include "ssh-gss.h"
#endif
#include "authfile.h"
#include "monitor_wrap.h"
#include "ssherr.h"
#include "channels.h"

/* import */
extern ServerOptions options;

/* Debugging messages */
static struct sshbuf *auth_debug;

/*
 * Formats any key left in authctxt->auth_method_key for inclusion in
 * auth_log()'s message. Also includes authxtct->auth_method_info if present.
 */
static char *
format_method_key(Authctxt *authctxt)
{
	const struct sshkey *key = authctxt->auth_method_key;
	const char *methinfo = authctxt->auth_method_info;
	char *fp, *cafp, *ret = NULL;

	if (key == NULL)
		return NULL;

	if (sshkey_is_cert(key)) {
		fp = sshkey_fingerprint(key,
		    options.fingerprint_hash, SSH_FP_DEFAULT);
		cafp = sshkey_fingerprint(key->cert->signature_key,
		    options.fingerprint_hash, SSH_FP_DEFAULT);
		xasprintf(&ret, "%s %s ID %s (serial %llu) CA %s %s%s%s",
		    sshkey_type(key), fp == NULL ? "(null)" : fp,
		    key->cert->key_id,
		    (unsigned long long)key->cert->serial,
		    sshkey_type(key->cert->signature_key),
		    cafp == NULL ? "(null)" : cafp,
		    methinfo == NULL ? "" : ", ",
		    methinfo == NULL ? "" : methinfo);
		free(fp);
		free(cafp);
	} else {
		fp = sshkey_fingerprint(key, options.fingerprint_hash,
		    SSH_FP_DEFAULT);
		xasprintf(&ret, "%s %s%s%s", sshkey_type(key),
		    fp == NULL ? "(null)" : fp,
		    methinfo == NULL ? "" : ", ",
		    methinfo == NULL ? "" : methinfo);
		free(fp);
	}
	return ret;
}

void
auth_log(struct ssh *ssh, int authenticated, int partial,
    const char *method, const char *submethod)
{
	Authctxt *authctxt = (Authctxt *)ssh->authctxt;
	int level = SYSLOG_LEVEL_VERBOSE;
	const char *authmsg;
	char *extra = NULL;

	if (!mm_is_monitor() && !authctxt->postponed)
		return;

	/* Raise logging level */
	if (authenticated == 1 ||
	    !authctxt->valid ||
	    authctxt->failures >= options.max_authtries / 2 ||
	    strcmp(method, "password") == 0)
		level = SYSLOG_LEVEL_INFO;

	if (authctxt->postponed)
		authmsg = "Postponed";
	else if (partial)
		authmsg = "Partial";
	else
		authmsg = authenticated ? "Accepted" : "Failed";

	if ((extra = format_method_key(authctxt)) == NULL) {
		if (authctxt->auth_method_info != NULL)
			extra = xstrdup(authctxt->auth_method_info);
	}

	do_log2(level, "%s %s%s%s for %s%.100s from %.200s port %d ssh2%s%s",
	    authmsg,
	    method,
	    submethod != NULL ? "/" : "", submethod == NULL ? "" : submethod,
	    authctxt->valid ? "" : "invalid user ",
	    authctxt->user,
	    ssh_remote_ipaddr(ssh),
	    ssh_remote_port(ssh),
	    extra != NULL ? ": " : "",
	    extra != NULL ? extra : "");

	free(extra);
}

void
auth_debug_add(const char *fmt,...)
{
	char buf[1024];
	va_list args;
	int r;

	va_start(args, fmt);
	vsnprintf(buf, sizeof(buf), fmt, args);
	va_end(args);
	debug3("%s", buf);
	if (auth_debug != NULL)
		if ((r = sshbuf_put_cstring(auth_debug, buf)) != 0)
			fatal_fr(r, "sshbuf_put_cstring");
}

void
auth_debug_send(struct ssh *ssh)
{
	char *msg;
	int r;

	if (auth_debug == NULL)
		return;
	while (sshbuf_len(auth_debug) != 0) {
		if ((r = sshbuf_get_cstring(auth_debug, &msg, NULL)) != 0)
			fatal_fr(r, "sshbuf_get_cstring");
		ssh_packet_send_debug(ssh, "%s", msg);
		free(msg);
	}
}

void
auth_debug_reset(void)
{
	if (auth_debug != NULL)
		sshbuf_reset(auth_debug);
	else if ((auth_debug = sshbuf_new()) == NULL)
		fatal_f("sshbuf_new failed");
}

/* Log sshauthopt options locally and (optionally) for remote transmission */
void
auth_log_authopts(const char *loc, const struct sshauthopt *opts, int do_remote)
{
	int do_env = options.permit_user_env && opts->nenv > 0;
	int do_permitopen = opts->npermitopen > 0 &&
	    (options.allow_tcp_forwarding & FORWARD_LOCAL) != 0;
	int do_permitlisten = opts->npermitlisten > 0 &&
	    (options.allow_tcp_forwarding & FORWARD_REMOTE) != 0;
	size_t i;
	char msg[1024], buf[64];

	snprintf(buf, sizeof(buf), "%d", opts->force_tun_device);
	/* Try to keep this alphabetically sorted */
	snprintf(msg, sizeof(msg), "key options:%s%s%s%s%s%s%s%s%s%s%s%s%s%s%s",
	    opts->permit_agent_forwarding_flag ? " agent-forwarding" : "",
	    opts->force_command == NULL ? "" : " command",
	    do_env ?  " environment" : "",
	    opts->valid_before == 0 ? "" : "expires",
	    opts->no_require_user_presence ? " no-touch-required" : "",
	    do_permitopen ?  " permitopen" : "",
	    do_permitlisten ?  " permitlisten" : "",
	    opts->permit_port_forwarding_flag ? " port-forwarding" : "",
	    opts->cert_principals == NULL ? "" : " principals",
	    opts->permit_pty_flag ? " pty" : "",
	    opts->require_verify ? " uv" : "",
	    opts->force_tun_device == -1 ? "" : " tun=",
	    opts->force_tun_device == -1 ? "" : buf,
	    opts->permit_user_rc ? " user-rc" : "",
	    opts->permit_x11_forwarding_flag ? " x11-forwarding" : "");

	debug("%s: %s", loc, msg);
	if (do_remote)
		auth_debug_add("%s: %s", loc, msg);

	if (options.permit_user_env) {
		for (i = 0; i < opts->nenv; i++) {
			debug("%s: environment: %s", loc, opts->env[i]);
			if (do_remote) {
				auth_debug_add("%s: environment: %s",
				    loc, opts->env[i]);
			}
		}
	}

	/* Go into a little more details for the local logs. */
	if (opts->valid_before != 0) {
		format_absolute_time(opts->valid_before, buf, sizeof(buf));
		debug("%s: expires at %s", loc, buf);
	}
	if (opts->cert_principals != NULL) {
		debug("%s: authorized principals: \"%s\"",
		    loc, opts->cert_principals);
	}
	if (opts->force_command != NULL)
		debug("%s: forced command: \"%s\"", loc, opts->force_command);
	if (do_permitopen) {
		for (i = 0; i < opts->npermitopen; i++) {
			debug("%s: permitted open: %s",
			    loc, opts->permitopen[i]);
		}
	}
	if (do_permitlisten) {
		for (i = 0; i < opts->npermitlisten; i++) {
			debug("%s: permitted listen: %s",
			    loc, opts->permitlisten[i]);
		}
	}
}
