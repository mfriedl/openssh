/* $OpenBSD: auth2-pubkey.c,v 1.118 2023/02/17 04:22:50 dtucker Exp $ */
/*
 * Copyright (c) 2000 Markus Friedl.  All rights reserved.
 * Copyright (c) 2010 Damien Miller.  All rights reserved.
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

#include <stdlib.h>
#include <errno.h>
#include <paths.h>
#include <pwd.h>
#include <signal.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <limits.h>

#include "xmalloc.h"
#include "ssh.h"
#include "ssh2.h"
#include "packet.h"
#include "kex.h"
#include "sshbuf.h"
#include "log.h"
#include "misc.h"
#include "servconf.h"
#include "compat.h"
#include "sshkey.h"
#include "hostfile.h"
#include "auth.h"
#include "pathnames.h"
#include "uidswap.h"
#include "auth-options.h"
#include "canohost.h"
#ifdef GSSAPI
#include "ssh-gss.h"
#endif
#include "monitor_wrap.h"
#include "authfile.h"
#include "match.h"
#include "ssherr.h"
#include "channels.h" /* XXX for session.h */
#include "session.h" /* XXX for child_set_env(); refactor? */
#include "sk-api.h"

/* import */
extern ServerOptions options;
extern struct authmethod_cfg methodcfg_pubkey;

static char *
format_key(const struct sshkey *key)
{
	char *ret, *fp = sshkey_fingerprint(key,
	    options.fingerprint_hash, SSH_FP_DEFAULT);

	xasprintf(&ret, "%s %s", sshkey_type(key), fp);
	free(fp);
	return ret;
}

static int
userauth_pubkey(struct ssh *ssh, const char *method)
{
	Authctxt *authctxt = ssh->authctxt;
	struct passwd *pw = authctxt->pw;
	struct sshbuf *b = NULL;
	struct sshkey *key = NULL, *hostkey = NULL;
	char *pkalg = NULL, *userstyle = NULL, *key_s = NULL, *ca_s = NULL;
	u_char *pkblob = NULL, *sig = NULL, have_sig;
	size_t blen, slen;
	int hostbound, r, pktype;
	int req_presence = 0, req_verify = 0, authenticated = 0;
	struct sshauthopt *authopts = NULL;
	struct sshkey_sig_details *sig_details = NULL;

	hostbound = strcmp(method, "publickey-hostbound-v00@openssh.com") == 0;

	if ((r = sshpkt_get_u8(ssh, &have_sig)) != 0 ||
	    (r = sshpkt_get_cstring(ssh, &pkalg, NULL)) != 0 ||
	    (r = sshpkt_get_string(ssh, &pkblob, &blen)) != 0)
		fatal_fr(r, "parse %s packet", method);

	/* hostbound auth includes the hostkey offered at initial KEX */
	if (hostbound) {
		if ((r = sshpkt_getb_froms(ssh, &b)) != 0 ||
		    (r = sshkey_fromb(b, &hostkey)) != 0)
			fatal_fr(r, "parse %s hostkey", method);
		if (ssh->kex->initial_hostkey == NULL)
			fatal_f("internal error: initial hostkey not recorded");
		if (!sshkey_equal(hostkey, ssh->kex->initial_hostkey))
			fatal_f("%s packet contained wrong host key", method);
		sshbuf_free(b);
		b = NULL;
	}

	if (log_level_get() >= SYSLOG_LEVEL_DEBUG2) {
		char *keystring;
		struct sshbuf *pkbuf;

		if ((pkbuf = sshbuf_from(pkblob, blen)) == NULL)
			fatal_f("sshbuf_from failed");
		if ((keystring = sshbuf_dtob64_string(pkbuf, 0)) == NULL)
			fatal_f("sshbuf_dtob64 failed");
		debug2_f("%s user %s %s public key %s %s",
		    authctxt->valid ? "valid" : "invalid", authctxt->user,
		    have_sig ? "attempting" : "querying", pkalg, keystring);
		sshbuf_free(pkbuf);
		free(keystring);
	}

	pktype = sshkey_type_from_name(pkalg);
	if (pktype == KEY_UNSPEC) {
		/* this is perfectly legal */
		verbose_f("unsupported public key algorithm: %s", pkalg);
		goto done;
	}
	if ((r = sshkey_from_blob(pkblob, blen, &key)) != 0) {
		error_fr(r, "parse key");
		goto done;
	}
	if (key == NULL) {
		error_f("cannot decode key: %s", pkalg);
		goto done;
	}
	if (key->type != pktype) {
		error_f("type mismatch for decoded key "
		    "(received %d, expected %d)", key->type, pktype);
		goto done;
	}
	if (auth2_key_already_used(authctxt, key)) {
		logit("refusing previously-used %s key", sshkey_type(key));
		goto done;
	}
	if (match_pattern_list(pkalg, options.pubkey_accepted_algos, 0) != 1) {
		logit_f("signature algorithm %s not in "
		    "PubkeyAcceptedAlgorithms", pkalg);
		goto done;
	}
	if ((r = sshkey_check_cert_sigtype(key,
	    options.ca_sign_algorithms)) != 0) {
		logit_fr(r, "certificate signature algorithm %s",
		    (key->cert == NULL || key->cert->signature_type == NULL) ?
		    "(null)" : key->cert->signature_type);
		goto done;
	}
	if ((r = sshkey_check_rsa_length(key,
	    options.required_rsa_size)) != 0) {
		logit_r(r, "refusing %s key", sshkey_type(key));
		goto done;
	}
	key_s = format_key(key);
	if (sshkey_is_cert(key))
		ca_s = format_key(key->cert->signature_key);

	if (have_sig) {
		debug3_f("%s have %s signature for %s%s%s",
		    method, pkalg, key_s,
		    ca_s == NULL ? "" : " CA ", ca_s == NULL ? "" : ca_s);
		if ((r = sshpkt_get_string(ssh, &sig, &slen)) != 0 ||
		    (r = sshpkt_get_end(ssh)) != 0)
			fatal_fr(r, "parse signature packet");
		if ((b = sshbuf_new()) == NULL)
			fatal_f("sshbuf_new failed");
		if (ssh->compat & SSH_OLD_SESSIONID) {
			if ((r = sshbuf_putb(b, ssh->kex->session_id)) != 0)
				fatal_fr(r, "put old session id");
		} else {
			if ((r = sshbuf_put_stringb(b,
			    ssh->kex->session_id)) != 0)
				fatal_fr(r, "put session id");
		}
		if (!authctxt->valid || authctxt->user == NULL) {
			debug2_f("disabled because of invalid user");
			goto done;
		}
		/* reconstruct packet */
		xasprintf(&userstyle, "%s%s%s", authctxt->user,
		    authctxt->style ? ":" : "",
		    authctxt->style ? authctxt->style : "");
		if ((r = sshbuf_put_u8(b, SSH2_MSG_USERAUTH_REQUEST)) != 0 ||
		    (r = sshbuf_put_cstring(b, userstyle)) != 0 ||
		    (r = sshbuf_put_cstring(b, authctxt->service)) != 0 ||
		    (r = sshbuf_put_cstring(b, method)) != 0 ||
		    (r = sshbuf_put_u8(b, have_sig)) != 0 ||
		    (r = sshbuf_put_cstring(b, pkalg)) != 0 ||
		    (r = sshbuf_put_string(b, pkblob, blen)) != 0)
			fatal_fr(r, "reconstruct %s packet", method);
		if (hostbound &&
		    (r = sshkey_puts(ssh->kex->initial_hostkey, b)) != 0)
			fatal_fr(r, "reconstruct %s packet", method);
#ifdef DEBUG_PK
		sshbuf_dump(b, stderr);
#endif
		/* test for correct signature */
		authenticated = 0;
		if (mm_user_key_allowed(ssh, pw, key, 1, &authopts) &&
		    mm_sshkey_verify(key, sig, slen,
		    sshbuf_ptr(b), sshbuf_len(b),
		    (ssh->compat & SSH_BUG_SIGTYPE) == 0 ? pkalg : NULL,
		    ssh->compat, &sig_details) == 0) {
			authenticated = 1;
		}
		if (authenticated == 1 && sig_details != NULL) {
			auth2_record_info(authctxt, "signature count = %u",
			    sig_details->sk_counter);
			debug_f("sk_counter = %u, sk_flags = 0x%02x",
			    sig_details->sk_counter, sig_details->sk_flags);
			req_presence = (options.pubkey_auth_options &
			    PUBKEYAUTH_TOUCH_REQUIRED) ||
			    !authopts->no_require_user_presence;
			if (req_presence && (sig_details->sk_flags &
			    SSH_SK_USER_PRESENCE_REQD) == 0) {
				error("public key %s signature for %s%s from "
				    "%.128s port %d rejected: user presence "
				    "(authenticator touch) requirement "
				    "not met ", key_s,
				    authctxt->valid ? "" : "invalid user ",
				    authctxt->user, ssh_remote_ipaddr(ssh),
				    ssh_remote_port(ssh));
				authenticated = 0;
				goto done;
			}
			req_verify = (options.pubkey_auth_options &
			    PUBKEYAUTH_VERIFY_REQUIRED) ||
			    authopts->require_verify;
			if (req_verify && (sig_details->sk_flags &
			    SSH_SK_USER_VERIFICATION_REQD) == 0) {
				error("public key %s signature for %s%s from "
				    "%.128s port %d rejected: user "
				    "verification requirement not met ", key_s,
				    authctxt->valid ? "" : "invalid user ",
				    authctxt->user, ssh_remote_ipaddr(ssh),
				    ssh_remote_port(ssh));
				authenticated = 0;
				goto done;
			}
		}
		auth2_record_key(authctxt, authenticated, key);
	} else {
		debug_f("%s test pkalg %s pkblob %s%s%s", method, pkalg, key_s,
		    ca_s == NULL ? "" : " CA ", ca_s == NULL ? "" : ca_s);

		if ((r = sshpkt_get_end(ssh)) != 0)
			fatal_fr(r, "parse packet");

		if (!authctxt->valid || authctxt->user == NULL) {
			debug2_f("disabled because of invalid user");
			goto done;
		}
		/* XXX fake reply and always send PK_OK ? */
		/*
		 * XXX this allows testing whether a user is allowed
		 * to login: if you happen to have a valid pubkey this
		 * message is sent. the message is NEVER sent at all
		 * if a user is not allowed to login. is this an
		 * issue? -markus
		 */
		if (mm_user_key_allowed(ssh, pw, key, 0, NULL)) {
			if ((r = sshpkt_start(ssh, SSH2_MSG_USERAUTH_PK_OK))
			    != 0 ||
			    (r = sshpkt_put_cstring(ssh, pkalg)) != 0 ||
			    (r = sshpkt_put_string(ssh, pkblob, blen)) != 0 ||
			    (r = sshpkt_send(ssh)) != 0 ||
			    (r = ssh_packet_write_wait(ssh)) != 0)
				fatal_fr(r, "send packet");
			authctxt->postponed = 1;
		}
	}
done:
	if (authenticated == 1 && auth_activate_options(ssh, authopts) != 0) {
		debug_f("key options inconsistent with existing");
		authenticated = 0;
	}
	debug2_f("authenticated %d pkalg %s", authenticated, pkalg);

	sshbuf_free(b);
	sshauthopt_free(authopts);
	sshkey_free(key);
	sshkey_free(hostkey);
	free(userstyle);
	free(pkalg);
	free(pkblob);
	free(key_s);
	free(ca_s);
	free(sig);
	sshkey_sig_details_free(sig_details);
	return authenticated;
}

Authmethod method_pubkey = {
	&methodcfg_pubkey,
	userauth_pubkey,
};
