/* $OpenBSD: auth2.c,v 1.166 2023/03/08 04:43:12 guenther Exp $ */
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
#include <sys/uio.h>

#include <fcntl.h>
#include <limits.h>
#include <pwd.h>
#include <stdarg.h>
#include <string.h>
#include <unistd.h>
#include <time.h>

#include "stdlib.h"
#include "atomicio.h"
#include "xmalloc.h"
#include "ssh2.h"
#include "packet.h"
#include "log.h"
#include "sshbuf.h"
#include "misc.h"
#include "servconf.h"
#include "sshkey.h"
#include "hostfile.h"
#include "auth.h"
#include "auth-options.h"
#include "dispatch.h"
#include "pathnames.h"
#ifdef GSSAPI
#include "ssh-gss.h"
#endif
#include "monitor_wrap.h"
#include "ssherr.h"
#include "digest.h"

/* import */
extern ServerOptions options;
extern struct sshauthopt *auth_opts;

/* methods */

extern Authmethod method_none;
extern Authmethod method_pubkey;
extern Authmethod method_passwd;
extern Authmethod method_kbdint;
extern Authmethod method_hostbased;
#ifdef GSSAPI
extern Authmethod method_gssapi;
#endif

Authmethod *authmethods[] = {
	&method_none,
	&method_pubkey,
#ifdef GSSAPI
	&method_gssapi,
#endif
	&method_passwd,
	&method_kbdint,
	&method_hostbased,
	NULL
};

#define MATCH_NONE	0	/* method or submethod mismatch */
#define MATCH_METHOD	1	/* method matches (no submethod specified) */
#define MATCH_BOTH	2	/* method and submethod match */
#define MATCH_PARTIAL	3	/* method matches, submethod can't be checked */
static int list_starts_with(const char *, const char *, const char *);

/*
 * Checks whether method is allowed by at least one AuthenticationMethods
 * methods list. Returns 1 if allowed, or no methods lists configured.
 * 0 otherwise.
 */
int
auth2_method_allowed(Authctxt *authctxt, const char *method,
    const char *submethod)
{
	u_int i;

	/*
	 * NB. authctxt->num_auth_methods might be zero as a result of
	 * auth2_setup_methods_lists(), so check the configuration.
	 */
	if (options.num_auth_methods == 0)
		return 1;
	for (i = 0; i < authctxt->num_auth_methods; i++) {
		if (list_starts_with(authctxt->auth_methods[i], method,
		    submethod) != MATCH_NONE)
			return 1;
	}
	return 0;
}

char *
authmethods_get(Authctxt *authctxt)
{
	struct sshbuf *b;
	char *list;
	int i, r;

	if ((b = sshbuf_new()) == NULL)
		fatal_f("sshbuf_new failed");
	for (i = 0; authmethods[i] != NULL; i++) {
		if (strcmp(authmethods[i]->cfg->name, "none") == 0)
			continue;
		if (authmethods[i]->cfg->enabled == NULL ||
		    *(authmethods[i]->cfg->enabled) == 0)
			continue;
		if (!auth2_method_allowed(authctxt, authmethods[i]->cfg->name,
		    NULL))
			continue;
		if ((r = sshbuf_putf(b, "%s%s", sshbuf_len(b) ? "," : "",
		    authmethods[i]->cfg->name)) != 0)
			fatal_fr(r, "buffer error");
	}
	if ((list = sshbuf_dup_string(b)) == NULL)
		fatal_f("sshbuf_dup_string failed");
	sshbuf_free(b);
	return list;
}

Authmethod *
authmethod_byname(const char *name)
{
	int i;

	if (name == NULL)
		fatal_f("NULL authentication method name");
	for (i = 0; authmethods[i] != NULL; i++) {
		if (strcmp(name, authmethods[i]->cfg->name) == 0 ||
		    (authmethods[i]->cfg->synonym != NULL &&
		    strcmp(name, authmethods[i]->cfg->synonym) == 0))
			return authmethods[i];
	}
	debug_f("unrecognized authentication method name: %s", name);
	return NULL;
}

Authmethod *
authmethod_lookup(Authctxt *authctxt, const char *name)
{
	Authmethod *method;

	if ((method = authmethod_byname(name)) == NULL)
		return NULL;

	if (method->cfg->enabled == NULL || *(method->cfg->enabled) == 0) {
		debug3_f("method %s not enabled", name);
		return NULL;
	}
	if (!auth2_method_allowed(authctxt, method->cfg->name, NULL)) {
		debug3_f("method %s not allowed "
		    "by AuthenticationMethods", name);
		return NULL;
	}
	return method;
}

/*
 * Prune the AuthenticationMethods supplied in the configuration, removing
 * any methods lists that include disabled methods. Note that this might
 * leave authctxt->num_auth_methods == 0, even when multiple required auth
 * has been requested. For this reason, all tests for whether multiple is
 * enabled should consult options.num_auth_methods directly.
 */
int
auth2_setup_methods_lists(Authctxt *authctxt)
{
	u_int i;

	/* First, normalise away the "any" pseudo-method */
	if (options.num_auth_methods == 1 &&
	    strcmp(options.auth_methods[0], "any") == 0) {
		free(options.auth_methods[0]);
		options.auth_methods[0] = NULL;
		options.num_auth_methods = 0;
	}

	if (options.num_auth_methods == 0)
		return 0;
	debug3_f("checking methods");
	authctxt->auth_methods = xcalloc(options.num_auth_methods,
	    sizeof(*authctxt->auth_methods));
	authctxt->num_auth_methods = 0;
	for (i = 0; i < options.num_auth_methods; i++) {
		if (auth2_methods_valid(options.auth_methods[i], 1) != 0) {
			logit("Authentication methods list \"%s\" contains "
			    "disabled method, skipping",
			    options.auth_methods[i]);
			continue;
		}
		debug("authentication methods list %d: %s",
		    authctxt->num_auth_methods, options.auth_methods[i]);
		authctxt->auth_methods[authctxt->num_auth_methods++] =
		    xstrdup(options.auth_methods[i]);
	}
	if (authctxt->num_auth_methods == 0) {
		error("No AuthenticationMethods left after eliminating "
		    "disabled methods");
		return -1;
	}
	return 0;
}

static int
list_starts_with(const char *methods, const char *method,
    const char *submethod)
{
	size_t l = strlen(method);
	int match;
	const char *p;

	if (strncmp(methods, method, l) != 0)
		return MATCH_NONE;
	p = methods + l;
	match = MATCH_METHOD;
	if (*p == ':') {
		if (!submethod)
			return MATCH_PARTIAL;
		l = strlen(submethod);
		p += 1;
		if (strncmp(submethod, p, l))
			return MATCH_NONE;
		p += l;
		match = MATCH_BOTH;
	}
	if (*p != ',' && *p != '\0')
		return MATCH_NONE;
	return match;
}

/*
 * Remove method from the start of a comma-separated list of methods.
 * Returns 0 if the list of methods did not start with that method or 1
 * if it did.
 */
static int
remove_method(char **methods, const char *method, const char *submethod)
{
	char *omethods = *methods, *p;
	size_t l = strlen(method);
	int match;

	match = list_starts_with(omethods, method, submethod);
	if (match != MATCH_METHOD && match != MATCH_BOTH)
		return 0;
	p = omethods + l;
	if (submethod && match == MATCH_BOTH)
		p += 1 + strlen(submethod); /* include colon */
	if (*p == ',')
		p++;
	*methods = xstrdup(p);
	free(omethods);
	return 1;
}

/*
 * Called after successful authentication. Will remove the successful method
 * from the start of each list in which it occurs. If it was the last method
 * in any list, then authentication is deemed successful.
 * Returns 1 if the method completed any authentication list or 0 otherwise.
 */
int
auth2_update_methods_lists(Authctxt *authctxt, const char *method,
    const char *submethod)
{
	u_int i, found = 0;

	debug3_f("updating methods list after \"%s\"", method);
	for (i = 0; i < authctxt->num_auth_methods; i++) {
		if (!remove_method(&(authctxt->auth_methods[i]), method,
		    submethod))
			continue;
		found = 1;
		if (*authctxt->auth_methods[i] == '\0') {
			debug2("authentication methods list %d complete", i);
			return 1;
		}
		debug3("authentication methods list %d remaining: \"%s\"",
		    i, authctxt->auth_methods[i]);
	}
	/* This should not happen, but would be bad if it did */
	if (!found)
		fatal_f("method not in AuthenticationMethods");
	return 0;
}

/* Reset method-specific information */
void auth2_authctxt_reset_info(Authctxt *authctxt)
{
	sshkey_free(authctxt->auth_method_key);
	free(authctxt->auth_method_info);
	authctxt->auth_method_key = NULL;
	authctxt->auth_method_info = NULL;
}

/* Record auth method-specific information for logs */
void
auth2_record_info(Authctxt *authctxt, const char *fmt, ...)
{
	va_list ap;
	int i;

	free(authctxt->auth_method_info);
	authctxt->auth_method_info = NULL;

	va_start(ap, fmt);
	i = vasprintf(&authctxt->auth_method_info, fmt, ap);
	va_end(ap);

	if (i == -1)
		fatal_f("vasprintf failed");
}

/*
 * Records a public key used in authentication. This is used for logging
 * and to ensure that the same key is not subsequently accepted again for
 * multiple authentication.
 */
void
auth2_record_key(Authctxt *authctxt, int authenticated,
    const struct sshkey *key)
{
	struct sshkey **tmp, *dup;
	int r;

	if ((r = sshkey_from_private(key, &dup)) != 0)
		fatal_fr(r, "copy key");
	sshkey_free(authctxt->auth_method_key);
	authctxt->auth_method_key = dup;

	if (!authenticated)
		return;

	/* If authenticated, make sure we don't accept this key again */
	if ((r = sshkey_from_private(key, &dup)) != 0)
		fatal_fr(r, "copy key");
	if (authctxt->nprev_keys >= INT_MAX ||
	    (tmp = recallocarray(authctxt->prev_keys, authctxt->nprev_keys,
	    authctxt->nprev_keys + 1, sizeof(*authctxt->prev_keys))) == NULL)
		fatal_f("reallocarray failed");
	authctxt->prev_keys = tmp;
	authctxt->prev_keys[authctxt->nprev_keys] = dup;
	authctxt->nprev_keys++;

}

/* Checks whether a key has already been previously used for authentication */
int
auth2_key_already_used(Authctxt *authctxt, const struct sshkey *key)
{
	u_int i;
	char *fp;

	for (i = 0; i < authctxt->nprev_keys; i++) {
		if (sshkey_equal_public(key, authctxt->prev_keys[i])) {
			fp = sshkey_fingerprint(authctxt->prev_keys[i],
			    options.fingerprint_hash, SSH_FP_DEFAULT);
			debug3_f("key already used: %s %s",
			    sshkey_type(authctxt->prev_keys[i]),
			    fp == NULL ? "UNKNOWN" : fp);
			free(fp);
			return 1;
		}
	}
	return 0;
}

/*
 * Updates authctxt->session_info with details of authentication. Should be
 * whenever an authentication method succeeds.
 */
void
auth2_update_session_info(Authctxt *authctxt, const char *method,
    const char *submethod)
{
	int r;

	if (authctxt->session_info == NULL) {
		if ((authctxt->session_info = sshbuf_new()) == NULL)
			fatal_f("sshbuf_new");
	}

	/* Append method[/submethod] */
	if ((r = sshbuf_putf(authctxt->session_info, "%s%s%s",
	    method, submethod == NULL ? "" : "/",
	    submethod == NULL ? "" : submethod)) != 0)
		fatal_fr(r, "append method");

	/* Append key if present */
	if (authctxt->auth_method_key != NULL) {
		if ((r = sshbuf_put_u8(authctxt->session_info, ' ')) != 0 ||
		    (r = sshkey_format_text(authctxt->auth_method_key,
		    authctxt->session_info)) != 0)
			fatal_fr(r, "append key");
	}

	if (authctxt->auth_method_info != NULL) {
		/* Ensure no ambiguity here */
		if (strchr(authctxt->auth_method_info, '\n') != NULL)
			fatal_f("auth_method_info contains \\n");
		if ((r = sshbuf_put_u8(authctxt->session_info, ' ')) != 0 ||
		    (r = sshbuf_putf(authctxt->session_info, "%s",
		    authctxt->auth_method_info)) != 0) {
			fatal_fr(r, "append method info");
		}
	}
	if ((r = sshbuf_put_u8(authctxt->session_info, '\n')) != 0)
		fatal_fr(r, "append");
}

/*
 * Check whether root logins are disallowed.
 */
int
auth_root_allowed(struct ssh *ssh, const char *method)
{
	switch (options.permit_root_login) {
	case PERMIT_YES:
		return 1;
	case PERMIT_NO_PASSWD:
		if (strcmp(method, "publickey") == 0 ||
		    strcmp(method, "hostbased") == 0 ||
		    strcmp(method, "gssapi-with-mic") == 0)
			return 1;
		break;
	case PERMIT_FORCED_ONLY:
		if (auth_opts->force_command != NULL) {
			logit("Root login accepted for forced command.");
			return 1;
		}
		break;
	}
	logit("ROOT LOGIN REFUSED FROM %.200s port %d",
	    ssh_remote_ipaddr(ssh), ssh_remote_port(ssh));
	return 0;
}
