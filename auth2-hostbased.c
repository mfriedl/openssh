/* $OpenBSD: auth2-hostbased.c,v 1.52 2023/03/05 05:34:09 dtucker Exp $ */
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

#include <stdlib.h>
#include <pwd.h>
#include <string.h>
#include <stdarg.h>

#include "xmalloc.h"
#include "ssh2.h"
#include "packet.h"
#include "kex.h"
#include "sshbuf.h"
#include "log.h"
#include "misc.h"
#include "servconf.h"
#include "sshkey.h"
#include "hostfile.h"
#include "auth.h"
#include "canohost.h"
#ifdef GSSAPI
#include "ssh-gss.h"
#endif
#include "monitor_wrap.h"
#include "pathnames.h"
#include "ssherr.h"
#include "match.h"

/* import */
extern ServerOptions options;
extern struct authmethod_cfg methodcfg_hostbased;

static int
userauth_hostbased(struct ssh *ssh, const char *method)
{
	Authctxt *authctxt = ssh->authctxt;
	struct sshbuf *b;
	struct sshkey *key = NULL;
	char *pkalg, *cuser, *chost;
	u_char *pkblob, *sig;
	size_t alen, blen, slen;
	int r, pktype, authenticated = 0;

	/* XXX use sshkey_froms() */
	if ((r = sshpkt_get_cstring(ssh, &pkalg, &alen)) != 0 ||
	    (r = sshpkt_get_string(ssh, &pkblob, &blen)) != 0 ||
	    (r = sshpkt_get_cstring(ssh, &chost, NULL)) != 0 ||
	    (r = sshpkt_get_cstring(ssh, &cuser, NULL)) != 0 ||
	    (r = sshpkt_get_string(ssh, &sig, &slen)) != 0)
		fatal_fr(r, "parse packet");

	debug_f("cuser %s chost %s pkalg %s slen %zu",
	    cuser, chost, pkalg, slen);
#ifdef DEBUG_PK
	debug("signature:");
	sshbuf_dump_data(sig, slen, stderr);
#endif
	pktype = sshkey_type_from_name(pkalg);
	if (pktype == KEY_UNSPEC) {
		/* this is perfectly legal */
		logit_f("unsupported public key algorithm: %s",
		    pkalg);
		goto done;
	}
	if ((r = sshkey_from_blob(pkblob, blen, &key)) != 0) {
		error_fr(r, "key_from_blob");
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
	if (match_pattern_list(pkalg, options.hostbased_accepted_algos, 0) != 1) {
		logit_f("signature algorithm %s not in "
		    "HostbasedAcceptedAlgorithms", pkalg);
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

	if (!authctxt->valid || authctxt->user == NULL) {
		debug2_f("disabled because of invalid user");
		goto done;
	}

	if ((b = sshbuf_new()) == NULL)
		fatal_f("sshbuf_new failed");
	/* reconstruct packet */
	if ((r = sshbuf_put_stringb(b, ssh->kex->session_id)) != 0 ||
	    (r = sshbuf_put_u8(b, SSH2_MSG_USERAUTH_REQUEST)) != 0 ||
	    (r = sshbuf_put_cstring(b, authctxt->user)) != 0 ||
	    (r = sshbuf_put_cstring(b, authctxt->service)) != 0 ||
	    (r = sshbuf_put_cstring(b, method)) != 0 ||
	    (r = sshbuf_put_string(b, pkalg, alen)) != 0 ||
	    (r = sshbuf_put_string(b, pkblob, blen)) != 0 ||
	    (r = sshbuf_put_cstring(b, chost)) != 0 ||
	    (r = sshbuf_put_cstring(b, cuser)) != 0)
		fatal_fr(r, "reconstruct packet");
#ifdef DEBUG_PK
	sshbuf_dump(b, stderr);
#endif

	auth2_record_info(authctxt,
	    "client user \"%.100s\", client host \"%.100s\"", cuser, chost);

	/* test for allowed key and correct signature */
	authenticated = 0;
	if (mm_hostbased_key_allowed(ssh, authctxt->pw, cuser,
	    chost, key) &&
	    mm_sshkey_verify(key, sig, slen,
	    sshbuf_ptr(b), sshbuf_len(b), pkalg, ssh->compat, NULL) == 0)
		authenticated = 1;

	auth2_record_key(authctxt, authenticated, key);
	sshbuf_free(b);
done:
	debug2_f("authenticated %d", authenticated);
	sshkey_free(key);
	free(pkalg);
	free(pkblob);
	free(cuser);
	free(chost);
	free(sig);
	return authenticated;
}

Authmethod method_hostbased = {
	&methodcfg_hostbased,
	userauth_hostbased,
};
