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
#include <login_cap.h>
#include <paths.h>
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
extern struct include_list includes;

/* XXX used by session.c */
login_cap_t *lc;

/*
 * Check if the user is allowed to log in via ssh. If user is listed
 * in DenyUsers or one of user's groups is listed in DenyGroups, false
 * will be returned. If AllowUsers isn't empty and user isn't listed
 * there, or if AllowGroups isn't empty and one of user's groups isn't
 * listed there, false will be returned.
 * If the user's shell is not executable, false will be returned.
 * Otherwise true is returned.
 */
static int
allowed_user(struct ssh *ssh, struct passwd * pw)
{
	struct stat st;
	const char *hostname = NULL, *ipaddr = NULL;
	int r;
	u_int i;

	/* Shouldn't be called if pw is NULL, but better safe than sorry... */
	if (!pw || !pw->pw_name)
		return 0;

	/*
	 * Deny if shell does not exist or is not executable unless we
	 * are chrooting.
	 */
	if (options.chroot_directory == NULL ||
	    strcasecmp(options.chroot_directory, "none") == 0) {
		char *shell = xstrdup((pw->pw_shell[0] == '\0') ?
		    _PATH_BSHELL : pw->pw_shell); /* empty = /bin/sh */

		if (stat(shell, &st) == -1) {
			logit("User %.100s not allowed because shell %.100s "
			    "does not exist", pw->pw_name, shell);
			free(shell);
			return 0;
		}
		if (S_ISREG(st.st_mode) == 0 ||
		    (st.st_mode & (S_IXOTH|S_IXUSR|S_IXGRP)) == 0) {
			logit("User %.100s not allowed because shell %.100s "
			    "is not executable", pw->pw_name, shell);
			free(shell);
			return 0;
		}
		free(shell);
	}

	if (options.num_deny_users > 0 || options.num_allow_users > 0 ||
	    options.num_deny_groups > 0 || options.num_allow_groups > 0) {
		hostname = auth_get_canonical_hostname(ssh, options.use_dns);
		ipaddr = ssh_remote_ipaddr(ssh);
	}

	/* Return false if user is listed in DenyUsers */
	if (options.num_deny_users > 0) {
		for (i = 0; i < options.num_deny_users; i++) {
			r = match_user(pw->pw_name, hostname, ipaddr,
			    options.deny_users[i]);
			if (r < 0) {
				fatal("Invalid DenyUsers pattern \"%.100s\"",
				    options.deny_users[i]);
			} else if (r != 0) {
				logit("User %.100s from %.100s not allowed "
				    "because listed in DenyUsers",
				    pw->pw_name, hostname);
				return 0;
			}
		}
	}
	/* Return false if AllowUsers isn't empty and user isn't listed there */
	if (options.num_allow_users > 0) {
		for (i = 0; i < options.num_allow_users; i++) {
			r = match_user(pw->pw_name, hostname, ipaddr,
			    options.allow_users[i]);
			if (r < 0) {
				fatal("Invalid AllowUsers pattern \"%.100s\"",
				    options.allow_users[i]);
			} else if (r == 1)
				break;
		}
		/* i < options.num_allow_users iff we break for loop */
		if (i >= options.num_allow_users) {
			logit("User %.100s from %.100s not allowed because "
			    "not listed in AllowUsers", pw->pw_name, hostname);
			return 0;
		}
	}
	if (options.num_deny_groups > 0 || options.num_allow_groups > 0) {
		/* Get the user's group access list (primary and supplementary) */
		if (ga_init(pw->pw_name, pw->pw_gid) == 0) {
			logit("User %.100s from %.100s not allowed because "
			    "not in any group", pw->pw_name, hostname);
			return 0;
		}

		/* Return false if one of user's groups is listed in DenyGroups */
		if (options.num_deny_groups > 0)
			if (ga_match(options.deny_groups,
			    options.num_deny_groups)) {
				ga_free();
				logit("User %.100s from %.100s not allowed "
				    "because a group is listed in DenyGroups",
				    pw->pw_name, hostname);
				return 0;
			}
		/*
		 * Return false if AllowGroups isn't empty and one of user's groups
		 * isn't listed there
		 */
		if (options.num_allow_groups > 0)
			if (!ga_match(options.allow_groups,
			    options.num_allow_groups)) {
				ga_free();
				logit("User %.100s from %.100s not allowed "
				    "because none of user's groups are listed "
				    "in AllowGroups", pw->pw_name, hostname);
				return 0;
			}
		ga_free();
	}
	/* We found no reason not to let this user try to log on... */
	return 1;
}

struct passwd *
getpwnamallow(struct ssh *ssh, const char *user)
{
	auth_session_t *as;
	struct passwd *pw;
	struct connection_info *ci;
	u_int i;

	ci = get_connection_info(ssh, 1, options.use_dns);
	ci->user = user;
	parse_server_match_config(&options, &includes, ci);
	log_change_level(options.log_level);
	log_verbose_reset();
	for (i = 0; i < options.num_log_verbose; i++)
		log_verbose_add(options.log_verbose[i]);
	server_process_permitopen(ssh);

	pw = getpwnam(user);
	if (pw == NULL) {
		logit("Invalid user %.100s from %.100s port %d",
		    user, ssh_remote_ipaddr(ssh), ssh_remote_port(ssh));
		return (NULL);
	}
	if (!allowed_user(ssh, pw))
		return (NULL);
	if ((lc = login_getclass(pw->pw_class)) == NULL) {
		debug("unable to get login class: %s", user);
		return (NULL);
	}
	if ((as = auth_open()) == NULL || auth_setpwd(as, pw) != 0 ||
	    auth_approval(as, lc, pw->pw_name, "ssh") <= 0) {
		debug("Approval failure for %s", user);
		pw = NULL;
	}
	if (as != NULL)
		auth_close(as);
	if (pw != NULL)
		return (pwcopy(pw));
	return (NULL);
}

/* Returns 1 if key is revoked by revoked_keys_file, 0 otherwise */
int
auth_key_is_revoked(struct sshkey *key)
{
	char *fp = NULL;
	int r;

	if (options.revoked_keys_file == NULL)
		return 0;
	if ((fp = sshkey_fingerprint(key, options.fingerprint_hash,
	    SSH_FP_DEFAULT)) == NULL) {
		r = SSH_ERR_ALLOC_FAIL;
		error_fr(r, "fingerprint key");
		goto out;
	}

	r = sshkey_check_revoked(key, options.revoked_keys_file);
	switch (r) {
	case 0:
		break; /* not revoked */
	case SSH_ERR_KEY_REVOKED:
		error("Authentication key %s %s revoked by file %s",
		    sshkey_type(key), fp, options.revoked_keys_file);
		goto out;
	default:
		error_r(r, "Error checking authentication key %s %s in "
		    "revoked keys file %s", sshkey_type(key), fp,
		    options.revoked_keys_file);
		goto out;
	}

	/* Success */
	r = 0;

 out:
	free(fp);
	return r == 0 ? 0 : 1;
}

/*
 * Return the canonical name of the host in the other side of the current
 * connection.  The host name is cached, so it is efficient to call this
 * several times.
 */

const char *
auth_get_canonical_hostname(struct ssh *ssh, int use_dns)
{
	static char *dnsname;

	if (!use_dns)
		return ssh_remote_ipaddr(ssh);
	if (dnsname != NULL)
		return dnsname;
	dnsname = ssh_remote_hostname(ssh);
	return dnsname;
}
