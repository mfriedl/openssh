/* $OpenBSD: sshd.c,v 1.600 2023/03/08 04:43:12 guenther Exp $ */
/*
 * SSH2 implementation:
 * Privilege Separation:
 *
 * Copyright (c) 2000, 2001, 2002 Markus Friedl.  All rights reserved.
 * Copyright (c) 2002 Niels Provos.  All rights reserved.
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
#include <sys/ioctl.h>
#include <sys/wait.h>
#include <sys/tree.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/queue.h>

#include <errno.h>
#include <fcntl.h>
#include <netdb.h>
#include <paths.h>
#include <pwd.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <unistd.h>
#include <limits.h>

#ifdef WITH_OPENSSL
#include <openssl/bn.h>
#include <openssl/evp.h>
#endif

#include "xmalloc.h"
#include "ssh.h"
#include "ssh2.h"
#include "sshpty.h"
#include "packet.h"
#include "log.h"
#include "sshbuf.h"
#include "misc.h"
#include "match.h"
#include "servconf.h"
#include "uidswap.h"
#include "compat.h"
#include "cipher.h"
#include "digest.h"
#include "sshkey.h"
#include "kex.h"
#include "authfile.h"
#include "pathnames.h"
#include "atomicio.h"
#include "canohost.h"
#include "hostfile.h"
#include "auth.h"
#include "authfd.h"
#include "msg.h"
#include "dispatch.h"
#include "channels.h"
#include "session.h"
#include "monitor.h"
#ifdef GSSAPI
#include "ssh-gss.h"
#endif
#include "monitor_wrap.h"
#include "ssh-sandbox.h"
#include "auth-options.h"
#include "version.h"
#include "ssherr.h"
#include "sk-api.h"
#include "srclimit.h"
#include "dh.h"

/* Re-exec fds */
#define REEXEC_DEVCRYPTO_RESERVED_FD	(STDERR_FILENO + 1)
#define REEXEC_STARTUP_PIPE_FD		(STDERR_FILENO + 2)
#define REEXEC_CONFIG_PASS_FD		(STDERR_FILENO + 3)
#define REEXEC_MIN_FREE_FD		(STDERR_FILENO + 4)

extern char *__progname;

/* Server configuration options. */
ServerOptions options;

/* Name of the server configuration file. */
char *config_file_name = _PATH_SERVER_CONFIG_FILE;

/*
 * Debug mode flag.  This can be set on the command line.  If debug
 * mode is enabled, extra debugging output will be sent to the system
 * log, the daemon will not go to background, and will exit after processing
 * the first connection.
 */
int debug_flag = 0;

/* Flag indicating that the daemon is being started from inetd. */
static int inetd_flag = 0;

/* debug goes to stderr unless inetd_flag is set */
static int log_stderr = 0;

/* Saved arguments to main(). */
static char **saved_argv;

/* Daemon's agent connection */
int auth_sock = -1;
static int have_agent = 0;

/*
 * Any really sensitive data in the application is contained in this
 * structure. The idea is that this structure could be locked into memory so
 * that the pages do not get written into swap.  However, there are some
 * problems. The private key contains BIGNUMs, and we do not (in principle)
 * have access to the internals of them, and locking just the structure is
 * not very useful.  Currently, memory locking is not implemented.
 */
struct {
	struct sshkey	**host_keys;		/* all private host keys */
	struct sshkey	**host_pubkeys;		/* all public host keys */
	struct sshkey	**host_certificates;	/* all public host certificates */
	int		have_ssh2_key;
} sensitive_data;

/* record remote hostname or ip */
u_int utmp_len = HOST_NAME_MAX+1;

static int startup_pipe = -1;		/* in child */

/* variables used for privilege separation */
struct monitor *pmonitor = NULL;
int privsep_is_preauth = 1;

/* global connection state and authentication contexts */
Authctxt *the_authctxt = NULL;
struct ssh *the_active_state;

/* global key/cert auth options. XXX move to permanent ssh->authctxt? */
struct sshauthopt *auth_opts = NULL;

/* sshd_config buffer */
struct sshbuf *cfg;

/* Included files from the configuration file */
struct include_list includes = TAILQ_HEAD_INITIALIZER(includes);

/* message to be displayed after login */
struct sshbuf *loginmsg;

/* Prototypes for various functions defined later in this file. */
void destroy_sensitive_data(void);
void demote_sensitive_data(void);
static void do_ssh2_kex(struct ssh *);

/*
 * Signal handler for the alarm after the login grace period has expired.
 */
static void
grace_alarm_handler(int sig)
{
	/*
	 * Try to kill any processes that we have spawned, E.g. authorized
	 * keys command helpers or privsep children.
	 */
	if (getpgid(0) == getpid()) {
		ssh_signal(SIGTERM, SIG_IGN);
		kill(0, SIGTERM);
	}

	/* Log error and exit. */
	sigdie("Timeout before authentication for %s port %d",
	    ssh_remote_ipaddr(the_active_state),
	    ssh_remote_port(the_active_state));
}

/* Destroy the host and server keys.  They will no longer be needed. */
void
destroy_sensitive_data(void)
{
	u_int i;

	for (i = 0; i < options.num_host_key_files; i++) {
		if (sensitive_data.host_keys[i]) {
			sshkey_free(sensitive_data.host_keys[i]);
			sensitive_data.host_keys[i] = NULL;
		}
		if (sensitive_data.host_certificates[i]) {
			sshkey_free(sensitive_data.host_certificates[i]);
			sensitive_data.host_certificates[i] = NULL;
		}
	}
}

/* Demote private to public keys for network child */
void
demote_sensitive_data(void)
{
	struct sshkey *tmp;
	u_int i;
	int r;

	for (i = 0; i < options.num_host_key_files; i++) {
		if (sensitive_data.host_keys[i]) {
			if ((r = sshkey_from_private(
			    sensitive_data.host_keys[i], &tmp)) != 0)
				fatal_r(r, "could not demote host %s key",
				    sshkey_type(sensitive_data.host_keys[i]));
			sshkey_free(sensitive_data.host_keys[i]);
			sensitive_data.host_keys[i] = tmp;
		}
		/* Certs do not need demotion */
	}
}

static void
privsep_preauth_child(void)
{
	gid_t gidset[1];
	struct passwd *pw;

	/* Enable challenge-response authentication for privilege separation */
	privsep_challenge_enable();

#ifdef GSSAPI
	/* Cache supported mechanism OIDs for later use */
	ssh_gssapi_prepare_supported_oids();
#endif

	/* Demote the private keys to public keys. */
	demote_sensitive_data();

	/* Demote the child */
	if (getuid() == 0 || geteuid() == 0) {
		if ((pw = getpwnam(SSH_PRIVSEP_USER)) == NULL)
			fatal("Privilege separation user %s does not exist",
			    SSH_PRIVSEP_USER);
		pw = pwcopy(pw); /* Ensure mutable */
		endpwent();
		freezero(pw->pw_passwd, strlen(pw->pw_passwd));

		/* Change our root directory */
		if (chroot(_PATH_PRIVSEP_CHROOT_DIR) == -1)
			fatal("chroot(\"%s\"): %s", _PATH_PRIVSEP_CHROOT_DIR,
			    strerror(errno));
		if (chdir("/") == -1)
			fatal("chdir(\"/\"): %s", strerror(errno));

		/*
		 * Drop our privileges
		 * NB. Can't use setusercontext() after chroot.
		 */
		debug3("privsep user:group %u:%u", (u_int)pw->pw_uid,
		    (u_int)pw->pw_gid);
		gidset[0] = pw->pw_gid;
		if (setgroups(1, gidset) == -1)
			fatal("setgroups: %.100s", strerror(errno));
		permanently_set_uid(pw);
	}
}

static int
privsep_preauth(struct ssh *ssh)
{
	int status, r;
	pid_t pid;
	struct ssh_sandbox *box = NULL;

	/* Set up unprivileged child process to deal with network data */
	pmonitor = monitor_init();
	/* Store a pointer to the kex for later rekeying */
	pmonitor->m_pkex = &ssh->kex;

	box = ssh_sandbox_init();
	pid = fork();
	if (pid == -1) {
		fatal("fork of unprivileged child failed");
	} else if (pid != 0) {
		debug2("Network child is on pid %ld", (long)pid);

		pmonitor->m_pid = pid;
		if (have_agent) {
			r = ssh_get_authentication_socket(&auth_sock);
			if (r != 0) {
				error_r(r, "Could not get agent socket");
				have_agent = 0;
			}
		}
		if (box != NULL)
			ssh_sandbox_parent_preauth(box, pid);
		monitor_child_preauth(ssh, pmonitor);

		/* Wait for the child's exit status */
		while (waitpid(pid, &status, 0) == -1) {
			if (errno == EINTR)
				continue;
			pmonitor->m_pid = -1;
			fatal_f("waitpid: %s", strerror(errno));
		}
		privsep_is_preauth = 0;
		pmonitor->m_pid = -1;
		if (WIFEXITED(status)) {
			if (WEXITSTATUS(status) != 0)
				fatal_f("preauth child exited with status %d",
				    WEXITSTATUS(status));
		} else if (WIFSIGNALED(status))
			fatal_f("preauth child terminated by signal %d",
			    WTERMSIG(status));
		if (box != NULL)
			ssh_sandbox_parent_finish(box);
		return 1;
	} else {
		/* child */
		close(pmonitor->m_sendfd);
		close(pmonitor->m_log_recvfd);

		/* Arrange for logging to be sent to the monitor */
		set_log_handler(mm_log_handler, pmonitor);

		privsep_preauth_child();
		setproctitle("%s", "[net]");
		if (box != NULL)
			ssh_sandbox_child(box);

		return 0;
	}
}

static void
privsep_postauth(struct ssh *ssh, Authctxt *authctxt)
{
	/* New socket pair */
	monitor_reinit(pmonitor);

	pmonitor->m_pid = fork();
	if (pmonitor->m_pid == -1)
		fatal("fork of unprivileged child failed");
	else if (pmonitor->m_pid != 0) {
		verbose("User child is on pid %ld", (long)pmonitor->m_pid);
		sshbuf_reset(loginmsg);
		monitor_clear_keystate(ssh, pmonitor);
		monitor_child_postauth(ssh, pmonitor);

		/* NEVERREACHED */
		exit(0);
	}

	/* child */

	close(pmonitor->m_sendfd);
	pmonitor->m_sendfd = -1;

	/* Demote the private keys to public keys. */
	demote_sensitive_data();

	/* Drop privileges */
	do_setusercontext(authctxt->pw);

	/* It is safe now to apply the key state */
	monitor_apply_keystate(ssh, pmonitor);

	/*
	 * Tell the packet layer that authentication was successful, since
	 * this information is not part of the key state.
	 */
	ssh_packet_set_authenticated(ssh);
}

static void
append_hostkey_type(struct sshbuf *b, const char *s)
{
	int r;

	if (match_pattern_list(s, options.hostkeyalgorithms, 0) != 1) {
		debug3_f("%s key not permitted by HostkeyAlgorithms", s);
		return;
	}
	if ((r = sshbuf_putf(b, "%s%s", sshbuf_len(b) > 0 ? "," : "", s)) != 0)
		fatal_fr(r, "sshbuf_putf");
}

static char *
list_hostkey_types(void)
{
	struct sshbuf *b;
	struct sshkey *key;
	char *ret;
	u_int i;

	if ((b = sshbuf_new()) == NULL)
		fatal_f("sshbuf_new failed");
	for (i = 0; i < options.num_host_key_files; i++) {
		key = sensitive_data.host_keys[i];
		if (key == NULL)
			key = sensitive_data.host_pubkeys[i];
		if (key == NULL)
			continue;
		switch (key->type) {
		case KEY_RSA:
			/* for RSA we also support SHA2 signatures */
			append_hostkey_type(b, "rsa-sha2-512");
			append_hostkey_type(b, "rsa-sha2-256");
			/* FALLTHROUGH */
		case KEY_DSA:
		case KEY_ECDSA:
		case KEY_ED25519:
		case KEY_ECDSA_SK:
		case KEY_ED25519_SK:
		case KEY_XMSS:
			append_hostkey_type(b, sshkey_ssh_name(key));
			break;
		}
		/* If the private key has a cert peer, then list that too */
		key = sensitive_data.host_certificates[i];
		if (key == NULL)
			continue;
		switch (key->type) {
		case KEY_RSA_CERT:
			/* for RSA we also support SHA2 signatures */
			append_hostkey_type(b,
			    "rsa-sha2-512-cert-v01@openssh.com");
			append_hostkey_type(b,
			    "rsa-sha2-256-cert-v01@openssh.com");
			/* FALLTHROUGH */
		case KEY_DSA_CERT:
		case KEY_ECDSA_CERT:
		case KEY_ED25519_CERT:
		case KEY_ECDSA_SK_CERT:
		case KEY_ED25519_SK_CERT:
		case KEY_XMSS_CERT:
			append_hostkey_type(b, sshkey_ssh_name(key));
			break;
		}
	}
	if ((ret = sshbuf_dup_string(b)) == NULL)
		fatal_f("sshbuf_dup_string failed");
	sshbuf_free(b);
	debug_f("%s", ret);
	return ret;
}

static struct sshkey *
get_hostkey_by_type(int type, int nid, int need_private, struct ssh *ssh)
{
	u_int i;
	struct sshkey *key;

	for (i = 0; i < options.num_host_key_files; i++) {
		switch (type) {
		case KEY_RSA_CERT:
		case KEY_DSA_CERT:
		case KEY_ECDSA_CERT:
		case KEY_ED25519_CERT:
		case KEY_ECDSA_SK_CERT:
		case KEY_ED25519_SK_CERT:
		case KEY_XMSS_CERT:
			key = sensitive_data.host_certificates[i];
			break;
		default:
			key = sensitive_data.host_keys[i];
			if (key == NULL && !need_private)
				key = sensitive_data.host_pubkeys[i];
			break;
		}
		if (key == NULL || key->type != type)
			continue;
		switch (type) {
		case KEY_ECDSA:
		case KEY_ECDSA_SK:
		case KEY_ECDSA_CERT:
		case KEY_ECDSA_SK_CERT:
			if (key->ecdsa_nid != nid)
				continue;
			/* FALLTHROUGH */
		default:
			return need_private ?
			    sensitive_data.host_keys[i] : key;
		}
	}
	return NULL;
}

struct sshkey *
get_hostkey_public_by_type(int type, int nid, struct ssh *ssh)
{
	return get_hostkey_by_type(type, nid, 0, ssh);
}

struct sshkey *
get_hostkey_private_by_type(int type, int nid, struct ssh *ssh)
{
	return get_hostkey_by_type(type, nid, 1, ssh);
}

struct sshkey *
get_hostkey_by_index(int ind)
{
	if (ind < 0 || (u_int)ind >= options.num_host_key_files)
		return (NULL);
	return (sensitive_data.host_keys[ind]);
}

struct sshkey *
get_hostkey_public_by_index(int ind, struct ssh *ssh)
{
	if (ind < 0 || (u_int)ind >= options.num_host_key_files)
		return (NULL);
	return (sensitive_data.host_pubkeys[ind]);
}

int
get_hostkey_index(struct sshkey *key, int compare, struct ssh *ssh)
{
	u_int i;

	for (i = 0; i < options.num_host_key_files; i++) {
		if (sshkey_is_cert(key)) {
			if (key == sensitive_data.host_certificates[i] ||
			    (compare && sensitive_data.host_certificates[i] &&
			    sshkey_equal(key,
			    sensitive_data.host_certificates[i])))
				return (i);
		} else {
			if (key == sensitive_data.host_keys[i] ||
			    (compare && sensitive_data.host_keys[i] &&
			    sshkey_equal(key, sensitive_data.host_keys[i])))
				return (i);
			if (key == sensitive_data.host_pubkeys[i] ||
			    (compare && sensitive_data.host_pubkeys[i] &&
			    sshkey_equal(key, sensitive_data.host_pubkeys[i])))
				return (i);
		}
	}
	return (-1);
}

/* Inform the client of all hostkeys */
static void
notify_hostkeys(struct ssh *ssh)
{
	struct sshbuf *buf;
	struct sshkey *key;
	u_int i, nkeys;
	int r;
	char *fp;

	/* Some clients cannot cope with the hostkeys message, skip those. */
	if (ssh->compat & SSH_BUG_HOSTKEYS)
		return;

	if ((buf = sshbuf_new()) == NULL)
		fatal_f("sshbuf_new");
	for (i = nkeys = 0; i < options.num_host_key_files; i++) {
		key = get_hostkey_public_by_index(i, ssh);
		if (key == NULL || key->type == KEY_UNSPEC ||
		    sshkey_is_cert(key))
			continue;
		fp = sshkey_fingerprint(key, options.fingerprint_hash,
		    SSH_FP_DEFAULT);
		debug3_f("key %d: %s %s", i, sshkey_ssh_name(key), fp);
		free(fp);
		if (nkeys == 0) {
			/*
			 * Start building the request when we find the
			 * first usable key.
			 */
			if ((r = sshpkt_start(ssh, SSH2_MSG_GLOBAL_REQUEST)) != 0 ||
			    (r = sshpkt_put_cstring(ssh, "hostkeys-00@openssh.com")) != 0 ||
			    (r = sshpkt_put_u8(ssh, 0)) != 0) /* want reply */
				sshpkt_fatal(ssh, r, "%s: start request", __func__);
		}
		/* Append the key to the request */
		sshbuf_reset(buf);
		if ((r = sshkey_putb(key, buf)) != 0)
			fatal_fr(r, "couldn't put hostkey %d", i);
		if ((r = sshpkt_put_stringb(ssh, buf)) != 0)
			sshpkt_fatal(ssh, r, "%s: append key", __func__);
		nkeys++;
	}
	debug3_f("sent %u hostkeys", nkeys);
	if (nkeys == 0)
		fatal_f("no hostkeys");
	if ((r = sshpkt_send(ssh)) != 0)
		sshpkt_fatal(ssh, r, "%s: send", __func__);
	sshbuf_free(buf);
}

static void
usage(void)
{
	fprintf(stderr, "%s, %s\n", SSH_VERSION, SSH_OPENSSL_VERSION);
	fprintf(stderr,
"usage: sshd [-46DdeGiqTtV] [-C connection_spec] [-c host_cert_file]\n"
"            [-E log_file] [-f config_file] [-g login_grace_time]\n"
"            [-h host_key_file] [-o option] [-p port] [-u len]\n"
	);
	exit(1);
}

static void
recv_rexec_state(int fd, struct sshbuf *conf)
{
	struct sshbuf *m, *inc;
	u_char *cp, ver;
	size_t len;
	int r;
	struct include_item *item;

	debug3_f("entering fd = %d", fd);

	if ((m = sshbuf_new()) == NULL || (inc = sshbuf_new()) == NULL)
		fatal_f("sshbuf_new failed");
	if (ssh_msg_recv(fd, m) == -1)
		fatal_f("ssh_msg_recv failed");
	if ((r = sshbuf_get_u8(m, &ver)) != 0)
		fatal_fr(r, "parse version");
	if (ver != 0)
		fatal_f("rexec version mismatch");
	if ((r = sshbuf_get_string(m, &cp, &len)) != 0 ||
	    (r = sshbuf_get_stringb(m, inc)) != 0)
		fatal_fr(r, "parse config");

	if (conf != NULL && (r = sshbuf_put(conf, cp, len)))
		fatal_fr(r, "sshbuf_put");

	while (sshbuf_len(inc) != 0) {
		item = xcalloc(1, sizeof(*item));
		if ((item->contents = sshbuf_new()) == NULL)
			fatal_f("sshbuf_new failed");
		if ((r = sshbuf_get_cstring(inc, &item->selector, NULL)) != 0 ||
		    (r = sshbuf_get_cstring(inc, &item->filename, NULL)) != 0 ||
		    (r = sshbuf_get_stringb(inc, item->contents)) != 0)
			fatal_fr(r, "parse includes");
		TAILQ_INSERT_TAIL(&includes, item, entry);
	}

	free(cp);
	sshbuf_free(m);

	debug3_f("done");
}

/*
 * If IP options are supported, make sure there are none (log and
 * return an error if any are found).  Basically we are worried about
 * source routing; it can be used to pretend you are somebody
 * (ip-address) you are not. That itself may be "almost acceptable"
 * under certain circumstances, but rhosts authentication is useless
 * if source routing is accepted. Notice also that if we just dropped
 * source routing here, the other side could use IP spoofing to do
 * rest of the interaction and could still bypass security.  So we
 * exit here if we detect any IP options.
 */
static void
check_ip_options(struct ssh *ssh)
{
	int sock_in = ssh_packet_get_connection_in(ssh);
	struct sockaddr_storage from;
	u_char opts[200];
	socklen_t i, option_size = sizeof(opts), fromlen = sizeof(from);
	char text[sizeof(opts) * 3 + 1];

	memset(&from, 0, sizeof(from));
	if (getpeername(sock_in, (struct sockaddr *)&from,
	    &fromlen) == -1)
		return;
	if (from.ss_family != AF_INET)
		return;
	/* XXX IPv6 options? */

	if (getsockopt(sock_in, IPPROTO_IP, IP_OPTIONS, opts,
	    &option_size) >= 0 && option_size != 0) {
		text[0] = '\0';
		for (i = 0; i < option_size; i++)
			snprintf(text + i*3, sizeof(text) - i*3,
			    " %2.2x", opts[i]);
		fatal("Connection from %.100s port %d with IP opts: %.800s",
		    ssh_remote_ipaddr(ssh), ssh_remote_port(ssh), text);
	}
	return;
}

/* Set the routing domain for this process */
static void
set_process_rdomain(struct ssh *ssh, const char *name)
{
	int rtable, ortable = getrtable();
	const char *errstr;

	if (name == NULL)
		return; /* default */

	if (strcmp(name, "%D") == 0) {
		/* "expands" to routing domain of connection */
		if ((name = ssh_packet_rdomain_in(ssh)) == NULL)
			return;
	}

	rtable = (int)strtonum(name, 0, 255, &errstr);
	if (errstr != NULL) /* Shouldn't happen */
		fatal("Invalid routing domain \"%s\": %s", name, errstr);
	if (rtable != ortable && setrtable(rtable) != 0)
		fatal("Unable to set routing domain %d: %s",
		    rtable, strerror(errno));
	debug_f("set routing domain %d (was %d)", rtable, ortable);
}

static void
accumulate_host_timing_secret(struct sshbuf *server_cfg,
    struct sshkey *key)
{
	static struct ssh_digest_ctx *ctx;
	u_char *hash;
	size_t len;
	struct sshbuf *buf;
	int r;

	if (ctx == NULL && (ctx = ssh_digest_start(SSH_DIGEST_SHA512)) == NULL)
		fatal_f("ssh_digest_start");
	if (key == NULL) { /* finalize */
		/* add server config in case we are using agent for host keys */
		if (ssh_digest_update(ctx, sshbuf_ptr(server_cfg),
		    sshbuf_len(server_cfg)) != 0)
			fatal_f("ssh_digest_update");
		len = ssh_digest_bytes(SSH_DIGEST_SHA512);
		hash = xmalloc(len);
		if (ssh_digest_final(ctx, hash, len) != 0)
			fatal_f("ssh_digest_final");
		options.timing_secret = PEEK_U64(hash);
		freezero(hash, len);
		ssh_digest_free(ctx);
		ctx = NULL;
		return;
	}
	if ((buf = sshbuf_new()) == NULL)
		fatal_f("could not allocate buffer");
	if ((r = sshkey_private_serialize(key, buf)) != 0)
		fatal_fr(r, "encode %s key", sshkey_ssh_name(key));
	if (ssh_digest_update(ctx, sshbuf_ptr(buf), sshbuf_len(buf)) != 0)
		fatal_f("ssh_digest_update");
	sshbuf_reset(buf);
	sshbuf_free(buf);
}

/*
 * Main program for the daemon.
 */
int
main(int ac, char **av)
{
	struct ssh *ssh = NULL;
	extern char *optarg;
	extern int optind;
	int r, opt, on = 1, remote_port;
	int sock_in = -1, sock_out = -1, rexeced_flag = 0;
	const char *remote_ip, *rdomain;
	char *fp, *line, *laddr, *logfile = NULL;
	u_int i, j;
	u_int64_t ibytes, obytes;
	mode_t new_umask;
	struct sshkey *key;
	struct sshkey *pubkey;
	int keytype;
	Authctxt *authctxt;
	struct connection_info *connection_info = NULL;
	sigset_t sigmask;

	sigemptyset(&sigmask);
	sigprocmask(SIG_SETMASK, &sigmask, NULL);

	/* Save argv. */
	saved_argv = av;

	/* Ensure that fds 0, 1 and 2 are open or directed to /dev/null */
	sanitise_stdfd();

	/* Initialize configuration options to their default values. */
	initialize_server_options(&options);

	/* Parse command-line arguments. */
	while ((opt = getopt(ac, av,
	    "C:E:b:c:f:g:h:k:o:p:u:46DGQRTdeiqrtV")) != -1) {
		switch (opt) {
		case '4':
			options.address_family = AF_INET;
			break;
		case '6':
			options.address_family = AF_INET6;
			break;
		case 'f':
			config_file_name = optarg;
			break;
		case 'c':
			servconf_add_hostcert("[command-line]", 0,
			    &options, optarg);
			break;
		case 'd':
			if (debug_flag == 0) {
				debug_flag = 1;
				options.log_level = SYSLOG_LEVEL_DEBUG1;
			} else if (options.log_level < SYSLOG_LEVEL_DEBUG3)
				options.log_level++;
			break;
		case 'D':
			/* ignore */
			break;
		case 'E':
			logfile = optarg;
			/* FALLTHROUGH */
		case 'e':
			log_stderr = 1;
			break;
		case 'i':
			inetd_flag = 1;
			break;
		case 'r':
			/* ignore */
			break;
		case 'R':
			rexeced_flag = 1;
			break;
		case 'Q':
			/* ignored */
			break;
		case 'q':
			options.log_level = SYSLOG_LEVEL_QUIET;
			break;
		case 'b':
			/* protocol 1, ignored */
			break;
		case 'p':
			options.ports_from_cmdline = 1;
			if (options.num_ports >= MAX_PORTS) {
				fprintf(stderr, "too many ports.\n");
				exit(1);
			}
			options.ports[options.num_ports++] = a2port(optarg);
			if (options.ports[options.num_ports-1] <= 0) {
				fprintf(stderr, "Bad port number.\n");
				exit(1);
			}
			break;
		case 'g':
			if ((options.login_grace_time = convtime(optarg)) == -1) {
				fprintf(stderr, "Invalid login grace time.\n");
				exit(1);
			}
			break;
		case 'k':
			/* protocol 1, ignored */
			break;
		case 'h':
			servconf_add_hostkey("[command-line]", 0,
			    &options, optarg, 1);
			break;
		case 't':
		case 'T':
		case 'G':
			fatal("test/dump modes not supported");
			break;
		case 'C':
			connection_info = get_connection_info(ssh, 0, 0);
			if (parse_server_match_testspec(connection_info,
			    optarg) == -1)
				exit(1);
			break;
		case 'u':
			utmp_len = (u_int)strtonum(optarg, 0, HOST_NAME_MAX+1+1, NULL);
			if (utmp_len > HOST_NAME_MAX+1) {
				fprintf(stderr, "Invalid utmp length.\n");
				exit(1);
			}
			break;
		case 'o':
			line = xstrdup(optarg);
			if (process_server_config_line(&options, line,
			    "command-line", 0, NULL, NULL, &includes) != 0)
				exit(1);
			free(line);
			break;
		case 'V':
			fprintf(stderr, "%s, %s\n",
			    SSH_VERSION, SSH_OPENSSL_VERSION);
			exit(0);
		default:
			usage();
			break;
		}
	}

	/* Check that there are no remaining arguments. */
	if (optind < ac) {
		fprintf(stderr, "Extra argument %s.\n", av[optind]);
		exit(1);
	}

	debug("sshd version %s, %s", SSH_VERSION, SSH_OPENSSL_VERSION);

	if (!rexeced_flag)
		fatal("sshd-monitor should not be executed directly");

	closefrom(REEXEC_MIN_FREE_FD);

#ifdef WITH_OPENSSL
	OpenSSL_add_all_algorithms();
#endif

	/* If requested, redirect the logs to the specified logfile. */
	if (logfile != NULL)
		log_redirect_stderr_to(logfile);
	/*
	 * Force logging to stderr until we have loaded the private host
	 * key (unless started from inetd)
	 */
	log_init(__progname,
	    options.log_level == SYSLOG_LEVEL_NOT_SET ?
	    SYSLOG_LEVEL_INFO : options.log_level,
	    options.log_facility == SYSLOG_FACILITY_NOT_SET ?
	    SYSLOG_FACILITY_AUTH : options.log_facility,
	    log_stderr || !inetd_flag || debug_flag);

	sensitive_data.have_ssh2_key = 0;

	/* Fetch our configuration */
	if ((cfg = sshbuf_new()) == NULL)
		fatal("sshbuf_new config buf failed");
	setproctitle("%s", "[rexeced]");
	recv_rexec_state(REEXEC_CONFIG_PASS_FD, cfg);
	parse_server_config(&options, "rexec", cfg, &includes, NULL, 1);
	/* Fill in default values for those options not explicitly set. */
	fill_default_server_options(&options);

	if (!debug_flag) {
		startup_pipe = dup(REEXEC_STARTUP_PIPE_FD);
		close(REEXEC_STARTUP_PIPE_FD);
		/*
		 * Signal parent that this child is at a point where
		 * they can go away if they have a SIGHUP pending.
		 */
		(void)atomicio(vwrite, startup_pipe, "\0", 1);
	}

	/* Check that options are sensible */
	if (options.authorized_keys_command_user == NULL &&
	    (options.authorized_keys_command != NULL &&
	    strcasecmp(options.authorized_keys_command, "none") != 0))
		fatal("AuthorizedKeysCommand set without "
		    "AuthorizedKeysCommandUser");
	if (options.authorized_principals_command_user == NULL &&
	    (options.authorized_principals_command != NULL &&
	    strcasecmp(options.authorized_principals_command, "none") != 0))
		fatal("AuthorizedPrincipalsCommand set without "
		    "AuthorizedPrincipalsCommandUser");

	/*
	 * Check whether there is any path through configured auth methods.
	 * Unfortunately it is not possible to verify this generally before
	 * daemonisation in the presence of Match block, but this catches
	 * and warns for trivial misconfigurations that could break login.
	 */
	if (options.num_auth_methods != 0) {
		for (i = 0; i < options.num_auth_methods; i++) {
			if (auth2_methods_valid(options.auth_methods[i],
			    1) == 0)
				break;
		}
		if (i >= options.num_auth_methods)
			fatal("AuthenticationMethods cannot be satisfied by "
			    "enabled authentication methods");
	}

#ifdef WITH_OPENSSL
	if (options.moduli_file != NULL)
		dh_set_moduli_file(options.moduli_file);
#endif

	/* load host keys */
	sensitive_data.host_keys = xcalloc(options.num_host_key_files,
	    sizeof(struct sshkey *));
	sensitive_data.host_pubkeys = xcalloc(options.num_host_key_files,
	    sizeof(struct sshkey *));

	if (options.host_key_agent) {
		if (strcmp(options.host_key_agent, SSH_AUTHSOCKET_ENV_NAME))
			setenv(SSH_AUTHSOCKET_ENV_NAME,
			    options.host_key_agent, 1);
		if ((r = ssh_get_authentication_socket(NULL)) == 0)
			have_agent = 1;
		else
			error_r(r, "Could not connect to agent \"%s\"",
			    options.host_key_agent);
	}

	for (i = 0; i < options.num_host_key_files; i++) {
		int ll = options.host_key_file_userprovided[i] ?
		    SYSLOG_LEVEL_ERROR : SYSLOG_LEVEL_DEBUG1;

		if (options.host_key_files[i] == NULL)
			continue;
		if ((r = sshkey_load_private(options.host_key_files[i], "",
		    &key, NULL)) != 0 && r != SSH_ERR_SYSTEM_ERROR)
			do_log2_r(r, ll, "Unable to load host key \"%s\"",
			    options.host_key_files[i]);
		if (sshkey_is_sk(key) &&
		    key->sk_flags & SSH_SK_USER_PRESENCE_REQD) {
			debug("host key %s requires user presence, ignoring",
			    options.host_key_files[i]);
			key->sk_flags &= ~SSH_SK_USER_PRESENCE_REQD;
		}
		if (r == 0 && key != NULL &&
		    (r = sshkey_shield_private(key)) != 0) {
			do_log2_r(r, ll, "Unable to shield host key \"%s\"",
			    options.host_key_files[i]);
			sshkey_free(key);
			key = NULL;
		}
		if ((r = sshkey_load_public(options.host_key_files[i],
		    &pubkey, NULL)) != 0 && r != SSH_ERR_SYSTEM_ERROR)
			do_log2_r(r, ll, "Unable to load host key \"%s\"",
			    options.host_key_files[i]);
		if (pubkey != NULL && key != NULL) {
			if (!sshkey_equal(pubkey, key)) {
				error("Public key for %s does not match "
				    "private key", options.host_key_files[i]);
				sshkey_free(pubkey);
				pubkey = NULL;
			}
		}
		if (pubkey == NULL && key != NULL) {
			if ((r = sshkey_from_private(key, &pubkey)) != 0)
				fatal_r(r, "Could not demote key: \"%s\"",
				    options.host_key_files[i]);
		}
		if (pubkey != NULL && (r = sshkey_check_rsa_length(pubkey,
		    options.required_rsa_size)) != 0) {
			error_fr(r, "Host key %s", options.host_key_files[i]);
			sshkey_free(pubkey);
			sshkey_free(key);
			continue;
		}
		sensitive_data.host_keys[i] = key;
		sensitive_data.host_pubkeys[i] = pubkey;

		if (key == NULL && pubkey != NULL && have_agent) {
			debug("will rely on agent for hostkey %s",
			    options.host_key_files[i]);
			keytype = pubkey->type;
		} else if (key != NULL) {
			keytype = key->type;
			accumulate_host_timing_secret(cfg, key);
		} else {
			do_log2(ll, "Unable to load host key: %s",
			    options.host_key_files[i]);
			sensitive_data.host_keys[i] = NULL;
			sensitive_data.host_pubkeys[i] = NULL;
			continue;
		}

		switch (keytype) {
		case KEY_RSA:
		case KEY_DSA:
		case KEY_ECDSA:
		case KEY_ED25519:
		case KEY_ECDSA_SK:
		case KEY_ED25519_SK:
		case KEY_XMSS:
			if (have_agent || key != NULL)
				sensitive_data.have_ssh2_key = 1;
			break;
		}
		if ((fp = sshkey_fingerprint(pubkey, options.fingerprint_hash,
		    SSH_FP_DEFAULT)) == NULL)
			fatal("sshkey_fingerprint failed");
		debug("%s host key #%d: %s %s",
		    key ? "private" : "agent", i, sshkey_ssh_name(pubkey), fp);
		free(fp);
	}
	accumulate_host_timing_secret(cfg, NULL);
	if (!sensitive_data.have_ssh2_key) {
		logit("sshd: no hostkeys available -- exiting.");
		exit(1);
	}

	/*
	 * Load certificates. They are stored in an array at identical
	 * indices to the public keys that they relate to.
	 */
	sensitive_data.host_certificates = xcalloc(options.num_host_key_files,
	    sizeof(struct sshkey *));
	for (i = 0; i < options.num_host_key_files; i++)
		sensitive_data.host_certificates[i] = NULL;

	for (i = 0; i < options.num_host_cert_files; i++) {
		if (options.host_cert_files[i] == NULL)
			continue;
		if ((r = sshkey_load_public(options.host_cert_files[i],
		    &key, NULL)) != 0) {
			error_r(r, "Could not load host certificate \"%s\"",
			    options.host_cert_files[i]);
			continue;
		}
		if (!sshkey_is_cert(key)) {
			error("Certificate file is not a certificate: %s",
			    options.host_cert_files[i]);
			sshkey_free(key);
			continue;
		}
		/* Find matching private key */
		for (j = 0; j < options.num_host_key_files; j++) {
			if (sshkey_equal_public(key,
			    sensitive_data.host_pubkeys[j])) {
				sensitive_data.host_certificates[j] = key;
				break;
			}
		}
		if (j >= options.num_host_key_files) {
			error("No matching private key for certificate: %s",
			    options.host_cert_files[i]);
			sshkey_free(key);
			continue;
		}
		sensitive_data.host_certificates[j] = key;
		debug("host certificate: #%u type %d %s", j, key->type,
		    sshkey_type(key));
	}

	/* Ensure that umask disallows at least group and world write */
	new_umask = umask(0077) | 0022;
	(void) umask(new_umask);

	/* Initialize the log (it is reinitialized below in case we forked). */
	if (debug_flag)
		log_stderr = 1;
	log_init(__progname, options.log_level,
	    options.log_facility, log_stderr);
	for (i = 0; i < options.num_log_verbose; i++)
		log_verbose_add(options.log_verbose[i]);

	/* Reinitialize the log (because of the fork above). */
	log_init(__progname, options.log_level, options.log_facility, log_stderr);

	/*
	 * Chdir to the root directory so that the current disk can be
	 * unmounted if desired.
	 */
	if (chdir("/") == -1)
		error("chdir(\"/\"): %s", strerror(errno));

	/* ignore SIGPIPE */
	ssh_signal(SIGPIPE, SIG_IGN);

	/* Get a connection, either from inetd or rexec */
	close(REEXEC_CONFIG_PASS_FD);
	if (inetd_flag) {
		/*
		 * NB. must be different fd numbers for the !socket case,
		 * as packet_connection_is_on_socket() depends on this.
		 */
		sock_in = dup(STDIN_FILENO);
		sock_out = dup(STDOUT_FILENO);
	} else {
		/* rexec case; accept()ed socket in ancestor listener */
		sock_in = sock_out = dup(STDIN_FILENO);
	}

	/*
	 * We intentionally do not close the descriptors 0, 1, and 2
	 * as our code for setting the descriptors won't work if
	 * ttyfd happens to be one of those.
	 */
	if (stdfd_devnull(1, 1, !log_stderr) == -1)
		error("stdfd_devnull failed");
	debug("network sockets: %d, %d", sock_in, sock_out);

	/* This is the child processing a new connection. */
	setproctitle("%s", "[accepted]");

	/*
	 * Create a new session and process group since the 4.4BSD
	 * setlogin() affects the entire process group.  We don't
	 * want the child to be able to affect the parent.
	 */
	if (!debug_flag && !inetd_flag && setsid() == -1)
		error("setsid: %.100s", strerror(errno));

	/* Executed child processes don't need these. */
	fcntl(sock_out, F_SETFD, FD_CLOEXEC);
	fcntl(sock_in, F_SETFD, FD_CLOEXEC);

	/* We will not restart on SIGHUP since it no longer makes sense. */
	ssh_signal(SIGALRM, SIG_DFL);
	ssh_signal(SIGHUP, SIG_DFL);
	ssh_signal(SIGTERM, SIG_DFL);
	ssh_signal(SIGQUIT, SIG_DFL);
	ssh_signal(SIGCHLD, SIG_DFL);

	/*
	 * Register our connection.  This turns encryption off because we do
	 * not have a key.
	 */
	if ((ssh = ssh_packet_set_connection(NULL, sock_in, sock_out)) == NULL)
		fatal("Unable to create connection");
	the_active_state = ssh;
	ssh_packet_set_server(ssh);

	check_ip_options(ssh);

	/* Prepare the channels layer */
	channel_init_channels(ssh);
	channel_set_af(ssh, options.address_family);
	process_channel_timeouts(ssh, &options);
	process_permitopen(ssh, &options);

	/* Set SO_KEEPALIVE if requested. */
	if (options.tcp_keep_alive && ssh_packet_connection_is_on_socket(ssh) &&
	    setsockopt(sock_in, SOL_SOCKET, SO_KEEPALIVE, &on, sizeof(on)) == -1)
		error("setsockopt SO_KEEPALIVE: %.100s", strerror(errno));

	if ((remote_port = ssh_remote_port(ssh)) < 0) {
		debug("ssh_remote_port failed");
		cleanup_exit(255);
	}

	/*
	 * The rest of the code depends on the fact that
	 * ssh_remote_ipaddr() caches the remote ip, even if
	 * the socket goes away.
	 */
	remote_ip = ssh_remote_ipaddr(ssh);

	rdomain = ssh_packet_rdomain_in(ssh);

	/* Log the connection. */
	laddr = get_local_ipaddr(sock_in);
	verbose("Connection from %s port %d on %s port %d%s%s%s",
	    remote_ip, remote_port, laddr,  ssh_local_port(ssh),
	    rdomain == NULL ? "" : " rdomain \"",
	    rdomain == NULL ? "" : rdomain,
	    rdomain == NULL ? "" : "\"");
	free(laddr);

	/*
	 * We don't want to listen forever unless the other side
	 * successfully authenticates itself.  So we set up an alarm which is
	 * cleared after successful authentication.  A limit of zero
	 * indicates no limit. Note that we don't set the alarm in debugging
	 * mode; it is just annoying to have the server exit just when you
	 * are about to discover the bug.
	 */
	ssh_signal(SIGALRM, grace_alarm_handler);
	if (!debug_flag)
		alarm(options.login_grace_time);

	if ((r = kex_exchange_identification(ssh, -1,
	    options.version_addendum)) != 0)
		sshpkt_fatal(ssh, r, "banner exchange");

	ssh_packet_set_nonblocking(ssh);

	/* allocate authentication context */
	authctxt = xcalloc(1, sizeof(*authctxt));
	ssh->authctxt = authctxt;

	/* XXX global for cleanup, access from other modules */
	the_authctxt = authctxt;

	/* Set default key authentication options */
	if ((auth_opts = sshauthopt_new_with_keys_defaults()) == NULL)
		fatal("allocation failed");

	/* prepare buffer to collect messages to display to user after login */
	if ((loginmsg = sshbuf_new()) == NULL)
		fatal("sshbuf_new loginmsg failed");
	auth_debug_reset();

	if (privsep_preauth(ssh) == 1)
		goto authenticated;

	/* perform the key exchange */
	/* authenticate user and start session */
	do_ssh2_kex(ssh);
	do_authentication2(ssh);

	/*
	 * The unprivileged child now transfers the current keystate and exits.
	 */
	mm_send_keystate(ssh, pmonitor);
	ssh_packet_clear_keys(ssh);
	exit(0);

 authenticated:
	/*
	 * Cancel the alarm we set to limit the time taken for
	 * authentication.
	 */
	alarm(0);
	ssh_signal(SIGALRM, SIG_DFL);
	authctxt->authenticated = 1;
	if (startup_pipe != -1) {
		close(startup_pipe);
		startup_pipe = -1;
	}

	if (options.routing_domain != NULL)
		set_process_rdomain(ssh, options.routing_domain);

	/*
	 * In privilege separation, we fork another child and prepare
	 * file descriptor passing.
	 */
	privsep_postauth(ssh, authctxt);
	/* the monitor process [priv] will not return */

	ssh_packet_set_timeout(ssh, options.client_alive_interval,
	    options.client_alive_count_max);

	/* Try to send all our hostkeys to the client */
	notify_hostkeys(ssh);

	/* Start session. */
	do_authenticated(ssh, authctxt);

	/* The connection has been terminated. */
	ssh_packet_get_bytes(ssh, &ibytes, &obytes);
	verbose("Transferred: sent %llu, received %llu bytes",
	    (unsigned long long)obytes, (unsigned long long)ibytes);

	verbose("Closing connection to %.500s port %d", remote_ip, remote_port);
	ssh_packet_close(ssh);

	mm_terminate();

	exit(0);
}

int
sshd_hostkey_sign(struct ssh *ssh, struct sshkey *privkey,
    struct sshkey *pubkey, u_char **signature, size_t *slenp,
    const u_char *data, size_t dlen, const char *alg)
{
	if (privkey) {
		if (mm_sshkey_sign(ssh, privkey, signature, slenp,
		    data, dlen, alg, options.sk_provider, NULL,
		    ssh->compat) < 0)
			fatal_f("privkey sign failed");
	} else {
		if (mm_sshkey_sign(ssh, pubkey, signature, slenp,
		    data, dlen, alg, options.sk_provider, NULL,
		    ssh->compat) < 0)
			fatal_f("pubkey sign failed");
	}
	return 0;
}

/* SSH2 key exchange */
static void
do_ssh2_kex(struct ssh *ssh)
{
	char *hkalgs = NULL, *myproposal[PROPOSAL_MAX];
	const char *compression = NULL;
	struct kex *kex;
	int r;

	if (options.rekey_limit || options.rekey_interval)
		ssh_packet_set_rekey_limits(ssh, options.rekey_limit,
		    options.rekey_interval);

	if (options.compression == COMP_NONE)
		compression = "none";
	hkalgs = list_hostkey_types();

	kex_proposal_populate_entries(ssh, myproposal, options.kex_algorithms,
	    options.ciphers, options.macs, compression, hkalgs);

	free(hkalgs);

	/* start key exchange */
	if ((r = kex_setup(ssh, myproposal)) != 0)
		fatal_r(r, "kex_setup");
	kex = ssh->kex;
#ifdef WITH_OPENSSL
	kex->kex[KEX_DH_GRP1_SHA1] = kex_gen_server;
	kex->kex[KEX_DH_GRP14_SHA1] = kex_gen_server;
	kex->kex[KEX_DH_GRP14_SHA256] = kex_gen_server;
	kex->kex[KEX_DH_GRP16_SHA512] = kex_gen_server;
	kex->kex[KEX_DH_GRP18_SHA512] = kex_gen_server;
	kex->kex[KEX_DH_GEX_SHA1] = kexgex_server;
	kex->kex[KEX_DH_GEX_SHA256] = kexgex_server;
	kex->kex[KEX_ECDH_SHA2] = kex_gen_server;
#endif
	kex->kex[KEX_C25519_SHA256] = kex_gen_server;
	kex->kex[KEX_KEM_SNTRUP761X25519_SHA512] = kex_gen_server;
	kex->load_host_public_key=&get_hostkey_public_by_type;
	kex->load_host_private_key=&get_hostkey_private_by_type;
	kex->host_key_index=&get_hostkey_index;
	kex->sign = sshd_hostkey_sign;

	ssh_dispatch_run_fatal(ssh, DISPATCH_BLOCK, &kex->done);

#ifdef DEBUG_KEXDH
	/* send 1st encrypted/maced/compressed message */
	if ((r = sshpkt_start(ssh, SSH2_MSG_IGNORE)) != 0 ||
	    (r = sshpkt_put_cstring(ssh, "markus")) != 0 ||
	    (r = sshpkt_send(ssh)) != 0 ||
	    (r = ssh_packet_write_wait(ssh)) != 0)
		fatal_fr(r, "send test");
#endif
	kex_proposal_free_entries(myproposal);
	debug("KEX done");
}

/* server specific fatal cleanup */
void
cleanup_exit(int i)
{
	if (the_active_state != NULL && the_authctxt != NULL) {
		do_cleanup(the_active_state, the_authctxt);
		if (privsep_is_preauth &&
		    pmonitor != NULL && pmonitor->m_pid > 1) {
			debug("Killing privsep child %d", pmonitor->m_pid);
			if (kill(pmonitor->m_pid, SIGKILL) != 0 &&
			    errno != ESRCH) {
				error_f("kill(%d): %s", pmonitor->m_pid,
				    strerror(errno));
			}
		}
	}
	_exit(i);
}