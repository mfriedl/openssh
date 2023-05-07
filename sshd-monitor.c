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
#include "auth-options.h"
#include "version.h"
#include "ssherr.h"
#include "sk-api.h"
#include "dh.h"

/* Re-exec fds */
#define REEXEC_DEVCRYPTO_RESERVED_FD	(STDERR_FILENO + 1)
#define REEXEC_STARTUP_PIPE_FD		(STDERR_FILENO + 2)
#define REEXEC_CONFIG_PASS_FD		(STDERR_FILENO + 3)
#define REEXEC_MIN_FREE_FD		(STDERR_FILENO + 4)

/* Privsep fds */
#define PRIVSEP_MONITOR_FD		(STDERR_FILENO + 1)
#define PRIVSEP_LOG_FD			(STDERR_FILENO + 2)
#define PRIVSEP_CONFIG_PASS_FD		(STDERR_FILENO + 3)
#define PRIVSEP_MIN_FREE_FD		(STDERR_FILENO + 4)

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
	u_int		num_hostkeys;
	struct sshkey	**host_keys;		/* all private host keys */
	struct sshkey	**host_pubkeys;		/* all public host keys */
	struct sshkey	**host_certificates;	/* all public host certificates */
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

/* XXX stub */
int
mm_is_monitor(void)
{
	return 1;
}

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

static struct sshbuf *
pack_hostkeys(void)
{
	struct sshbuf *keybuf = NULL, *hostkeys = NULL;
	int r;
	u_int i;

	if ((hostkeys = sshbuf_new()) == NULL)
		fatal_f("sshbuf_new failed");

	/* pack hostkeys into a string. Empty key slots get empty strings */
	for (i = 0; i < options.num_host_key_files; i++) {
		/* public key */
		if (sensitive_data.host_pubkeys[i] != NULL) {
			if ((r = sshkey_puts(sensitive_data.host_pubkeys[i],
			    hostkeys)) != 0)
				fatal_fr(r, "compose hostkey public");
		} else {
			if ((r = sshbuf_put_string(hostkeys, NULL, 0)) != 0)
				fatal_fr(r, "compose hostkey empty public");
		}
		/* cert */
		if (sensitive_data.host_certificates[i] != NULL) {
			if ((r = sshkey_puts(
			    sensitive_data.host_certificates[i],
			    hostkeys)) != 0)
				fatal_fr(r, "compose host cert");
		} else {
			if ((r = sshbuf_put_string(hostkeys, NULL, 0)) != 0)
				fatal_fr(r, "compose host cert empty");
		}
	}

	sshbuf_free(keybuf);
	return hostkeys;
}

/* XXX simplify this by passing using a monitor call */
static void
send_privsep_state(struct ssh *ssh, int fd, struct sshbuf *conf)
{
	struct sshbuf *m = NULL, *inc = NULL, *hostkeys = NULL;
	struct sshbuf *opts = NULL, *confdata = NULL;
	struct include_item *item = NULL;
	Authctxt *authctxt = ssh->authctxt;
	char *pw_name = NULL;
	size_t pw_len = 0;
	int r;

	debug3_f("entering fd = %d config len %zu", fd,
	    sshbuf_len(conf));

	if ((m = sshbuf_new()) == NULL ||
	    (inc = sshbuf_new()) == NULL ||
	    (opts = sshbuf_new()) == NULL ||
	    (confdata = sshbuf_new()) == NULL)
		fatal_f("sshbuf_new failed");

	/* XXX unneccessary? */
	/* pack includes into a string */
	TAILQ_FOREACH(item, &includes, entry) {
		if ((r = sshbuf_put_cstring(inc, item->selector)) != 0 ||
		    (r = sshbuf_put_cstring(inc, item->filename)) != 0 ||
		    (r = sshbuf_put_stringb(inc, item->contents)) != 0)
			fatal_fr(r, "compose includes");
	}

	hostkeys = pack_hostkeys();
	if (authctxt != NULL && auth_opts != NULL &&
	    (r = sshauthopt_serialise(auth_opts, opts, 0)) != 0)
		fatal_fr(r, "sshauthopt_serialise failed");

	if (authctxt != NULL)
		mm_encode_server_options(confdata);

	/* authenticated user (postauth) */
	if (authctxt && authctxt->pw && authctxt->authenticated) {
		if ((pw_name = authctxt->pw->pw_name) != NULL)
			pw_len = strlen(pw_name);
	}

	debug3_f("send user len %zu", pw_len);

	/*
	 * Protocol from monitor to unpriv privsep process:
	 *	string	configuration
	 *	string	configuration_data (postauth)
	 *	uint64	timing_secret	XXX move delays to monitor and remove
	 *	string	host_keys[] {
	 *		string public_key
	 *		string certificate
	 *	}
	 *	string  server_banner
	 *	string  client_banner
	 *	string  keystate (postauth)
	 *	string  authenticated_user (postauth)
	 *	string  session_info (postauth)
	 *	string  authopts (postauth)
	 *	string	included_files[] {
	 *		string	selector
	 *		string	filename
	 *		string	contents
	 *	}
	 */
	if ((r = sshbuf_put_stringb(m, conf)) != 0 ||
	    (r = sshbuf_put_stringb(m, confdata)) != 0 ||
	    (r = sshbuf_put_u64(m, options.timing_secret)) != 0 ||
	    (r = sshbuf_put_stringb(m, hostkeys)) != 0 ||
	    (r = sshbuf_put_stringb(m, ssh->kex->server_version)) != 0 ||
	    (r = sshbuf_put_stringb(m, ssh->kex->client_version)) != 0 ||
	    (r = sshbuf_put_stringb(m, monitor_get_keystate())) != 0 ||
	    (r = sshbuf_put_string(m, pw_name, pw_len)) != 0 ||
	    (r = sshbuf_put_stringb(m, authctxt ? authctxt->session_info : NULL)) != 0 ||
	    (r = sshbuf_put_stringb(m, opts)) != 0 ||
	    (r = sshbuf_put_stringb(m, inc)) != 0)
		fatal_fr(r, "compose config");
	if (ssh_msg_send(fd, 0, m) == -1)
		error_f("ssh_msg_send failed");

	sshbuf_free(m);
	sshbuf_free(inc);
	sshbuf_free(opts);
	sshbuf_free(confdata);

	debug3_f("done");
}

static int
privsep_preauth(struct ssh *ssh)
{
	int devnull, i, hold[3], status, r, config_s[2], opt;
	pid_t pid;

	/*
	 * We need to ensure that we don't assign the monitor fds to
	 * ones that will collide with the clients, so reserve a few
	 * now. They will be freed momentarily.
	 */
	if ((devnull = open(_PATH_DEVNULL, O_RDWR)) == -1)
		fatal_f("open %s: %s", _PATH_DEVNULL, strerror(errno));
	for (i = 0; i < (int)(sizeof(hold) / sizeof(*hold)); i++) {
		if ((hold[i] = dup(devnull)) == -1)
			fatal_f("dup devnull: %s", strerror(errno));
		fcntl(hold[i], F_SETFD, FD_CLOEXEC);
	}

	/* Set up unprivileged child process to deal with network data */
	pmonitor = monitor_init();
	/* Store a pointer to the kex for later rekeying */
	pmonitor->m_pkex = &ssh->kex;

	if ((pid = fork()) == -1)
		fatal("fork of unprivileged child failed");
	else if (pid != 0) {
		debug2("Network child is on pid %ld", (long)pid);

		close(devnull);
		for (i = 0; i < (int)(sizeof(hold) / sizeof(*hold)); i++)
			close(hold[i]);

		pmonitor->m_pid = pid;
		if (have_agent) {
			r = ssh_get_authentication_socket(&auth_sock);
			if (r != 0) {
				error_r(r, "Could not get agent socket");
				have_agent = 0;
			}
		}
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
		return 1;
	} else {
		/* child */
		close(pmonitor->m_sendfd);
		close(pmonitor->m_log_recvfd);

		/*
		 * Arrange unpriv-preauth child process fds:
		 * 0, 1 network socket
		 * 2 optional stderr
		 * 3 reserved
		 * 4 monitor message socket
		 * 5 monitor logging socket
		 * 6 configuration message socket
		 *
		 * We know that the monitor sockets will have fds > 4 because
		 * of the reserved fds in hold[].
		 */

		/* XXX simplify this by passing config via a monitor call */

		/* Send configuration to ancestor sshd-monitor process */
		if (socketpair(AF_UNIX, SOCK_STREAM, 0, config_s) == -1)
			fatal("socketpair: %s", strerror(errno));
		/* XXX hack: need to move stuff to monitor calls */
		opt = 128*1024;
		if (setsockopt(config_s[0], SOL_SOCKET, SO_SNDBUF,
		    &opt, sizeof opt) == -1)
			fatal_f("setsockopt SO_SNDBUF: %s", strerror(errno));

		send_privsep_state(ssh, config_s[0], cfg);

		if (dup2(ssh_packet_get_connection_in(ssh),
		    STDIN_FILENO) == -1)
			debug3_f("dup2 stdin: %s", strerror(errno));
		if (dup2(ssh_packet_get_connection_out(ssh),
		    STDOUT_FILENO) == -1)
			debug3_f("dup2 stout: %s", strerror(errno));
		/* leave stderr as-is */
		log_redirect_stderr_to(NULL); /* dup can clobber log fd */
		if (dup2(pmonitor->m_recvfd, PRIVSEP_MONITOR_FD) == -1)
			debug3_f("dup2 PRIVSEP_MONITOR_FD: %s", strerror(errno));
		if (dup2(pmonitor->m_log_sendfd, PRIVSEP_LOG_FD) == -1)
			debug3_f("dup2 PRIVSEP_LOG_FD: %s", strerror(errno));
		if (dup2(config_s[1], PRIVSEP_CONFIG_PASS_FD) == -1)
			debug3_f("dup2 PRIVSEP_CONFIG_PASS_FD: %s", strerror(errno));
		closefrom(PRIVSEP_MIN_FREE_FD);

		saved_argv[0] = options.sshd_privsep_preauth_path;
		execv(options.sshd_privsep_preauth_path, saved_argv);
		fatal_f("exec of %s failed: %s",
		    options.sshd_privsep_preauth_path, strerror(errno));
	}
}

static void
privsep_postauth(struct ssh *ssh)
{
	int devnull, i, hold[3], config_s[2], opt;

debug_f("pkt %d/%d",
ssh_packet_get_connection_in(ssh),
ssh_packet_get_connection_out(ssh));

	/*
	 * We need to ensure that we don't assign the monitor fds to
	 * ones that will collide with the clients, so reserve a few
	 * now. They will be freed momentarily.
	 */
	if ((devnull = open(_PATH_DEVNULL, O_RDWR)) == -1)
		fatal_f("open %s: %s", _PATH_DEVNULL, strerror(errno));
	for (i = 0; i < (int)(sizeof(hold) / sizeof(*hold)); i++) {
		if ((hold[i] = dup(devnull)) == -1)
			fatal_f("dup devnull: %s", strerror(errno));
		fcntl(hold[i], F_SETFD, FD_CLOEXEC);
	}

	/* New socket pair */
	monitor_reinit(pmonitor);

	pmonitor->m_pid = fork();
	if (pmonitor->m_pid == -1)
		fatal("fork of unprivileged child failed");
	else if (pmonitor->m_pid != 0) {
		close(devnull);
		for (i = 0; i < (int)(sizeof(hold) / sizeof(*hold)); i++)
			close(hold[i]);

		verbose("User child is on pid %ld", (long)pmonitor->m_pid);
		sshbuf_reset(loginmsg);
		monitor_clear_keystate(ssh, pmonitor);
		monitor_child_postauth(ssh, pmonitor);

		/* NEVERREACHED */
		exit(0);
	}

	/* child */
	close(pmonitor->m_sendfd);
	close(pmonitor->m_log_recvfd);

	/*
	 * Arrange unpriv-postauth child process fds:
	 * 0, 1 network socket
	 * 2 optional stderr
	 * 3 reserved
	 * 4 monitor message socket
	 * 5 monitor logging socket
	 * 6 configuration message socket
	 *
	 * We know that the monitor sockets will have fds > 4 because
	 * of the reserved fds in hold[].
	 */

	/* XXX simplify this by passing config via a monitor call */

	/* Send configuration to ancestor sshd-monitor process */
	if (socketpair(AF_UNIX, SOCK_STREAM, 0, config_s) == -1)
		fatal("socketpair: %s", strerror(errno));
	/* XXX hack: need to move stuff to monitor calls */
	opt = 128*1024;
	if (setsockopt(config_s[0], SOL_SOCKET, SO_SNDBUF,
	    &opt, sizeof opt) == -1)
		fatal_f("setsockopt SO_SNDBUF: %s", strerror(errno));
	send_privsep_state(ssh, config_s[0], cfg);

	if (dup2(ssh_packet_get_connection_in(ssh),
	    STDIN_FILENO) == -1)
		debug3_f("dup2 stdin: %s", strerror(errno));
	if (dup2(ssh_packet_get_connection_out(ssh),
	    STDOUT_FILENO) == -1)
		debug3_f("dup2 stdout: %s", strerror(errno));
	/* leave stderr as-is */
	log_redirect_stderr_to(NULL); /* dup can clobber log fd */
	if (dup2(pmonitor->m_recvfd, PRIVSEP_MONITOR_FD) == -1)
		debug3_f("dup2 PRIVSEP_MONITOR_FD: %s", strerror(errno));
	if (dup2(pmonitor->m_log_sendfd, PRIVSEP_LOG_FD) == -1)
		debug3_f("dup2 PRIVSEP_LOG_FD: %s", strerror(errno));
	if (dup2(config_s[1], PRIVSEP_CONFIG_PASS_FD) == -1)
		debug3_f("dup2 PRIVSEP_CONFIG_PASS_FD: %s", strerror(errno));
	closefrom(PRIVSEP_MIN_FREE_FD);

	saved_argv[0] = options.sshd_privsep_postauth_path;
	execv(options.sshd_privsep_postauth_path, saved_argv);
	fatal_f("exec of %s failed: %s",
	    options.sshd_privsep_postauth_path, strerror(errno));
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
parse_hostkeys(struct sshbuf *hostkeys)
{
	int r;
	u_int num_keys = 0;
	struct sshkey *k;
	struct sshbuf *kbuf;
	const u_char *cp;
	size_t len;

	while (sshbuf_len(hostkeys) != 0) {
		if (num_keys > 2048)
			fatal_f("too many hostkeys");
		sensitive_data.host_keys = xrecallocarray(
		    sensitive_data.host_keys, num_keys, num_keys + 1,
		    sizeof(*sensitive_data.host_pubkeys));
		sensitive_data.host_pubkeys = xrecallocarray(
		    sensitive_data.host_pubkeys, num_keys, num_keys + 1,
		    sizeof(*sensitive_data.host_pubkeys));
		sensitive_data.host_certificates = xrecallocarray(
		    sensitive_data.host_certificates, num_keys, num_keys + 1,
		    sizeof(*sensitive_data.host_certificates));
		/* private key */
		k = NULL;
		if ((r = sshbuf_froms(hostkeys, &kbuf)) != 0)
			fatal_fr(r, "extract privkey");
		if (sshbuf_len(kbuf) != 0 &&
		    (r = sshkey_private_deserialize(kbuf, &k)) != 0)
			fatal_fr(r, "parse pubkey");
		sensitive_data.host_keys[num_keys] = k;
		sshbuf_free(kbuf);
		if (k)
			debug2_f("privkey %u: %s", num_keys, sshkey_ssh_name(k));
		/* public key */
		k = NULL;
		if ((r = sshbuf_get_string_direct(hostkeys, &cp, &len)) != 0)
			fatal_fr(r, "extract pubkey");
		if (len != 0 && (r = sshkey_from_blob(cp, len, &k)) != 0)
			fatal_fr(r, "parse pubkey");
		sensitive_data.host_pubkeys[num_keys] = k;
		if (k)
			debug2_f("pubkey %u: %s", num_keys, sshkey_ssh_name(k));
		/* certificate */
		k = NULL;
		if ((r = sshbuf_get_string_direct(hostkeys, &cp, &len)) != 0)
			fatal_fr(r, "extract pubkey");
		if (len != 0 && (r = sshkey_from_blob(cp, len, &k)) != 0)
			fatal_fr(r, "parse pubkey");
		sensitive_data.host_certificates[num_keys] = k;
		if (k)
			debug2_f("cert %u: %s", num_keys, sshkey_ssh_name(k));
		num_keys++;
	}
	sensitive_data.num_hostkeys = num_keys;
}

static void
recv_rexec_state(int fd, struct sshbuf *conf, uint64_t *timing_secretp)
{
	struct sshbuf *m, *inc, *hostkeys;
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
	if ((r = sshbuf_get_string(m, &cp, &len)) != 0 || /* XXX _direct */
	    (r = sshbuf_get_u64(m, timing_secretp)) != 0 ||
	    (r = sshbuf_froms(m, &hostkeys)) != 0 ||
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

	parse_hostkeys(hostkeys);

	free(cp);
	sshbuf_free(m);
	sshbuf_free(hostkeys);
	sshbuf_free(inc);

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
	int sock_in = -1, sock_out = -1, rexeced_flag = 0, have_key = 0;
	const char *remote_ip, *rdomain;
	char *line, *laddr, *logfile = NULL;
	u_int i;
	mode_t new_umask;
	Authctxt *authctxt;
	struct connection_info *connection_info = NULL;
	sigset_t sigmask;
	struct stat sb;
	uint64_t timing_secret = 0;

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

	if (!rexeced_flag)
		fatal("sshd-monitor should not be executed directly");

	closefrom(REEXEC_MIN_FREE_FD);

	if (!debug_flag && !inetd_flag) {
		startup_pipe = dup(REEXEC_STARTUP_PIPE_FD);
		close(REEXEC_STARTUP_PIPE_FD);
	}

#ifdef WITH_OPENSSL
	OpenSSL_add_all_algorithms();
#endif

	/* If requested, redirect the logs to the specified logfile. */
	if (logfile != NULL) {
		char *cp, pid_s[32];

		snprintf(pid_s, sizeof(pid_s), "%ld", (unsigned long)getpid());
		cp = percent_expand(logfile,
		    "p", pid_s,
		    "P", "sshd-monitor",
		    (char *)NULL);
		log_redirect_stderr_to(cp);
		free(cp);
	}

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

	debug("sshd version %s, %s", SSH_VERSION, SSH_OPENSSL_VERSION);

	/* Fetch our configuration */
	if ((cfg = sshbuf_new()) == NULL)
		fatal("sshbuf_new config buf failed");
	setproctitle("%s", "[rexeced]");
	recv_rexec_state(REEXEC_CONFIG_PASS_FD, cfg, &timing_secret);
	close(REEXEC_CONFIG_PASS_FD);
	parse_server_config(&options, "rexec", cfg, &includes, NULL, 1);
	/* Fill in default values for those options not explicitly set. */
	fill_default_server_options(&options);
	options.timing_secret = timing_secret;

	if (startup_pipe != -1) {
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

	if (options.num_host_key_files != sensitive_data.num_hostkeys) {
		fatal("internal error: hostkeys confused (config %u recvd %u)",
		    options.num_host_key_files, sensitive_data.num_hostkeys);
	}

	for (i = 0; i < options.num_host_key_files; i++) {
		if (sensitive_data.host_keys[i] != NULL ||
		    (have_agent && sensitive_data.host_pubkeys[i] != NULL)) {
			have_key = 1;
			break;
		}
	}
	if (!have_key)
		fatal("internal error: monitor recieved no hostkeys");

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

	/* Identify binary for sshd-unpriv-preauth */
	if (stat(options.sshd_privsep_preauth_path, &sb) != 0 ||
	    !(sb.st_mode & (S_IXOTH|S_IXUSR))) {
		fatal("%s does not exist or is not executable",
		    options.sshd_privsep_preauth_path);
	}
	debug3("using %s for unprivileged preauth",
	    options.sshd_privsep_preauth_path);

	/* Identify binary for sshd-unpriv-postauth */
	if (stat(options.sshd_privsep_postauth_path, &sb) != 0 ||
	    !(sb.st_mode & (S_IXOTH|S_IXUSR))) {
		fatal("%s does not exist or is not executable",
		    options.sshd_privsep_postauth_path);
	}

	if (privsep_preauth(ssh) != 1)
		fatal("privsep_preauth failed");

	/* Now user is authenticated */

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
	privsep_postauth(ssh);
	/* the monitor process [priv] will not return */

	exit(0);
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
