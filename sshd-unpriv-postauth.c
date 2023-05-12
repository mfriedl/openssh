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

#include <login_cap.h>	/* fixme */

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

/* Privsep fds */
#define PRIVSEP_MONITOR_FD		(STDERR_FILENO + 1)
#define PRIVSEP_LOG_FD			(STDERR_FILENO + 2)
#define PRIVSEP_MIN_FREE_FD		(STDERR_FILENO + 3)

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

/* Saved arguments to main(). */
static char **saved_argv;

u_int		num_hostkeys;
struct sshkey	**host_pubkeys;		/* all public host keys */
struct sshkey	**host_certificates;	/* all public host certificates */

/* record remote hostname or ip */
u_int utmp_len = HOST_NAME_MAX+1;

/* variables used for privilege separation */
struct monitor *pmonitor = NULL;

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

/* was a side effect of getpwnamallow in monitor */
login_cap_t *lc;			/* XXX */

/* Prototypes for various functions defined later in this file. */
static void setup_ssh2_kex(struct ssh *);

/* XXX stub */
int
mm_is_monitor(void)
{
	return 0;
}

struct sshkey *
get_hostkey_public_by_type(int type, int nid, struct ssh *ssh)
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
			key = host_certificates[i];
			break;
		default:
			key = host_pubkeys[i];
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
			return key;
		}
	}
	return NULL;
}

/* XXX remove */
struct sshkey *
get_hostkey_private_by_type(int type, int nid, struct ssh *ssh)
{
	return NULL;
}

/* XXX remove */
struct sshkey *
get_hostkey_by_index(int ind)
{
	return NULL;
}

struct sshkey *
get_hostkey_public_by_index(int ind, struct ssh *ssh)
{
	if (ind < 0 || (u_int)ind >= options.num_host_key_files)
		return (NULL);
	return host_pubkeys[ind];
}

int
get_hostkey_index(struct sshkey *key, int compare, struct ssh *ssh)
{
	u_int i;

	for (i = 0; i < options.num_host_key_files; i++) {
		if (sshkey_is_cert(key)) {
			if (key == host_certificates[i] ||
			    (compare && host_certificates[i] &&
			    sshkey_equal(key, host_certificates[i])))
				return (i);
		} else {
			if (key == host_pubkeys[i] ||
			    (compare && host_pubkeys[i] &&
			    sshkey_equal(key, host_pubkeys[i])))
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
parse_hostkeys(struct sshbuf *hostkeys)
{
	int r;
	u_int num_keys = 0;
	struct sshkey *k;
	const u_char *cp;
	size_t len;

	while (sshbuf_len(hostkeys) != 0) {
		if (num_keys > 2048)
			fatal_f("too many hostkeys");
		host_pubkeys = xrecallocarray(host_pubkeys,
		    num_keys, num_keys + 1, sizeof(*host_pubkeys));
		host_certificates = xrecallocarray(host_certificates,
		    num_keys, num_keys + 1, sizeof(*host_certificates));
		/* public key */
		k = NULL;
		if ((r = sshbuf_get_string_direct(hostkeys, &cp, &len)) != 0)
			fatal_fr(r, "extract pubkey");
		if (len != 0 && (r = sshkey_from_blob(cp, len, &k)) != 0)
			fatal_fr(r, "parse pubkey");
		host_pubkeys[num_keys] = k;
		if (k)
			debug2_f("key %u: %s", num_keys, sshkey_ssh_name(k));
		/* certificate */
		k = NULL;
		if ((r = sshbuf_get_string_direct(hostkeys, &cp, &len)) != 0)
			fatal_fr(r, "extract pubkey");
		if (len != 0 && (r = sshkey_from_blob(cp, len, &k)) != 0)
			fatal_fr(r, "parse pubkey");
		host_certificates[num_keys] = k;
		if (k)
			debug2_f("cert %u: %s", num_keys, sshkey_ssh_name(k));
		num_keys++;
	}
	num_hostkeys = num_keys;
}

static void
recv_privsep_state(struct ssh *ssh, struct sshbuf *conf,
    struct sshbuf **active_confp, uint64_t *timing_secretp)
{
	Authctxt *authctxt;
	struct sshbuf *hostkeys = NULL, *keystate = NULL;
	struct sshbuf *authinfo = NULL, *opts = NULL;
	struct passwd *pw;
	u_char *pw_name;
	int r;

	debug3_f("begin");

	mm_get_state(ssh, &includes, conf, active_confp, timing_secretp,
	    &hostkeys, &keystate, &pw_name, &authinfo, &opts);

	debug_f("keystate %zu", sshbuf_len(keystate));

	parse_hostkeys(hostkeys);

	if ((r = sshauthopt_deserialise(opts, &auth_opts)) != 0)
		fatal_fr(r, "sshauthopt_deserialise failed");

	debug3_f("packet_set_state");
	if ((r = ssh_packet_set_state(ssh, keystate)) != 0)
		fatal_fr(r, "packet_set_state");

	/* set authctxt */
	if ((authctxt = ssh->authctxt) == NULL)
		fatal_f("no authctxt for user");
	if ((pw = getpwnam(pw_name)) == NULL)
		fatal_f("user %s does not exist", pw_name);
	pw = pwcopy(pw); /* Ensure mutable */
	endpwent();
	freezero(pw->pw_passwd, strlen(pw->pw_passwd));
	authctxt->pw = pw;
	authctxt->user = pw_name;
	authctxt->valid = 1;
	authctxt->session_info = authinfo;

	lc = login_getclass(pw->pw_class);	/* XXX */

	sshbuf_free(hostkeys);
	sshbuf_free(keystate);
	sshbuf_free(opts);

	debug3_f("done");
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
	int opt, have_key = 0;
	int remote_port;
	int sock_in = -1, sock_out = -1, rexeced_flag = 0;
	const char *remote_ip;
	char *line, *logfile = NULL;
	u_int i;
	u_int64_t ibytes, obytes;
	mode_t new_umask;
	Authctxt *authctxt;
	struct connection_info *connection_info = NULL;
	sigset_t sigmask;
	uint64_t timing_secret = 0;
	struct sshbuf *active_cfg = NULL;

	closefrom(PRIVSEP_MIN_FREE_FD);
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
			/* ignore */
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
			connection_info = server_get_connection_info(ssh, 0, 0);
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

#ifdef WITH_OPENSSL
	OpenSSL_add_all_algorithms();
#endif

	/* If requested, redirect the logs to the specified logfile. */
	if (logfile != NULL) {
		char *cp, pid_s[32];

		snprintf(pid_s, sizeof(pid_s), "%ld", (unsigned long)getpid());
		cp = percent_expand(logfile,
		    "p", pid_s,
		    "P", "sshd-unpriv-postauth",
		    (char *)NULL);
		log_redirect_stderr_to(cp);
		free(cp);
	}

	log_init(__progname,
	    options.log_level == SYSLOG_LEVEL_NOT_SET ?
	    SYSLOG_LEVEL_INFO : options.log_level,
	    options.log_facility == SYSLOG_FACILITY_NOT_SET ?
	    SYSLOG_FACILITY_AUTH : options.log_facility, 1);

	if (!rexeced_flag)
		fatal("sshd-unpriv-postauth should not be executed directly");

	/* XXX can't use monitor_init(); it makes fds */
	pmonitor = xcalloc(1, sizeof(*pmonitor));
	pmonitor->m_sendfd = pmonitor->m_log_recvfd = -1;
	pmonitor->m_recvfd = PRIVSEP_MONITOR_FD;
	pmonitor->m_log_sendfd = PRIVSEP_LOG_FD;
	set_log_handler(mm_log_handler, pmonitor);

	/* Check that there are no remaining arguments. */
	if (optind < ac) {
		fprintf(stderr, "Extra argument %s.\n", av[optind]);
		exit(1);
	}

	debug("sshd version %s, %s", SSH_VERSION, SSH_OPENSSL_VERSION);

	/* Connection passed by stdin/out */
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

	if (stdfd_devnull(1, 1, 0) == -1)
		error("stdfd_devnull failed");
	debug("network sockets: %d, %d", sock_in, sock_out);

	/*
	 * Register our connection.  This turns encryption off because we do
	 * not have a key.
	 */
	if ((ssh = ssh_packet_set_connection(NULL, sock_in, sock_out)) == NULL)
		fatal("Unable to create connection");
	the_active_state = ssh;
	ssh_packet_set_server(ssh);
	pmonitor->m_pkex = &ssh->kex;

	/* Set default key authentication options */
	if ((auth_opts = sshauthopt_new_with_keys_defaults()) == NULL)
		fatal("allocation failed");

	/* allocate authentication context */
	authctxt = xcalloc(1, sizeof(*authctxt));
	ssh->authctxt = authctxt;

	/* XXX global for cleanup, access from other modules */
	the_authctxt = authctxt;

	if ((loginmsg = sshbuf_new()) == NULL)	/* XXX */
		fatal("sshbuf_new loginmsg failed");

	/* Fetch our configuration */
	if ((cfg = sshbuf_new()) == NULL)
		fatal("sshbuf_new config buf failed");
	setproctitle("%s", "[unpriv-postauth-early]");

	recv_privsep_state(ssh, cfg, &active_cfg, &timing_secret);

	parse_server_config(&options, "rexec", cfg, &includes, NULL, 1);
	/* Fill in default values for those options not explicitly set. */
	fill_default_server_options(&options);
	options.timing_secret = timing_secret; /* XXX eliminate from unpriv */
	mm_decode_activate_server_options(ssh, active_cfg);
	sshbuf_free(active_cfg);

#ifdef WITH_OPENSSL
	if (options.moduli_file != NULL)
		dh_set_moduli_file(options.moduli_file);
#endif

	if (options.num_host_key_files != num_hostkeys) {
		fatal("internal error: hostkeys confused (config %u recvd %u)",
		    options.num_host_key_files, num_hostkeys);
	}

	for (i = 0; i < options.num_host_key_files; i++) {
		if (host_pubkeys[i] != NULL) {
			have_key = 1;
			break;
		}
	}
	if (!have_key)
		fatal("internal error: recieved no hostkeys");

	/* Ensure that umask disallows at least group and world write */
	new_umask = umask(0077) | 0022;
	(void) umask(new_umask);

	/* Initialize the log (it is reinitialized below in case we forked). */
	log_init(__progname, options.log_level, options.log_facility, 1);
	set_log_handler(mm_log_handler, pmonitor);
	for (i = 0; i < options.num_log_verbose; i++)
		log_verbose_add(options.log_verbose[i]);

	/* Reinitialize the log (because of the fork above). */
	log_init(__progname, options.log_level, options.log_facility, 1);
	set_log_handler(mm_log_handler, pmonitor);

	/*
	 * Chdir to the root directory so that the current disk can be
	 * unmounted if desired.
	 */
	if (chdir("/") == -1)
		error("chdir(\"/\"): %s", strerror(errno));

	setproctitle("%s", "[unpriv-postauth]");

	/* Executed child processes don't need these. */
	fcntl(sock_out, F_SETFD, FD_CLOEXEC);
	fcntl(sock_in, F_SETFD, FD_CLOEXEC);

	ssh_signal(SIGPIPE, SIG_IGN);
	ssh_signal(SIGALRM, SIG_DFL);
	ssh_signal(SIGHUP, SIG_DFL);
	ssh_signal(SIGTERM, SIG_DFL);
	ssh_signal(SIGQUIT, SIG_DFL);
	ssh_signal(SIGCHLD, SIG_DFL);

	/* Prepare the channels layer */
	channel_init_channels(ssh);
	channel_set_af(ssh, options.address_family);
	server_process_channel_timeouts(ssh);
	server_process_permitopen(ssh);

	ssh_packet_set_nonblocking(ssh);

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

#ifdef GSSAPI
	/* Cache supported mechanism OIDs for later use */
	ssh_gssapi_prepare_supported_oids();
#endif

	setproctitle("%s", "[unpriv-postauth]");

	/* Drop privileges */
	do_setusercontext(authctxt->pw);

	/*
	 * Tell the packet layer that authentication was successful, since
	 * this information is not part of the key state.
	 */
	ssh_packet_set_authenticated(ssh);

	ssh_packet_set_timeout(ssh, options.client_alive_interval,
	    options.client_alive_count_max);

	setup_ssh2_kex(ssh);

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
setup_ssh2_kex(struct ssh *ssh)
{
	struct kex *kex;

	if ((kex = ssh->kex) == NULL)
		fatal_f("internal error: ssh->kex == NULL");

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
}

/* server specific fatal cleanup */
void
cleanup_exit(int i)
{
	_exit(i);
}
