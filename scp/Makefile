#	$OpenBSD: Makefile,v 1.18 2017/12/10 19:37:57 deraadt Exp $

.PATH:		${.CURDIR}/..

SRCS=	scp.c
SRCS+=	atomicio.c cleanup.c fatal.c progressmeter.c utf8.c
SRCS+=	${SRCS_BASE}

PROG=	scp
BINOWN=	root

BINMODE?=555

BINDIR=	/usr/bin

.include <bsd.prog.mk>
