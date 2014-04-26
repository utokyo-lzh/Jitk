MACHINE_ARCH=	i386

SYSDIR?=	../sys

SRCS=		bpf_jit.c

CFLAGS+=	-D__wchar_t=int

CFLAGS+=	-g -I${SYSDIR}

CFLAGS+=	-DBPF_VALIDATE

SRCS+=		${SYSDIR}/net/bpf_jitter.c	\
		${SYSDIR}/${MACHINE_ARCH}/${MACHINE_ARCH}/bpf_jit_machdep.c

CFLAGS+=	-DBPF_JIT_COMPILER
LIBS+=		-lutil
WARNS?=		6

all:
	@gcc ${CFLAGS} -o bpf_jit ${SRCS} ${LIBS}
