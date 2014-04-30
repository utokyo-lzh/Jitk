/*
 * Seccomp filter example for x86 (32-bit and 64-bit) with BPF macros
 *
 * Copyright (c) 2012 The Chromium OS Authors <chromium-os-dev@chromium.org>
 * Author: Will Drewry <wad@chromium.org>
 *
 * The code may be used by anyone for any purpose,
 * and can serve as a starting point for developing
 * applications using prctl(PR_SET_SECCOMP, 2, ...).
 */
#if defined(__i386__) || defined(__x86_64__)
#define SUPPORTED_ARCH 1
#endif

#if defined(SUPPORTED_ARCH)
#define __USE_GNU 1
#define _GNU_SOURCE 1

#include <linux/audit.h>
#include <linux/types.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <linux/unistd.h>
#include <signal.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <sys/prctl.h>
#include <unistd.h>
#include <errno.h>
#include <sys/time.h>

#define syscall_arg(_n) (offsetof(struct seccomp_data, args[_n]))
#define syscall_nr (offsetof(struct seccomp_data, nr))

#if defined(__i386__)
#define REG_RESULT	REG_EAX
#define REG_SYSCALL	REG_EAX
#define REG_ARG0	REG_EBX
#define REG_ARG1	REG_ECX
#define REG_ARG2	REG_EDX
#define REG_ARG3	REG_ESI
#define REG_ARG4	REG_EDI
#define REG_ARG5	REG_EBP
#elif defined(__x86_64__)
#define REG_RESULT	REG_RAX
#define REG_SYSCALL	REG_RAX
#define REG_ARG0	REG_RDI
#define REG_ARG1	REG_RSI
#define REG_ARG2	REG_RDX
#define REG_ARG3	REG_R10
#define REG_ARG4	REG_R8
#define REG_ARG5	REG_R9
#endif

#ifndef PR_SET_NO_NEW_PRIVS
#define PR_SET_NO_NEW_PRIVS 38
#endif

#ifndef SYS_SECCOMP
#define SYS_SECCOMP 1
#endif

static void emulator(int nr, siginfo_t *info, void *void_context)
{
	ucontext_t *ctx = (ucontext_t *)(void_context);
	int syscall;
	char *buf;
	ssize_t bytes;
	size_t len;
	if (info->si_code != SYS_SECCOMP)
		return;
	if (!ctx)
		return;
	syscall = ctx->uc_mcontext.gregs[REG_SYSCALL];
	buf = (char *) ctx->uc_mcontext.gregs[REG_ARG1];
	len = (size_t) ctx->uc_mcontext.gregs[REG_ARG2];

	if (syscall != __NR_write)
		return;
	if (ctx->uc_mcontext.gregs[REG_ARG0] != STDERR_FILENO)
		return;
	/* Redirect stderr messages to stdout. Doesn't handle EINTR, etc */
	ctx->uc_mcontext.gregs[REG_RESULT] = -1;
	if (write(STDOUT_FILENO, "[ERR] ", 6) > 0) {
		bytes = write(STDOUT_FILENO, buf, len);
		ctx->uc_mcontext.gregs[REG_RESULT] = bytes;
	}
	return;
}

static int install_emulator(void)
{
	struct sigaction act;
	sigset_t mask;
	memset(&act, 0, sizeof(act));
	sigemptyset(&mask);
	sigaddset(&mask, SIGSYS);

	act.sa_sigaction = &emulator;
	act.sa_flags = SA_SIGINFO;
	if (sigaction(SIGSYS, &act, NULL) < 0) {
		perror("sigaction");
		return -1;
	}
	if (sigprocmask(SIG_UNBLOCK, &mask, NULL)) {
		perror("sigprocmask");
		return -1;
	}
	return 0;
}

/* Simple helpers to avoid manual errors (but larger BPF programs). */
#define SC_DENY(_nr, _errno) \
        BPF_JUMP(BPF_JMP+BPF_JEQ+BPF_K, __NR_ ## _nr, 0, 1), \
        BPF_STMT(BPF_RET+BPF_K, SECCOMP_RET_ERRNO|(_errno))
#define SC_ALLOW(_nr) \
        BPF_JUMP(BPF_JMP+BPF_JEQ+BPF_K, __NR_ ## _nr, 0, 1), \
        BPF_STMT(BPF_RET+BPF_K, SECCOMP_RET_ALLOW)

#define SECCOMP_AUDIT_ARCH AUDIT_ARCH_I386
#define SECCOMP_FILTER_FAIL SECCOMP_RET_KILL

static int install_filter(void)
{
	struct sock_filter filter[] = {
        	/* Ensure the syscall arch convention is as expected. */
        	BPF_STMT(BPF_LD+BPF_W+BPF_ABS,
                	offsetof(struct seccomp_data, arch)),
        	BPF_JUMP(BPF_JMP+BPF_JEQ+BPF_K, SECCOMP_AUDIT_ARCH, 1, 0),
        	BPF_STMT(BPF_RET+BPF_K, SECCOMP_FILTER_FAIL),
        	/* Load the syscall number for checking. */
        	BPF_STMT(BPF_LD+BPF_W+BPF_ABS,
                	offsetof(struct seccomp_data, nr)),
        	SC_DENY(open, EACCES),
        	SC_ALLOW(getpid),
        	SC_ALLOW(clock_gettime),
#ifdef __NR_time /* not defined on EABI ARM */
        	SC_ALLOW(time),
#endif
        	SC_ALLOW(read),
        	SC_ALLOW(write),
        	SC_ALLOW(close),
#ifdef __NR_shutdown /* not defined on archs that go via socketcall(2) */
        	SC_ALLOW(shutdown),
#endif
        	SC_ALLOW(brk),
        	SC_ALLOW(poll),
#ifdef __NR__newselect
        	SC_ALLOW(_newselect),
#else
        	SC_ALLOW(select),
#endif
        	SC_ALLOW(madvise),
#ifdef __NR_mmap2 /* EABI ARM only has mmap2() */
        	SC_ALLOW(mmap2),
#endif
#ifdef __NR_mmap
        	SC_ALLOW(mmap),
#endif
        	SC_ALLOW(munmap),
        	SC_ALLOW(exit_group),
#ifdef __NR_rt_sigprocmask
        	SC_ALLOW(rt_sigprocmask),
#else
        	SC_ALLOW(sigprocmask),
#endif
        	SC_ALLOW(gettimeofday),
        	BPF_STMT(BPF_RET+BPF_K, SECCOMP_FILTER_FAIL),
	};
	struct sock_fprog prog = {
		.len = (unsigned short)(sizeof(filter)/sizeof(filter[0])),
		.filter = filter,
	};

	if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)) {
		perror("prctl(NO_NEW_PRIVS)");
		return 1;
	}


	if (prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog)) {
		perror("prctl");
		return 1;
	}
	return 0;
}

#define payload(_c) (_c), sizeof((_c))
int main(int argc, char **argv)
{
	char buf[4096];
	ssize_t bytes = 0;
	int x = 0;
	int i;
	//if (install_emulator()) return 1;
	if (install_filter())
		return 1;

	for (i = 0; i < 1000000; i++) {
		struct timeval tv;
		gettimeofday(&tv, NULL);
		x += tv.tv_sec;
	}
	sprintf(buf, "x=%d\n", x);
	syscall(__NR_write, STDOUT_FILENO, buf, strlen(buf));
	return 0;

	syscall(__NR_write, STDOUT_FILENO,
		payload("OHAI! WHAT IS YOUR NAME? "));
	bytes = syscall(__NR_read, STDIN_FILENO, buf, sizeof(buf));
	syscall(__NR_write, STDOUT_FILENO, payload("HELLO, "));
	syscall(__NR_write, STDOUT_FILENO, buf, bytes);
	syscall(__NR_write, STDERR_FILENO,
		payload("Error message going to STDERR\n"));
	return 0;
}
#else	/* SUPPORTED_ARCH */
/*
 * This sample is x86-only.  Since kernel samples are compiled with the
 * host toolchain, a non-x86 host will result in using only the main()
 * below.
 */
int main(void)
{
	return 1;
}
#endif	/* SUPPORTED_ARCH */
