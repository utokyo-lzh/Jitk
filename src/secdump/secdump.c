#include <linux/filter.h>
#include <linux/prctl.h>
#include <linux/seccomp.h>
#include <dlfcn.h>
#include <stdio.h>

void bpf_disasm_all(const struct sock_filter *f, unsigned int len);

static int (*orig_prctl)(int, unsigned long, unsigned long, unsigned long, unsigned long);

int prctl(int option, unsigned long arg2, unsigned long arg3,
	  unsigned long arg4, unsigned long arg5)
{
	if (option == PR_SET_SECCOMP && arg2 == SECCOMP_MODE_FILTER) {
		struct sock_fprog *fp = (struct sock_fprog *)arg3;
		int i, n = fp->len;

		fprintf(stderr, "\n=== SECCOMP ===\n");
		bpf_disasm_all(fp->filter, fp->len);
#if 0
		fprintf(stderr, "%d,", n);
		for (i = 0; i < n; ++i) {
			struct sock_filter *f = &fp->filter[i];
			fprintf(stderr, "%d %d %d %d,", f->code, f->jt, f->jf, f->k);
		}
		fprintf(stderr, "\n");
#endif
		fprintf(stderr, "=== SECCOMP ===\n\n");
	}
	return orig_prctl(option, arg2, arg3, arg4, arg5);
}

__attribute__ ((constructor))
static void init(void)
{
	orig_prctl = dlsym(RTLD_NEXT, "prctl");
}
