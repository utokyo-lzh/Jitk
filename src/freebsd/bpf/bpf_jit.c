#include <sys/cdefs.h>
#include <sys/types.h>
#include <stdio.h>
#include <stdlib.h>
#include <net/bpf.h>
#include <libutil.h>
#include <net/bpf_jitter.h>

#define MAX_INSNS 1024

int main(void)
{
	struct bpf_insn *pc;
	int nins;
	bpf_jit_filter *filter;

	pc = malloc(MAX_INSNS * sizeof(struct bpf_insn));
	if (!pc) {
		fprintf(stderr, "malloc failed\n");
		return -1;
	}
	nins = fread(pc, sizeof(struct bpf_insn), MAX_INSNS, stdin);
	if (nins == MAX_INSNS) {
		fprintf(stderr, "input too large\n");
		return -1;
	}
	fprintf(stderr, "%d instructions\n", nins);

	if ((filter = bpf_jitter(pc, nins)) == NULL) {
		fprintf(stderr, "bpf_jitter error!\n");
		return -1;
	}
	fprintf(stderr, "jit: %zd bytes\n", filter->size);
//	hexdump(filter->func, filter->size, NULL, HD_OMIT_CHARS);
	fwrite(filter->func, 1, filter->size, stdout);

	return 0;
}
