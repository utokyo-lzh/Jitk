#include "kfilter.h"

extern void bpf_jit_compile(struct sk_filter *);
extern void bpf_jit_free(struct sk_filter *);

#define MAX_INSNS	1000

static void encode_filter(struct sock_filter *filter, u32 flen);

int main(void)
{
	struct sk_filter *fp;

	fp = malloc(sizeof(struct sk_filter) + MAX_INSNS * sizeof(struct sock_filter));
	memset(fp, 0, sizeof(struct sk_filter));
	fp->len = fread(fp->insns, sizeof(struct sock_filter), MAX_INSNS, stdin);
	fprintf(stderr, "bpf: %lu bytes (%u insns)\n",
		fp->len * sizeof(struct sock_filter), fp->len);
	encode_filter(fp->insns, fp->len);
	bpf_jit_compile(fp);
	bpf_jit_free(fp);
	return 0;
}

static void encode_filter(struct sock_filter *filter, u32 flen)
{
	/*
	 * Valid instructions are initialized to non-0.
	 * Invalid instructions are initialized to 0.
	 */
	static const u8 codes[] = {
		[BPF_ALU|BPF_ADD|BPF_K]  = BPF_S_ALU_ADD_K,
		[BPF_ALU|BPF_ADD|BPF_X]  = BPF_S_ALU_ADD_X,
		[BPF_ALU|BPF_SUB|BPF_K]  = BPF_S_ALU_SUB_K,
		[BPF_ALU|BPF_SUB|BPF_X]  = BPF_S_ALU_SUB_X,
		[BPF_ALU|BPF_MUL|BPF_K]  = BPF_S_ALU_MUL_K,
		[BPF_ALU|BPF_MUL|BPF_X]  = BPF_S_ALU_MUL_X,
		[BPF_ALU|BPF_DIV|BPF_X]  = BPF_S_ALU_DIV_X,
		[BPF_ALU|BPF_MOD|BPF_K]  = BPF_S_ALU_MOD_K,
		[BPF_ALU|BPF_MOD|BPF_X]  = BPF_S_ALU_MOD_X,
		[BPF_ALU|BPF_AND|BPF_K]  = BPF_S_ALU_AND_K,
		[BPF_ALU|BPF_AND|BPF_X]  = BPF_S_ALU_AND_X,
		[BPF_ALU|BPF_OR|BPF_K]   = BPF_S_ALU_OR_K,
		[BPF_ALU|BPF_OR|BPF_X]   = BPF_S_ALU_OR_X,
		[BPF_ALU|BPF_XOR|BPF_K]  = BPF_S_ALU_XOR_K,
		[BPF_ALU|BPF_XOR|BPF_X]  = BPF_S_ALU_XOR_X,
		[BPF_ALU|BPF_LSH|BPF_K]  = BPF_S_ALU_LSH_K,
		[BPF_ALU|BPF_LSH|BPF_X]  = BPF_S_ALU_LSH_X,
		[BPF_ALU|BPF_RSH|BPF_K]  = BPF_S_ALU_RSH_K,
		[BPF_ALU|BPF_RSH|BPF_X]  = BPF_S_ALU_RSH_X,
		[BPF_ALU|BPF_NEG]        = BPF_S_ALU_NEG,
		[BPF_LD|BPF_W|BPF_ABS]   = BPF_S_LD_W_ABS,
		[BPF_LD|BPF_H|BPF_ABS]   = BPF_S_LD_H_ABS,
		[BPF_LD|BPF_B|BPF_ABS]   = BPF_S_LD_B_ABS,
		[BPF_LD|BPF_W|BPF_LEN]   = BPF_S_LD_W_LEN,
		[BPF_LD|BPF_W|BPF_IND]   = BPF_S_LD_W_IND,
		[BPF_LD|BPF_H|BPF_IND]   = BPF_S_LD_H_IND,
		[BPF_LD|BPF_B|BPF_IND]   = BPF_S_LD_B_IND,
		[BPF_LD|BPF_IMM]         = BPF_S_LD_IMM,
		[BPF_LDX|BPF_W|BPF_LEN]  = BPF_S_LDX_W_LEN,
		[BPF_LDX|BPF_B|BPF_MSH]  = BPF_S_LDX_B_MSH,
		[BPF_LDX|BPF_IMM]        = BPF_S_LDX_IMM,
		[BPF_MISC|BPF_TAX]       = BPF_S_MISC_TAX,
		[BPF_MISC|BPF_TXA]       = BPF_S_MISC_TXA,
		[BPF_RET|BPF_K]          = BPF_S_RET_K,
		[BPF_RET|BPF_A]          = BPF_S_RET_A,
		[BPF_ALU|BPF_DIV|BPF_K]  = BPF_S_ALU_DIV_K,
		[BPF_LD|BPF_MEM]         = BPF_S_LD_MEM,
		[BPF_LDX|BPF_MEM]        = BPF_S_LDX_MEM,
		[BPF_ST]                 = BPF_S_ST,
		[BPF_STX]                = BPF_S_STX,
		[BPF_JMP|BPF_JA]         = BPF_S_JMP_JA,
		[BPF_JMP|BPF_JEQ|BPF_K]  = BPF_S_JMP_JEQ_K,
		[BPF_JMP|BPF_JEQ|BPF_X]  = BPF_S_JMP_JEQ_X,
		[BPF_JMP|BPF_JGE|BPF_K]  = BPF_S_JMP_JGE_K,
		[BPF_JMP|BPF_JGE|BPF_X]  = BPF_S_JMP_JGE_X,
		[BPF_JMP|BPF_JGT|BPF_K]  = BPF_S_JMP_JGT_K,
		[BPF_JMP|BPF_JGT|BPF_X]  = BPF_S_JMP_JGT_X,
		[BPF_JMP|BPF_JSET|BPF_K] = BPF_S_JMP_JSET_K,
		[BPF_JMP|BPF_JSET|BPF_X] = BPF_S_JMP_JSET_X,
	};
	int pc;

	for (pc = 0; pc < flen; pc++) {
		struct sock_filter *ftest = &filter[pc];
		u16 code = ftest->code;

		if (code >= ARRAY_SIZE(codes))
			errx(1, "too big code");
		code = codes[code];
		if (!code)
			errx(1, "unknown op code");
		ftest->code = code;
	}	
}
