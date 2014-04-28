bpf_jit_arm: CFLAGS += -D__LINUX_ARM_ARCH__=7
#bpf_jit_arm: CFLAGS += -DCONFIG_FRAME_POINTER

all: bpf_jit_arm bpf_jit_ppc

bpf_jit_arm: main.o bpf_jit_arm.o
	$(CC) -o $@ $^

bpf_jit_ppc: main.o bpf_jit_ppc.o
	$(CC) -o $@ $^

%.c: %.o

clean:
	rm -f *.o bpf_jit_arm bpf_jit_ppc
