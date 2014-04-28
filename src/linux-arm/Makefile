CFLAGS += -D__LINUX_ARM_ARCH__=7
#CLFAGS += -DCONFIG_FRAME_POINTER

all: bpf_jit

bpf_jit: main.o bpf_jit_32.o
	$(CC) -o $@ $^

%.c: %.o

clean:
	rm -f *.o bpf_jit
