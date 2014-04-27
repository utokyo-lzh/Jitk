CFLAGS += -D_GNU_SOURCE -fPIC -g -I.

LEX = flex
YACC = bison

all: secdump.so bpf-as

secdump.so: secdump.o bpf.o
	$(CC) $(CFLAGS) -shared -o $@ $^ -ldl

bpf-as: bpf-as.o bpf_exp.lex.o bpf_exp.yacc.o

bpf_exp.lex.o : bpf_exp.yacc.c

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

%.yacc.c: %.y
	$(YACC) -o $@ -d $<

%.lex.c: %.l
	$(LEX) -o $@ $<

clean:
	rm -f *.o *.so *.lex.* *.yacc.* bpf-as
