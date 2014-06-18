COQINC = -I . -R compcert compcert
COQEXE = coqtop $(COQINC) -batch -load-vernac-source
COQC = coqc $(COQINC)
COQDEP = coqdep $(COQINC)

FILES = CpdtTactics.v \
	cmp.v \
	verif_cmp.v

all: $(FILES:.v=.vo)

%.vo: %.v
	$(COQC) $*.v

cmp.v: cmp.c
	compcert/clightgen $<

.PRECIOUS: c/%.v tests/test_%.native

depend: $(FILES)
	$(COQDEP) $^ \
	> .depend

clean:
	rm -rf *.vo *.glob

#include .depend
