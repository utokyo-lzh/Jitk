include compcert/Makefile.config

COQINC = -I . -R compcert compcert -R c ''
COQEXE = coqtop $(COQINC) -batch -load-vernac-source
COQC = coqc $(COQINC)
COQDEP = coqdep $(COQINC)

OCAMLBUILD = ocamlbuild -lib str
OCAMLINC   = \
	-I codegen -I compcert/extraction \
	-I compcert/lib -I compcert/common -I compcert/driver \
	-I compcert/backend -I compcert/cfrontend -I compcert/cparser \
	-I compcert/$(ARCH)/$(VARIANT) -I compcert/$(ARCH)

FILES = CpdtTactics.v \
	Seccomp.v Seccompjit.v Seccompspec.v Seccompenc.v \
	Seccompencproof.v #Seccompproof.v

all: test_seccomp.native test_enc.native

test_seccomp.native: test_seccomp.ml codegen/extraction.vo
	$(OCAMLBUILD) $(OCAMLINC) $@

test_enc.native: test_enc.ml codegen/extraction.vo
	$(OCAMLBUILD) $(OCAMLINC) $@

codegen/extraction.vo: $(FILES:.v=.vo)

%.vo: %.v
	$(COQC) $*.v

c/%.v: c/%.c
	./compcert/clightgen $<

.PRECIOUS: c/%.v

clean:
	rm -rf _build *.vo *.glob *.native
	cd codegen && rm -f *.ml *.mli *.mlo *.glob *.vo
