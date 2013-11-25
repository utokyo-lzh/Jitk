COQINC = -I . -R compcert compcert
COQEXE = coqtop $(COQINC) -batch -load-vernac-source
COQC = coqc $(COQINC)
COQDEP = coqdep $(COQINC)
OCAMLBUILD = ocamlbuild -I compcert/lib -I codegen -I compcert/extraction -I compcert/common -I compcert/driver -I compcert/backend -I compcert/ia32

FILES = Seccomp.v Seccompjit.v

all: test_seccomp.native

test_seccomp.native: test_seccomp.ml codegen/extraction.vo
	$(OCAMLBUILD) $@

codegen/extraction.vo: $(FILES:.v=.vo)

%.vo: %.v
	$(COQC) $*.v

clean:
	rm -rf _build *.vo *.glob *.native
	cd codegen && rm -f *.ml *.mlo *.glob
