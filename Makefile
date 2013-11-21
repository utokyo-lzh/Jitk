COQINC = -I . -R compcert compcert
COQEXE = coqtop $(COQINC) -batch -load-vernac-source
COQC = coqc $(COQINC)
OCAMLBUILD = ocamlbuild -I compcert/lib -I codegen -I compcert/extraction -I compcert/common -I compcert/driver

all: test.native

test.native: test.ml BPF.vo codegen/extraction.vo
	$(OCAMLBUILD) $@

codegen/extraction.vo: BPF.vo

%.vo: %.v
	$(COQC) $*.v

clean:
	rm -rf _build *.vo *.glob *.native
	cd codegen && rm -f *.ml *.mlo *.glob
