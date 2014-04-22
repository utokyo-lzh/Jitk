include compcert/Makefile.config

COQINC = -I $(ARCH) -R compcert compcert -R c ''
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
	Seccompconf.v \
	Seccomp.v \
	Cminorp.v \
	$(ARCH)/Asmp.v \
	Seccompjit.v \
	Seccompspec.v \
	Seccompfilter.v \
	Seccompenc.v \
	HLspec.v \
	HLproof.v \
	MiscLemmas.v \
	Seccompencproof.v \
	Seccompproof.v \
	Seccompbproof.v \
	InetDiag.v

all:	tests/test_seccomp.native \
	tests/test_enc.native \
	tests/test_gen.native \
	tests/test_gencminor.native \
	tests/test_hlspec.native \
	tests/test_inetdiag.native \
	$(patsubst %,examples/%/dump_bytes,direct vsftpd openssh)

tests/test_%.native: tests/test_%.ml codegen/extraction.vo
	rm -f $@
	$(OCAMLBUILD) $(OCAMLINC) -no-links $@
	ln -s $(CURDIR)/_build/$@ $@

examples/%/dump_bytes: examples/%/dump_bytes.c
	gcc $< -o $@

codegen/extraction.vo: $(FILES:.v=.vo)

%.vo: %.v
	$(COQC) $*.v

c/%.v: c/%.c
	./compcert/clightgen $<

.PRECIOUS: c/%.v tests/test_%.native

depend: $(FILES)
	$(COQDEP) $^ \
	> .depend

clean:
	rm -rf _build *.vo *.glob *.native
	cd codegen && rm -f *.ml *.mli *.mlo *.glob *.vo

include .depend
