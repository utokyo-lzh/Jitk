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
	Seccompencproof.v Seccompproof.v

all:	test_seccomp.native test_enc.native \
	test_gen.native test_gencminor.native \
	$(patsubst %,examples/%/dump_bytes,direct vsftpd openssh)

test_%.native: test_%.ml codegen/extraction.vo
	rm -f $@
	$(OCAMLBUILD) $(OCAMLINC) -no-links $@
	ln -s _build/$@ .

examples/%/dump_bytes: examples/%/dump_bytes.c
	gcc $< -o $@

codegen/extraction.vo: $(FILES:.v=.vo)

%.vo: %.v
	$(COQC) $*.v

c/%.v: c/%.c
	./compcert/clightgen $<

.PRECIOUS: c/%.v test_%.native

clean:
	rm -rf _build *.vo *.glob *.native
	cd codegen && rm -f *.ml *.mli *.mlo *.glob *.vo
