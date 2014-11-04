include compcert/Makefile.config

COQINC = -R $(ARCH) "" -R compcert compcert
#COQEXE = coqtop $(COQINC) -batch -load-vernac-source
#COQC = coqc $(COQINC)
#COQDEP = coqdep $(COQINC)

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
	HLtrans.v \
	MiscLemmas.v \
	InetDiagConf.v \
	InetDiag.v \
	InetDiagJit.v \
	Stackuse.v \
	Seccompall.v \
	Arch.v

PROOFFILES = \
	HLproof.v \
	Seccompencproof.v \
	Seccompproof.v \
	Seccompbproof.v \
	InetDiagProof.v

all:	tests/test_seccomp.native \
	tests/test_enc.native \
	tests/test_gen.native \
	tests/test_gen_nbytes.native \
	tests/test_gencminor.native \
	tests/test_hlspec.native \
	tests/test_inetdiag.native \
	$(patsubst %,examples/%/dump_bytes,direct vsftpd openssh) \
	examples/direct/bpf-direct

tests/test_%.native: tests/test_%.ml codegen/extraction.vo
	rm -f $@
	$(OCAMLBUILD) $(OCAMLINC) -no-links $@
	ln -s $(CURDIR)/_build/$@ $@

examples/%/dump_bytes: examples/%/dump_bytes.c
	gcc $< -o $@

examples/%/bpf-direct: examples/%/bpf-direct.c
	gcc $< -o $@

codegen/extraction.vo: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(FILES) $(PROOFFILES)
	coq_makefile -install none $(COQINC) $(FILES) $(PROOFFILES) -o $@

Arch.v: Makefile
	@echo "Require Export compcert.$(ARCH).Asm." > $@
	@echo "Require Export compcert.$(ARCH).Asmgen." >> $@

.PRECIOUS: tests/test_%.native

clean:
	rm -rf _build *.vo *.glob tests/*.native
	cd codegen && rm -f *.ml *.mli *.mlo *.glob *.vo
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Arch.v
