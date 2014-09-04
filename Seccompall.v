Require Import Seccompfilter.
Require Import Stackuse.
Require Import compcert.driver.Compiler.

Definition bpf_to_asm (p: Seccomp.program) : res Asm.program :=
  do cmp <- Seccompfilter.transl_program_filter p;
  do asp <- Compiler.transf_cminor_program cmp;
  do asp' <- Stackuse.check_program asp;
  asp'.
