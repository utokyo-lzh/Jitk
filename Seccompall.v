Require Import Seccompfilter.
Require Import Stackuse.
Require Import compcert.driver.Compiler.
Require Import compcert.common.Errors.
Require Import compcert.common.AST.
Require Import List.
Require Import ZArith.

Open Local Scope error_monad_scope.

Definition bpf_to_asm (p: Seccomp.program) : res Asm.program :=
  do cmp <- Seccompfilter.transl_program_filter p;
  do asp <- Compiler.transf_cminor_program cmp;
  do asp' <- Stackuse.check_program asp;
  OK asp'.

Theorem bpf_to_asm_stackok: forall p p', bpf_to_asm p = OK p' ->
  forall id f, In (id, Gfun (Internal f)) (prog_defs p') ->
  forall sz, stacksize f = OK sz -> (sz <= MaxStackSize)%Z.
Proof.
  intros.
  eapply bounded_stack_useage; [|eauto].
  monadInv H.
  unfold check_program in *.
  edestruct transform_partial_program_function; eauto.
  destruct H.
  destruct x1; simpl in *; try congruence.
  monadInv H2.
  rewrite EQ2.
  monadInv EQ2.
  destruct (Coqlib.zle x2 MaxStackSize); congruence.
Qed.
