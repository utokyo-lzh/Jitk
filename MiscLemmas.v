Require Import compcert.common.AST.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import CpdtTactics.

Lemma list_length_nat_z:
  forall A:Type,
  forall l:list A,
  list_length_z l = Z.of_nat (length l).
Proof.
  induction l.
  - crush.
  - rewrite list_length_z_cons; rewrite IHl.
    unfold length.
    rewrite Nat2Z.inj_succ.
    crush.
Qed.

Lemma length_skipn:
  forall A:Type,
  forall x,
  forall l:list A,
  (length (skipn x l) <= length l)%nat.
Proof.
  induction x.
  - crush.
  - induction l; crush.
Qed.

Lemma length_inj_bytes:
  forall l,
  length (Memdata.inj_bytes l) = length l.
Proof.
  induction l; crush.
Qed.

