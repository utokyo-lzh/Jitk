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

Lemma valid_access_load_int:
  forall m b ofs,
  Mem.valid_access m Mint32 b ofs Readable ->
  exists v, Mem.load Mint32 m b ofs = Some (Vint v).
Proof.
(*
  intros.
  destruct (Mem.valid_access_load m Mint32 b ofs); auto.
  cut (Val.has_type x 
  destruct x.
  cut (
*)
Abort.
