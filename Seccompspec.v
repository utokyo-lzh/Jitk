Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import compcert.lib.Coqlib.
Require Import Seccomp.
Require Import CpdtTactics.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

Lemma trace_E0:
  forall p s t s', Step (semantics p) s t s' -> t = nil.
Proof.
  intros.
  destruct H; auto.
Qed.

Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intro.
  constructor; simpl; intros.

  exists s1.
  assert (t1 = t2).
  assert (t1 = nil).
  apply (trace_E0 p s t1 s1). auto.
  destruct H0; crush.
  crush.

  constructor.
  destruct H; auto.
Qed.
