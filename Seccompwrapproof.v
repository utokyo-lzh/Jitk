Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Seccomp.
Require Import Seccompjit.
Require Import Seccompspec.
Require Import CpdtTactics.
Require Import Cminorp.
Require Import MiscLemmas.
Import ListNotations.

Section CMINORX.

Let getype := Genv.t Cminor.fundef unit.

(* An intermediate semantics for tracking execution of the prefix added by wrap_cminor.. *)
(* General plan: Cminorp p -> Cminorx (wrap p) -> Cminor (wrap p) *)

Inductive xstate: Type :=
  | Xinit: forall (s: Cminor.state), xstate
  | Xdone: forall (s: Cminor.state), xstate.

Inductive xinitial_state (p: Cminor.program): xstate -> Prop :=
  | Xinit_init:
    forall s, Cminor.initial_state p s -> xinitial_state p (Xinit s).

Inductive xstep: getype -> xstate -> trace -> xstate -> Prop :=
  | Xstep_init_to_done:
    forall ge s t s', Cminor.step ge s t s' -> xstep ge (Xinit s) t (Xdone s')
  | Xstep_done:
    forall ge s t s', Cminor.step ge s t s' -> xstep ge (Xdone s) t (Xdone s').

Inductive xfinal_state: xstate -> int -> Prop :=
  | Xdone_final:
    forall s r, Cminor.final_state s r -> xfinal_state (Xdone s) r.

Definition xsemantics (p: Cminor.program) :=
  Semantics xstep (xinitial_state p) xfinal_state (Genv.globalenv p).

End CMINORX.


Section TRANSLATION_CMINORX_TO_CMINOR.

Variable prog: Cminor.program.
Let ge := Genv.globalenv prog.

Inductive match_states: xstate -> Cminor.state -> Prop :=
  | match_init:
    forall s, match_states (Xinit s) s
  | match_done:
    forall s, match_states (Xdone s) s.

Theorem cminorx_to_cminor_correct:
  forward_simulation (xsemantics prog) (Cminor.semantics prog).
Proof.
  eapply forward_simulation_plus with (match_states:=match_states).
  - crush.
  - intros.  destruct H.  exists s.  crush.  constructor.
  - crush.  inversion H0.  rewrite <- H2 in H.  inversion H.  crush.
  - simpl.  intros.
    inversion H; inversion H0; crush.
    + exists s'.  split.  econstructor.  apply H1.  apply star_refl.  rewrite E0_right.  auto.
      constructor.
    + exists s'.  split.  econstructor.  apply H1.  apply star_refl.  rewrite E0_right.  auto.
      constructor.
Qed.

End TRANSLATION_CMINORX_TO_CMINOR.


Section TRANSLATION_CMINORP_TO_CMINORX.

Variable prog: Cminor.program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: Seccompjit.wrap_cminorp prog = tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Inductive match_states2 : Cminor.state -> xstate -> Prop :=
  | match_init2:
    forall s, match_states2 s (Xinit s)
  | match_done2:
    forall s, match_states2 s (Xdone s).

Theorem transl_program_correct:
  forward_simulation (Cminorp.semantics prog) (xsemantics tprog).
Proof.
  eapply forward_simulation_plus with (match_states:=match_states2).
  - subst tprog.  apply Genv.find_symbol_transf.
  - simpl.  intros.  exists (Xinit s1).  split; constructor.
    subst tprog.  (* XXX *)