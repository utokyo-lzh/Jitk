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
Inductive xstate: Type :=
  | Xinit: forall (s: Cminor.state), xstate
  | Xdone: forall (s: Cminor.state), xstate.

Inductive xinitial_state (p: Cminor.program): xstate -> Prop :=
  | Xinit_init:
    forall s, Cminor.initial_state p s -> xinitial_state p (Xinit s).

Inductive xstep: getype -> xstate -> trace -> xstate -> Prop :=
  | Xstep_init_to_done:
    forall ge s t s', Cminor.step ge s t s' -> xstep ge (Xinit s) t (Xdone s)
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
  - intros.
    destruct s1.
    inversion H.
 inversion H0.
    + exists s.  split.
      * econstructor.  
Qed.

End TRANSLATION_CMINORX_TO_CMINOR.

Section TRANSLATION.

Variable prog: Cminor.program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: Seccompjit.wrap_cminorp prog = tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  subst ge.  subst tge.  subst tprog.
  apply Genv.find_symbol_transf.
Qed.

Inductive match_states : Cminor.state -> Cminor.state -> Prop :=
  | match_state:
    forall 
  | match_returnstate:
    forall v k m,
    match_states (Cminor.Returnstate v k m) (Cminor.Returnstate v k m).

Theorem transl_program_correct:
  forward_simulation (Cminorp.semantics prog) (Cminor.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
