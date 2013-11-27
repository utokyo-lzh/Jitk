Require Import compcert.cfrontend.Clight.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Values.
Require Import Seccomp.
Require Import Seccompjit.

Section PRESERVATION.

Variable prog: Seccomp.program.
Variable tprog: Clight.program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  exact (Genv.find_symbol_transf_partial _ _ TRANSF).
Qed.

Inductive match_states: Seccomp.state -> Clight.state -> Prop :=
  | match_state:
      forall a x m f pc tf s k e le tm,
      match_states (Seccomp.State a x m f pc)
                   (Clight.State tf s k e le tm)
  | match_callstate:
      forall f tf args k tm
        (TF: transf_fundef f = OK tf)
        ,
      match_states (Seccomp.Callstate f)
                   (Clight.Callstate tf args k tm)
  | match_returnstate:
      forall v tv k tm
        (MV: Vint v = tv),
      match_states (Seccomp.Returnstate v)
                   (Clight.Returnstate tv k tm)
  .

(*
Lemma transf_initial_states:
  forall S, Seccomp.initial_state prog S ->
  exists R, Clight.initial_state tprog R /\ match_states S R.
*)

End PRESERVATION.
