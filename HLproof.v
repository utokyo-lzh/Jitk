Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import CpdtTactics.
Require HLspec.
Require Seccomp.
Require Seccompspec.

Definition semantics (p: HLspec.program) :=
  Semantics HLspec.step (HLspec.initial_state p) HLspec.final_state (Genv.globalenv p).

Variable prog: HLspec.program.
Variable tprog: Seccomp.program.
Hypothesis TRANSL: HLspec.transl_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  exact (Genv.find_symbol_transf_partial _ _ TRANSL).
Qed.

Definition mem_inj := Mem.mem_inj inject_id.

Inductive match_states: HLspec.state -> Seccomp.state -> Prop :=
  | match_state:
    forall d f c m ta tx tsm tf tc tp tm
      (TF: HLspec.transl_function f = tf),
      match_states (HLspec.State d f c m)
                   (Seccomp.State ta tx tsm tf tc tp tm)
  | match_callstate:
    forall d fd m tfd tp tm
      (TF: HLspec.transl_fundef fd = OK tfd)
      (MINJ: mem_inj m tm),
      match_states (HLspec.Callstate d fd m)
                   (Seccomp.Callstate tfd tp tm)
  | match_returnstate:
    forall a m tv tm
      (MV: HLspec.action_enc a = tv)
      (MINJ: mem_inj m tm),
      match_states (HLspec.Returnstate a m)
                   (Seccomp.Returnstate tv tm)
  .

Lemma transl_initial_states:
  forall S, HLspec.initial_state prog S ->
  exists R, Seccomp.initial_state tprog R /\ match_states S R.
Proof.
Admitted.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> HLspec.final_state S r -> Seccomp.final_state R r.
Proof.
Admitted.

Lemma transl_step:
  forall S1 t S2, HLspec.step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2, plus Seccomp.step tge R1 t R2 /\ match_states S2 R2.
Proof.
Admitted.

Theorem transl_program_correct:
  forward_simulation (semantics prog) (Seccompspec.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step.
Qed.
