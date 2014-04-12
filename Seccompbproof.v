Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.common.Behaviors.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Op.
Require Import Seccomp.
Require Import Seccompspec.
Require Import Seccompfilter.
Require Import Seccompjit.
Require Import CpdtTactics.

Theorem seccomp_terminates:
  forall prog,
  seccomp_filter prog = true ->
  exists t r,
  program_behaves (Seccompspec.semantics prog) (Terminates t r).
Proof.
  intros.
  destruct prog.
  destruct prog_defs; crush.
  destruct p.
  destruct g; [ idtac | crush ].
  destruct f; crush.
  destruct prog_defs ; [ idtac | crush ].

  econstructor.
  econstructor.
  econstructor.

  (* initial_state *)
  - econstructor.
    (* XXX *)

  (* state_behaves *)
  (* XXX *)
Admitted.

Theorem transl_terminates:
  forall prog tprog,
  seccomp_filter prog = true ->
  Seccompjit.transl_program prog = OK tprog ->
  exists t r,
  program_behaves (Cminor.semantics tprog) (Terminates t r).
Proof.
  intros.
  destruct (seccomp_terminates prog); [ auto | destruct H1 ].
  econstructor.
  econstructor.

  apply forward_simulation_same_safe_behavior
    with (L1:=(Seccompspec.semantics prog)).

  (* forward_simulation *)
  - apply transl_program_correct.

  (* program_behaves *)
  - exact H1.

  (* not_wrong *)
  - crush.
Qed.
