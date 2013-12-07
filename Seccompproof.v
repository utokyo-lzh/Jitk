Require Import compcert.backend.RTL.
Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Op.
Require Import Seccomp.
Require Import Seccompjit.

(* Section PRESERVATION. *)

Variable prog: Seccomp.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: Seccompjit.transl_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  exact (Genv.find_symbol_transf_partial _ _ TRANSL).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (fd: fundef),
  Genv.find_funct_ptr ge b = Some fd ->
  exists tfd, Genv.find_funct_ptr tge b = Some tfd /\ transl_fundef fd = OK tfd.
Proof.
  exact (Genv.find_funct_ptr_transf_partial _ _ TRANSL).
Qed.

Lemma functions_translated:
  forall (v: val) (fd: Seccomp.fundef),
  Genv.find_funct ge v = Some fd ->
  exists tfd,
  Genv.find_funct tge v = Some tfd /\ transl_fundef fd = OK tfd.
Proof.
  exact (Genv.find_funct_transf_partial transl_fundef _ TRANSL).
Qed.

Lemma sig_transl_function:
  forall fd tfd,
  transl_fundef fd = OK tfd ->
  RTL.funsig tfd = mksignature nil (Some Tint).
Proof.
  intros.
  destruct fd; monadInv H; auto.
  monadInv EQ.
  auto.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  exact (Genv.find_var_info_transf_partial transl_fundef _ TRANSL).
Qed.

(*
Inductive match_instr (tc: RTL.code): Seccomp.instruction -> node -> node -> Prop :=
  | match_Salu_add_k: forall
      match_instr tc (Salu_add_k k) ns 
  .
*)

Inductive match_states: Seccomp.state -> RTL.state -> Prop :=
  | match_state:
      forall a x sm f pc m tstack tf tsp tpc tregs tm jmap
        (MA: Vint a = tregs#reg_a)
        (MX: Vint x = tregs#reg_x)
        (TF: transl_function f = OK (mkfnmap tf jmap))
        (MEXT: Mem.extends m tm)
        (MS: tstack = nil)
        (MPC: tpc = (ZMap.get pc jmap))
        (MSP: tsp = Vint Int.zero),
      match_states (Seccomp.State a x sm f pc m)
                   (RTL.State tstack tf tsp tpc tregs tm)
  | match_callstate:
      forall fd m tstack tfd targs tm
        (TF: transl_fundef fd = OK tfd)
        (MEXT: Mem.extends m tm)
        (MS: tstack = nil)
        (MARGS: targs = nil),
      match_states (Seccomp.Callstate fd m)
                   (RTL.Callstate tstack tfd targs tm)
  | match_returnstate:
      forall v m tstack tv tm
        (MV: Vint v = tv)
        (MEXT: Mem.extends m tm)
        (MS: tstack = nil),
      match_states (Seccomp.Returnstate v m)
                   (RTL.Returnstate tstack tv tm)
  .

Lemma transl_initial_states:
  forall S, Seccomp.initial_state prog S ->
  exists R, RTL.initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto.
  intros (tf, (A, B)).

  econstructor; split.

  (* RTL.initial_state tprog R *)
  econstructor.
  apply (Genv.init_mem_transf_partial _ _ TRANSL); eauto.
  rewrite (transform_partial_program_main _ _ TRANSL).
  fold tge.
  rewrite symbols_preserved.
  eauto.
  eexact A.
  eapply sig_transl_function.
  eexact B.

  (* match states S R *)
  constructor; auto.
  apply Mem.extends_refl.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> Seccomp.final_state S r -> RTL.final_state R r.
Proof.
  intros.
  inv H0.
  inv H.
  constructor.
Qed.

(*
Lemma transl_step:
  forall S1 t S2, Seccomp.step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2, star RTL.step tge R1 t R2 /\ match_states S2 R2.
*)

(* End PRESERVATION. *)
