Require Import compcert.backend.Cminor.
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
Variable tprog: Cminor.program.
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
  Cminor.funsig tfd = mksignature nil (Some Tint).
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

Inductive match_states: Seccomp.state -> Cminor.state -> Prop :=
  | match_state:
      forall a x sm f c m tf ts tk tsp te tm sp
        (MA: Some (Vint a) = te!reg_a)
        (MX: Some (Vint x) = te!reg_x)
        (TF: transl_function f = OK tf)
        (TC: transl_code c = OK ts)
        (MEXT: Mem.extends m tm)
        (MSP: tsp = Vptr sp Int.zero),
      Mem.range_perm tm sp 0 (fn_stackspace tf) Cur Freeable ->
      match_states (Seccomp.State a x sm f c m)
                   (Cminor.State tf ts tk tsp te tm)
  | match_callstate:
      forall fd m tfd targs tk tm
        (TF: transl_fundef fd = OK tfd)
        (MEXT: Mem.extends m tm)
        (MARGS: targs = nil),
      match_states (Seccomp.Callstate fd m)
                   (Cminor.Callstate tfd targs tk tm)
  | match_returnstate:
      forall v m tv tk tm
        (MV: Vint v = tv)
        (MEXT: Mem.extends m tm)
        (MK: tk = Kstop),
      match_states (Seccomp.Returnstate v m)
                   (Cminor.Returnstate tv tk tm)
  .

Lemma transl_initial_states:
  forall S, Seccomp.initial_state prog S ->
  exists R, Cminor.initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto.
  intros (tf, (A, B)).

  econstructor; split.

  (* Cminor.initial_state tprog R *)
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
  match_states S R -> Seccomp.final_state S r -> Cminor.final_state R r.
Proof.
  intros.
  inv H0.
  inv H.
  constructor.
Qed.

Lemma transl_step:
  forall S1 t S2, Seccomp.step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2, star Cminor.step tge R1 t R2 /\ match_states S2 R2.
Proof.
  induction 1; intros R1 MST; inv MST.
  monadInv TC.

  econstructor; split.

  eapply star_step.
  constructor.
  eapply star_step.
  constructor.
  eapply star_step.
  constructor.

  apply eval_Ebinop with (v1 := Vint a) (v2 := Vint k).
  constructor; auto.
  constructor; auto.
  constructor.

  eapply star_step.
  constructor.
  apply star_refl.
  auto.
  auto.
  auto.
  auto.

  econstructor; auto.
  rewrite PTree.gss; auto.
  rewrite PTree.gso; auto.
  unfold reg_x; unfold reg_a; discriminate.

  (* return case *)
  monadInv TC.

  match goal with
    [ H: Mem.range_perm _ _ _ _ _ _ |- _ ] =>
      apply Mem.range_perm_free in H; inv H
  end.

  econstructor; split.
  eapply star_step.
  constructor.
  eapply star_step.
  constructor.
  eapply star_step.
  constructor.
  constructor; rewrite <- MA; auto.

  match goal with [ H: Mem.free _ _ _ _ = Some _ |- _ ] => exact H end.
  apply star_refl.
  auto.
  auto.
  auto.

  constructor.
  auto.
(* XXX:
  m : mem
  tm : mem
  x1 : mem
  MEXT : Mem.extends m tm
  sp : block
  H : Mem.free tm sp 0 (fn_stackspace tf) = Some x1
  ============================
   Mem.extends m x1
*)

(* End PRESERVATION. *)
