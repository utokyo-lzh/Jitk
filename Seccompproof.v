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
Require Import Seccompspec.

(* Section TRANSLATION. *)

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

Definition mem_inj := Mem.mem_inj inject_id.

Lemma inj_refl:
  forall m, mem_inj m m.
Proof.
  intros.
  constructor; intros; unfold inject_id in H; inv H.

  replace (ofs + 0) with ofs by omega.
  auto.

  apply Z.divide_0_r.

  replace (ofs + 0) with ofs by omega.
  apply memval_lessdef_refl.
Qed.

Lemma inj_trans:
  forall m1 m2 m3,
  mem_inj m1 m2 -> mem_inj m2 m3 -> mem_inj m1 m3.
Proof.
  unfold mem_inj.
  apply Mem.mem_inj_compose.
Qed.

Lemma free_alloc_inj:
  forall m1 m2 b lo hi m2',
  Mem.alloc m1 lo hi = (m2, b) ->
  Mem.free m2 b lo hi = Some m2' ->
  mem_inj m1 m2'.
Proof.
  intros.
  apply (Mem.free_right_inj inject_id m1 m2 b lo hi m2').
  apply (Mem.alloc_right_inj inject_id m1 m1 lo hi b m2).
  exact (inj_refl m1). auto. auto.

  intros.
  apply (Mem.fresh_block_alloc m1 lo hi m2 b).
  auto.
  apply (Mem.perm_valid_block m1 b') in H2.
  unfold inject_id in H1.
  inv H1.
  auto.
Qed.

Inductive match_states: Seccomp.state -> Cminor.state -> Prop :=
  | match_state:
      forall a x sm f c m tf ts tk tsp te tm b tm'
        (MA: Some (Vint a) = te!reg_a)
        (MX: Some (Vint x) = te!reg_x)
        (TF: transl_function f = OK tf)
        (TC: transl_code c = OK ts)
        (MK: call_cont tk = Kstop)
        (MSP: tsp = Vptr b Int.zero)
(*        (MPERM: Mem.range_perm tm b 0 tf.(fn_stackspace) Cur Freeable) *)
        (MFREE: Mem.free tm b 0 tf.(fn_stackspace) = Some tm')
        (MINJ: mem_inj m tm'),
      match_states (Seccomp.State a x sm f c m)
                   (Cminor.State tf ts tk tsp te tm)
  | match_callstate:
      forall fd m tfd targs tk tm
        (TF: transl_fundef fd = OK tfd)
        (MINJ: mem_inj m tm)
        (MARGS: targs = nil)
        (MK: call_cont tk = Kstop),
      match_states (Seccomp.Callstate fd m)
                   (Cminor.Callstate tfd targs tk tm)
  | match_returnstate:
      forall v m tv tk tm
        (MV: Vint v = tv)
        (MINJ: mem_inj m tm)
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
  apply inj_refl.
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
  exists R2, plus Cminor.step tge R1 t R2 /\ match_states S2 R2.
Proof.
  induction 1; intros R1 MST; inv MST.

  (* State -> State *)
  monadInv TC.
  econstructor; split.

  eapply plus_left.
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

  exact MFREE. auto.

  (* State -> ReturnState *)
  monadInv TC.
(*
  match goal with
    [ H: Mem.range_perm _ _ _ _ _ _ |- _ ] =>
      apply Mem.range_perm_free in H; inv H
  end.
*)
  econstructor; split.
  eapply plus_left.
  constructor.
  eapply star_step.
  constructor.
  eapply star_step.
  constructor.
  constructor; rewrite <- MA; auto.

  exact MFREE.
(*
  match goal with [ H: Mem.free _ _ _ _ = Some _ |- _ ] => exact H end.
*)
  apply star_refl.
  auto.
  auto.
  auto.

  constructor.
  auto.
  auto.

  simpl.
  auto.

  (* CallState -> State *)
  monadInv TF.
  monadInv EQ.
  monadInv EQ0.
  econstructor; split.

  eapply plus_left.
  apply step_internal_function with
    (m' := (fst (Mem.alloc tm 0 (seccomp_memwords * 4))))
    (sp := (snd (Mem.alloc tm 0 (seccomp_memwords * 4)))); auto.
  eapply star_step.
  constructor.
  eapply star_step.
  constructor.  constructor; constructor.
  eapply star_step.
  constructor.
  eapply star_step.
  constructor.
  eapply star_step.
  constructor.  constructor; constructor.
  eapply star_step.
  constructor.
  eapply star_step.
  constructor.
  eapply star_step.
  constructor.  constructor; constructor.
  eapply star_step.
  constructor.
  apply star_refl.

  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.
  auto.

  destruct (Mem.range_perm_free
    (fst (Mem.alloc tm 0 (seccomp_memwords * 4)))
    (snd (Mem.alloc tm 0 (seccomp_memwords * 4))) 0 
    (seccomp_memwords * 4)).
  unfold Mem.range_perm.
  intros.
  apply Mem.perm_alloc_2 with
    (m1 := tm)
    (lo := 0)
    (hi := seccomp_memwords * 4); auto.

  econstructor; auto.
  unfold transl_function; unfold transl_funbody; rewrite EQ; auto.
  exact e.

  apply (free_alloc_inj tm
    (fst (Mem.alloc tm 0 (seccomp_memwords * 4)))
    (snd (Mem.alloc tm 0 (seccomp_memwords * 4)))
    0 (seccomp_memwords * 4) _) in e.
  apply (inj_trans m tm _); auto.
  auto.
Qed.

Theorem transl_program_correct:
  forward_simulation (Seccompspec.semantics prog) (Cminor.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step.
Qed.

(* End TRANSLATION. *)
