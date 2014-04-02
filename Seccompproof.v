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
Require Import CpdtTactics.

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
        (TAIL: is_tail c f)
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
  - econstructor.
    + apply (Genv.init_mem_transf_partial _ _ TRANSL); eauto.
    + rewrite (transform_partial_program_main _ _ TRANSL).
      fold tge.
      rewrite symbols_preserved.
      eauto.
    + eexact A.
    + eapply sig_transl_function.
      eexact B.

  (* match states S R *)
  - constructor; auto.
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

Lemma transl_instr_no_labels:
  forall i n c l k,
  transl_instr i n = OK c ->
  find_label l c k = None.
Proof.
  destruct i; crush; destruct (n - Int.unsigned i); crush.
Qed.

Lemma psucc_ne:
  forall a b,
  a <> b -> P_of_succ_nat a <> P_of_succ_nat b.
Proof.
  unfold not.
  intros.
  apply H.
  apply SuccNat2Pos.inj.
  auto.
Qed.

Lemma transl_code_label_prefix:
  forall b c prefix x c' k,
  transl_code b = OK c ->
  transl_code (prefix ++ (x :: b)) = OK c' ->
  find_label (P_of_succ_nat (length b)) c' k = Some (c, k).
Proof.
  induction prefix.
  - intros.
    monadInv H0.
    unfold find_label; fold find_label.
    rewrite transl_instr_no_labels
      with (i:=x) (n:=(Z.pos (Pos.of_succ_nat (length b)))); auto.
    unfold ident_eq.
    destruct (peq (Pos.of_succ_nat (length b))
                  (Pos.of_succ_nat (length b))); crush.
  - intros.
    monadInv H0.
    unfold find_label; fold find_label.
    rewrite transl_instr_no_labels
      with (i:=a) (n:=(Z.pos (Pos.of_succ_nat (length (prefix ++ x :: b)))));
      auto.
    unfold ident_eq.
    destruct (peq (Pos.of_succ_nat (length b))
                  (Pos.of_succ_nat (length (prefix ++ x :: b)))).
    + rewrite app_length in e; apply psucc_ne in e; crush.
    + apply IHprefix with (x:=x); auto.
Qed.

Lemma is_tail_exists_prefix:
  forall A:Type,
  forall a b:list A,
  is_tail a b ->
  exists p,
  b = p ++ a.
Proof.
  intros.
  induction H.
  - exists nil; auto.
  - destruct IHis_tail; exists (i :: x); crush.
Qed.

Lemma is_tail_strict_prefix:
  forall A:Type,
  forall b' b:list A,
  is_tail b' b ->
  list_length_z b' < list_length_z b ->
  exists x:A,
  exists prefix:list A,
  b = prefix ++ (x :: b').
Proof.
  intros.
  destruct (is_tail_exists_prefix A b' b); auto.
  destruct x; crush.
  assert (a::x <> nil); crush.
  destruct (exists_last H1); destruct s.
  exists x1; exists x0.
  rewrite app_comm_cons; rewrite e; crush.
Qed.

Lemma is_tail_skipn:
  forall A:Type,
  forall n,
  forall l:list A,
  is_tail (skipn n l) l.
Proof.
  induction n; [ crush | destruct l; crush ].
Qed.

Lemma transl_code_label:
  forall b c b' c' k,
  transl_code b = OK c ->
  transl_code b' = OK c' ->
  is_tail b' b ->
  list_length_z b' < list_length_z b ->
  find_label (P_of_succ_nat (length b')) c k = Some (c', k).
Proof.
  intros.
  destruct (is_tail_strict_prefix instruction b' b); auto.
  destruct H3.
  apply transl_code_label_prefix with (prefix:=x0) (x:=x); crush.
Qed.

Lemma transl_code_suffix:
  forall b c b',
  transl_code b = OK c ->
  is_tail b' b ->
  exists c',
  transl_code b' = OK c'.
Proof.
  intros.
  destruct (is_tail_exists_prefix _ b' b); auto.
  clear H0.
  generalize H; clear H.
  generalize H1; clear H1.
  generalize c; clear c.
  generalize b; clear b.
  induction x.
  - intros; exists c; crush.
  - intros.
    rewrite H1 in H; clear H1.
    monadInv H.
    apply IHx with (b:=(x++b')) (c:=x0); auto.
Qed.


Lemma transl_step:
  forall S1 t S2, Seccomp.step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2, plus Cminor.step tge R1 t R2 /\ match_states S2 R2.
Proof.
  induction 1; intros R1 MST; inv MST.

  (* State -> State *)
  (* Salu_add_k *)
  - monadInv TC.
    econstructor; split.

    eapply plus_left.
    constructor.
    eapply star_step.
    constructor.

    apply eval_Ebinop with (v1 := Vint a) (v2 := Vint k).
    constructor; auto.
    constructor; auto.
    constructor.

    eapply star_step.
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

    apply is_tail_cons_left with (i := Salu_add_k k). auto.
    exact MFREE. auto.

  (* Sjmp_ja k *)
  - monadInv TC.
    remember (match - Int.unsigned k with
              | 0 => Z.pos (Pos.of_succ_nat (length b))
              | Z.pos y' => Z.pos (Pos.of_succ_nat (length b) + y')
              | Z.neg y' => Z.pos_sub (Pos.of_succ_nat (length b)) y'
              end) as newlabel.
    destruct newlabel; crush.

    monadInv TF.
    monadInv EQ0.

    destruct (transl_code_suffix b x0 (skipn (nat_of_Z off) b)).
    auto.
    apply is_tail_skipn.

    econstructor; split.
    eapply plus_left.
    constructor.
    eapply star_step.
    constructor.

    simpl.
    cut (p = P_of_succ_nat (length (skipn (nat_of_Z off) b))).
    intros; rewrite H1.
    simpl.    (* remove transl_funbody's preamble from find_label's arg *)
    apply transl_code_label with (b:=f); crush.

    apply is_tail_trans with (l2:=b).
    apply is_tail_skipn.
    apply is_tail_trans with (l2:=Sjmp_ja k :: b); crush.

    (* XXX need to prove:
        list_length_z (skipn (nat_of_Z off) b) < list_length_z f
    *)

    (* XXX need to prove:
        p = Pos.of_succ_nat (length (skipn (nat_of_Z off) b))
    *)

    apply star_refl.
    auto.
    auto.

    econstructor; crush.
    unfold transl_function; unfold transl_funbody; crush.
    apply is_tail_trans with (l2:=b).
    apply is_tail_skipn.
    apply is_tail_trans with (l2:=Sjmp_ja k :: b); crush.

(*
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

*)

(* End TRANSLATION. *)
