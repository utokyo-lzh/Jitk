Require Import compcert.backend.Cminor.
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
Require Import InetDiag.
Require Import InetDiagJit.
Require Import InetDiagConf.
Require Import CpdtTactics.
Require Import MiscLemmas.
Import ListNotations.

Section TRANSLATION.

Variable prog: program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  exact (Genv.find_symbol_transf_partial _ _ TRANSL).
Qed.

Inductive match_states: state -> Cminor.state -> Prop :=
  | match_state:
      forall c f e m tf ts tk tsp te tm b tm'
        (ME: Some (Vptr e Int.zero) = te!reg_entry)
        (TF: transl_function f = OK tf)
        (TC: transl_code c = OK ts)
        (MK: call_cont tk = Kstop)
        (TAIL: is_tail c f)
        (MSP: tsp = Vptr b Int.zero)
        (MFREE: Mem.free tm b 0 tf.(fn_stackspace) = Some tm')
        (MINJ: mem_inj m tm'),
      match_states (State c f e m) (Cminor.State tf ts tk tsp te tm)
  | match_callstate:
      forall fd e m tfd targs tk tm
        (TF: transl_fundef fd = OK tfd)
        (MINJ: mem_inj m tm)
        (MARGS: targs = [ Vptr e Int.zero ])
        (MK: call_cont tk = Kstop),
      match_states (Callstate fd e m) (Cminor.Callstate tfd targs tk tm)
  | match_returnstate:
      forall v m tv tk tm
        (MV: Vint v = tv)
        (MINJ: mem_inj m tm)
        (MK: tk = Kstop),
      match_states (Returnstate v m) (Cminor.Returnstate tv tk tm)
  .

Lemma function_ptr_translated:
  forall (b: block) (fd: fundef),
  Genv.find_funct_ptr ge b = Some fd ->
  exists tfd, Genv.find_funct_ptr tge b = Some tfd /\ transl_fundef fd = OK tfd.
Proof.
  exact (Genv.find_funct_ptr_transf_partial _ _ TRANSL).
Qed.

Lemma sig_transl_function:
  forall fd tfd,
  transl_fundef fd = OK tfd ->
  Cminor.funsig tfd = signature_main.
Proof.
  intros.
  destruct fd; monadInv H; auto.
  monadInv EQ.
  auto.
Qed.

Inductive cminorp_initial_state (p: Cminor.program): Cminor.state -> Prop :=
  | cminorp_initial_state_intro: forall b f m0 m1 m2 pkt,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      Mem.alloc m0 0 sizeof_entry = (m1, pkt) ->
      Mem.storebytes m1 pkt 0 (Memdata.inj_bytes entry_input) = Some m2 ->
      cminorp_initial_state p (Cminor.Callstate f [ Vptr pkt Int.zero ] Kstop m2).

Definition cminorp_semantics (p: Cminor.program) :=
  Semantics Cminor.step (cminorp_initial_state p) Cminor.final_state (Genv.globalenv p).

Lemma transl_initial_states:
  forall S, initial_state prog S ->
  exists R, cminorp_initial_state tprog R /\ match_states S R.
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
    + eexact H2.
    + eexact H3.

  (* match states S R *)
  - constructor; auto.
    apply inj_refl.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> final_state S r -> Cminor.final_state R r.
Proof.
  intros.
  inv H0.
  inv H.
  constructor.
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

Lemma length_cons:
  forall A:Type,
  forall r:list A,
  forall x:A,
  length (x :: r) = (length r + 1)%nat.
Proof.
  crush.
Qed.

Lemma length_skipn_pos':
  forall A:Type,
  forall r:list A,
  forall n:nat,
  (n <= length r)%nat ->
  (Pos.of_succ_nat
     (match n with
      | O => S (length r)
      | S l => length r - l
      end - 1)) = Pos.of_succ_nat (length (skipn n r)).
Proof.
  destruct n; crush.
  induction r.
  auto.
  rewrite -> length_skipn.
  rewrite length_cons.
  crush.
  crush.
Qed.

Lemma transl_instr_no_labels:
  forall i n c l k,
  transl_instr i n = c ->
  find_label l c k = None.
Proof.
  destruct i; crush.
  unfold transl_jmp.
  destruct l; auto; auto.
  destruct l; auto; auto.
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
      with (i:=x) (n:=(S (length b))); auto.
    unfold ident_eq.
    destruct (peq (Pos.of_succ_nat (length b))
                  (Pos.of_succ_nat (length b))); crush.
  - intros.
    monadInv H0.
    unfold find_label; fold find_label.
    rewrite transl_instr_no_labels
      with (i:=a) (n:=(S (length (prefix ++ x :: b))));
      auto.
    unfold ident_eq.
    destruct (peq (Pos.of_succ_nat (length b))
                  (Pos.of_succ_nat (length (prefix ++ x :: b)))).
    + rewrite app_length in e; apply psucc_ne in e; crush.
    + apply IHprefix with (x:=x); auto.
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

Lemma load_field_match:
  forall cond v,
  forall c f e m,
  forall tf ts tk tsp te tm,
  load_field (cond_field cond) e m = Some (Vint v) ->
  match_states (InetDiag.State c f e m) (Cminor.State tf ts tk tsp te tm) ->
  eval_expr tge tsp te tm (transl_load_field (cond_field cond)) (Vint v).
Proof.
  intros.
  inv H0.
  destruct (cond_field cond).
  unfold transl_load_field.
  unfold load_field in H.
  apply eval_Eload with (vaddr:=Vptr e i).
  apply eval_Ebinop with (v1:=Vptr e Int.zero) (v2:=Vint i).
  constructor; auto.
  constructor; auto.
  simpl. rewrite Int.add_zero_l.  auto.
  unfold Mem.loadv.

  destruct (Mem.load_inj inject_id m tm' m0 e (Int.unsigned i) e 0 (Vint v)).
  exact MINJ. exact H. crush.
  destruct H0; rewrite Z.add_0_r in H0.

  rewrite Mem.load_free_2 with (m2:=tm') (bf:=b) (lo:=0) (hi:=(fn_stackspace tf)) (v:=x).
  inversion H1. auto. auto. auto.
Qed.

Lemma cond_match:
  forall cond x,
  forall c f e m,
  forall tf ts tk tsp te tm,
  load_field (cond_field cond) e m = Some (Vint x) ->
  match_states (InetDiag.State c f e m) (Cminor.State tf ts tk tsp te tm) ->
  exists v, eval_expr tge tsp te tm (transl_cond cond) v /\ Val.bool_of_val v (eval_cond cond x).
Proof.
  intros.
  inv H.
  case_eq (eval_cond cond x).

  - intros; destruct cond.

    exists Vtrue; split.
    unfold transl_cond.
    apply eval_Ebinop with (v1:=Vint x) (v2:=Vint p).
    apply load_field_match with (c:=c) (f:=f) (e:=e) (m:=m) (tf:=tf) (ts:=ts) (tk:=tk); auto.
    constructor; constructor.
    unfold eval_cond in H. unfold eval_binop. unfold Val.cmpu.
    unfold Val.cmpu_bool. unfold Int.cmpu. crush. constructor.

    exists Vtrue; split.
    unfold transl_cond.
    apply eval_Ebinop with (v1:=Vint x) (v2:=Vint p).
    apply load_field_match with (c:=c) (f:=f) (e:=e) (m:=m) (tf:=tf) (ts:=ts) (tk:=tk); auto.
    constructor; constructor.
    unfold eval_cond in H. unfold eval_binop. unfold Val.cmpu.
    unfold Val.cmpu_bool. unfold Int.cmpu. crush. constructor.

    exists Vtrue; split.
    unfold transl_cond.
    apply eval_Ebinop with (v1:=Vint x) (v2:=Vint p).
    apply load_field_match with (c:=c) (f:=f) (e:=e) (m:=m) (tf:=tf) (ts:=ts) (tk:=tk); auto.
    constructor; constructor.
    unfold eval_cond in H. unfold eval_binop. unfold Val.cmpu.
    unfold Val.cmpu_bool. unfold Int.cmpu. crush. constructor.

    exists Vtrue; split.
    unfold transl_cond.
    apply eval_Ebinop with (v1:=Vint x) (v2:=Vint p).
    apply load_field_match with (c:=c) (f:=f) (e:=e) (m:=m) (tf:=tf) (ts:=ts) (tk:=tk); auto.
    constructor; constructor.
    unfold eval_cond in H. unfold eval_binop. unfold Val.cmpu.
    unfold Val.cmpu_bool. unfold Int.cmpu. crush. constructor.

  - intros; destruct cond.

    exists Vfalse; split.
    unfold transl_cond.
    apply eval_Ebinop with (v1:=Vint x) (v2:=Vint p).
    apply load_field_match with (c:=c) (f:=f) (e:=e) (m:=m) (tf:=tf) (ts:=ts) (tk:=tk); auto.
    constructor; constructor.
    unfold eval_cond in H. unfold eval_binop. unfold Val.cmpu.
    unfold Val.cmpu_bool. unfold Int.cmpu. crush. constructor.

    exists Vfalse; split.
    unfold transl_cond.
    apply eval_Ebinop with (v1:=Vint x) (v2:=Vint p).
    apply load_field_match with (c:=c) (f:=f) (e:=e) (m:=m) (tf:=tf) (ts:=ts) (tk:=tk); auto.
    constructor; constructor.
    unfold eval_cond in H. unfold eval_binop. unfold Val.cmpu.
    unfold Val.cmpu_bool. unfold Int.cmpu. crush. constructor.

    exists Vfalse; split.
    unfold transl_cond.
    apply eval_Ebinop with (v1:=Vint x) (v2:=Vint p).
    apply load_field_match with (c:=c) (f:=f) (e:=e) (m:=m) (tf:=tf) (ts:=ts) (tk:=tk); auto.
    constructor; constructor.
    unfold eval_cond in H. unfold eval_binop. unfold Val.cmpu.
    unfold Val.cmpu_bool. unfold Int.cmpu. crush. constructor.

    exists Vfalse; split.
    unfold transl_cond.
    apply eval_Ebinop with (v1:=Vint x) (v2:=Vint p).
    apply load_field_match with (c:=c) (f:=f) (e:=e) (m:=m) (tf:=tf) (ts:=ts) (tk:=tk); auto.
    constructor; constructor.
    unfold eval_cond in H. unfold eval_binop. unfold Val.cmpu.
    unfold Val.cmpu_bool. unfold Int.cmpu. crush. constructor.
Qed.

Lemma Is_true_eq_false : forall x:bool, ~ Is_true x -> x = false.
Proof.
  destruct x; crush.
Qed.

Lemma transl_step:
  forall S1 t S2, step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2, plus Cminor.step tge R1 t R2 /\ match_states S2 R2.
Proof.
  induction 1; intros R1 MST; inversion MST.

  (* accept *)
  - monadInv TC.
    exists (Cminor.Returnstate (Vint Int.one) (call_cont tk) tm').
    split.
    apply plus_one with (t:=Events.E0).
    apply step_return_1.
    constructor; constructor.
    exact MFREE.
    constructor; auto.

  (* Nop *)
  - monadInv TC.
    exists (Cminor.State tf x tk (Vptr b Int.zero) te tm); split.
    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    econstructor; constructor.
    econstructor; auto.
    apply is_tail_cons_left with (i := Nop).
    exact TAIL.
    exact MFREE.
    exact MINJ.

  (* Jmp Reject *)
  - monadInv TC.
    exists (Cminor.Returnstate (Vint Int.zero) (call_cont tk) tm').
    split.
    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    constructor.
    constructor.
    exact MFREE.
    unfold call_cont.
    apply star_refl.
    constructor; auto.

  (* Jmp (Loc n) *)
  - monadInv TC.
    monadInv TF.
    destruct (transl_code_suffix r x (skipn n r));
        [ auto | apply is_tail_skipn | idtac ].

    econstructor; split.
    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].

    simpl.
    rewrite length_skipn_pos'; auto.
    apply transl_code_label with (b:=f); crush.

    apply is_tail_trans with (l2:=r);
      [ apply is_tail_skipn
      | apply is_tail_trans with (l2:=Jmp (Loc n) :: r); crush ].

    apply Z.le_lt_trans with (m:=(list_length_z r));
      [ apply list_length_z_skipn
      | apply list_length_z_istail_strict with (v:=Jmp (Loc n)); auto ].

    apply star_refl.
    econstructor; crush.
    unfold transl_function.
    crush.

    apply is_tail_trans with (l2:=r);
      [ apply is_tail_skipn
      | apply is_tail_trans with (l2:=Jmp (Loc n) :: r); crush ].

  (* Cjmp true _ *)
  - remember tf as tf_orig; generalize Heqtf_orig; generalize tf_orig.
    remember ts as ts_orig; generalize Heqts_orig; generalize ts_orig.
    monadInv TC.
    monadInv TF.
    intros; rewrite Heqtf_orig; rewrite Heqts_orig.

    econstructor; split.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].

    destruct (cond_match cond v (Cjmp cond loc :: r) f e m tf_orig ts_orig tk (Vptr b Int.zero) te tm); crush.
    apply step_ifthenelse with (v:=x1); [ auto | exact H3 ].

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    apply Is_true_eq_true in H0.
    rewrite -> H0.
    constructor.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    constructor.
    apply star_refl.
    econstructor; crush.
    unfold transl_function.
    crush.
    apply is_tail_cons_left with (i:=Cjmp cond loc); assumption.

  (* Cjmp false Reject *)
  - remember tf as tf_orig; generalize Heqtf_orig; generalize tf_orig.
    remember ts as ts_orig; generalize Heqts_orig; generalize ts_orig.
    monadInv TC.
    monadInv TF.
    intros; rewrite Heqtf_orig; rewrite Heqts_orig.

    exists (Cminor.Returnstate (Vint Int.zero) (call_cont tk) tm').
    split.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].

    destruct (cond_match cond v (Cjmp cond Reject :: r) f e m tf_orig ts_orig tk (Vptr b Int.zero) te tm); crush.
    apply step_ifthenelse with (v:=x1); [ auto | exact H3 ].

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    apply Is_true_eq_false in H0.
    rewrite -> H0.
    constructor; crush.
    constructor.
    constructor.
    apply star_refl.
    constructor; auto.

    (* Cjmp false (Loc n) *)
  - remember tf as tf_orig; generalize Heqtf_orig; generalize tf_orig.
    remember ts as ts_orig; generalize Heqts_orig; generalize ts_orig.
    monadInv TC.
    monadInv TF.
    intros; rewrite Heqtf_orig; rewrite Heqts_orig.

    destruct (transl_code_suffix r x (skipn n r));
        [ auto | apply is_tail_skipn | idtac ].

    econstructor; split.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].

    destruct (cond_match cond v (Cjmp cond (Loc n) :: r) f e m tf_orig ts_orig tk (Vptr b Int.zero) te tm); crush.
    apply step_ifthenelse with (v:=x2); [ auto | exact H5 ].

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    apply Is_true_eq_false in H1.
    rewrite -> H1.
    constructor; crush.

    rewrite length_skipn_pos'; auto.
    apply transl_code_label with (b:=f); crush.

    apply is_tail_trans with (l2:=r);
      [ apply is_tail_skipn
      | apply is_tail_trans with (l2:=Cjmp cond (Loc n) :: r); crush ].

    apply Z.le_lt_trans with (m:=(list_length_z r));
      [ apply list_length_z_skipn
      | apply list_length_z_istail_strict with (v:=Cjmp cond (Loc n)); auto ].

    apply star_refl.
    econstructor; crush.
    unfold transl_function.
    crush.

    apply is_tail_trans with (l2:=r);
      [ apply is_tail_skipn
      | apply is_tail_trans with (l2:=Cjmp cond (Loc n) :: r); crush ].
Qed.

Theorem transl_program_correct:
  forward_simulation (semantics prog) (cminorp_semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step.
Qed.

End TRANSLATION.
