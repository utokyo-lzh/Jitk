Require Import compcert.common.AST.
Require Import compcert.common.Errors.
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

Section TRANSLATION.

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
  forall (b: block) (fd: Seccomp.fundef),
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
  Cminor.funsig tfd = signature_main.
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
      forall a x sm f c p m tf ts tk tsp te tm b tm'
        (MP: Some (Vptr p Int.zero) = te!reg_pkt)
        (MA: Some (Vint a) = te!reg_a)
        (MX: Some (Vint x) = te!reg_x)
        (TF: transl_function f = OK tf)
        (TC: transl_code c = OK ts)
        (MK: call_cont tk = Kstop)
        (TAIL: is_tail c f)
        (MSP: tsp = Vptr b Int.zero)
        (MFREE: Mem.free tm b 0 tf.(fn_stackspace) = Some tm')
        (MINJ: mem_inj m tm'),
      match_states (Seccomp.State a x sm f c p m)
                   (Cminor.State tf ts tk tsp te tm)
  | match_callstate:
      forall fd p m tfd targs tk tm
        (TF: transl_fundef fd = OK tfd)
        (MINJ: mem_inj m tm)
        (MARGS: targs = [ Vptr p Int.zero ])
        (MK: call_cont tk = Kstop),
      match_states (Seccomp.Callstate fd p m)
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
  exists R, Cminorp.initial_state tprog R /\ match_states S R.
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
  destruct i; crush;
    try destruct (transl_alu_shift a);
    try destruct (n - Int.unsigned i);
    try destruct (n - Byte.unsigned i);
    try destruct (n - Byte.unsigned i0);
    crush.
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

Lemma length_pos:
  forall A:Type,
  forall l:list A,
  forall p,
  Z.pos p < list_length_z l ->
  (p < Pos.of_succ_nat (length l))%positive.
Proof.
  intros.
  rewrite list_length_nat_z in H.
  apply Pos.ltb_lt.
  rewrite Pos2Z.inj_ltb.
  apply Z.ltb_lt.
  apply (Z.lt_le_trans _ _ _ H).
  rewrite Zpos_P_of_succ_nat.
  crush.
Qed.

Lemma length_skipn_pos:
  forall A:Type,
  forall l:list A,
  forall p,
  Z.pos p < list_length_z l ->
  (Pos.of_succ_nat (length l) - p)%positive =
  Pos.of_succ_nat (length (skipn (Pos.to_nat p) l)).
Proof.
  intros.
  rewrite list_length_nat_z in H.
  rewrite length_skipn.
  repeat rewrite Pos.of_nat_succ.
  rewrite <- (Pos2Nat.id p) at 1.
  rewrite <- Nat2Pos.inj_sub.
  rewrite Nat2Pos.inj_iff.
  rewrite minus_Sn_m.
  auto.
  rewrite Nat2Z.inj_le.
  rewrite <- Z2Nat.inj_pos.
  rewrite Z2Nat.id.
  crush.
  crush.
  apply NPeano.Nat.sub_gt.
  rewrite Nat2Z.inj_lt.
  rewrite positive_nat_Z.
  rewrite Nat2Z.inj_succ.
  crush.
  crush.
  elim (Pos2Nat.is_pos p); crush.
  rewrite Nat2Z.inj_le.
  rewrite <- Z2Nat.inj_pos.
  rewrite Z2Nat.id.
  crush.
  crush.
Qed.

Lemma length_skipn_pos':
  forall A:Type,
  forall b:list A,
  forall z,
  0 <= z < list_length_z b ->
  (Z.to_pos
     match - z with
     | 0 => Z.pos (Pos.of_succ_nat (length b))
     | Z.pos y => Z.pos (Pos.of_succ_nat (length b) + y)
     | Z.neg y => Z.pos_sub (Pos.of_succ_nat (length b)) y
     end) = Pos.of_succ_nat (length (skipn (nat_of_Z z) b)).
Proof.
  destruct z; crush.
  rewrite Z.pos_sub_gt;
    [ apply length_skipn_pos; auto
    | apply length_pos; auto ].
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

Ltac cond_match_binop H a i :=
  split;
  [ simpl; simpl in H; 
    try apply eval_Ebinop with (v1:=Vint a) (v2:=Vint i);
    try constructor; auto;
    simpl;
    unfold Val.cmpu; unfold Val.cmpu_bool; unfold Int.cmpu;
    try rewrite H; auto;
    rewrite negb_false_iff in H;
    generalize (Int.eq_spec (Int.and a i) Int.zero);
    rewrite H; intro HA; rewrite HA; auto
  | try constructor; try rewrite <- H; constructor ].

Lemma cond_match:
  forall cond,
  forall a x sm f op p m,
  forall tf ts tk tsp te tm,
  match_states (Seccomp.State a x sm f op p m) (Cminor.State tf ts tk tsp te tm) ->
  exists v, eval_expr tge tsp te tm (transl_cond cond) v /\ Val.bool_of_val v (eval_cond cond a x).
Proof.
  intros.
  inv H.
  case_eq (eval_cond cond a x).
  - intros; destruct cond;
    [ exists Vtrue; cond_match_binop H a i
    | exists Vtrue; cond_match_binop H a i
    | exists Vtrue; cond_match_binop H a i
    | exists (Vint (Int.and a i)); cond_match_binop H a i
    | exists Vtrue; cond_match_binop H a x
    | exists Vtrue; cond_match_binop H a x
    | exists Vtrue; cond_match_binop H a x
    | exists (Vint (Int.and a x)); cond_match_binop H a x ].
  - intros; destruct cond;
    [ exists Vfalse; cond_match_binop H a i
    | exists Vfalse; cond_match_binop H a i
    | exists Vfalse; cond_match_binop H a i
    | exists Vzero; cond_match_binop H a i
    | exists Vfalse; cond_match_binop H a x
    | exists Vfalse; cond_match_binop H a x
    | exists Vfalse; cond_match_binop H a x
    | exists Vzero; cond_match_binop H a x ].
Qed.

Lemma transl_step:
  forall S1 t S2, Seccomp.step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2, plus Cminor.step tge R1 t R2 /\ match_states S2 R2.
Proof.
  induction 1; intros R1 MST; inversion MST.

  (* State -> State *)
  (* Salu_safe op *)
  - monadInv TC.
    remember a' as a''.
    subst a'.
    econstructor; split.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].

    destruct op;
      try apply eval_Ebinop with (v1 := Vint a) (v2 := Vint i);
      try constructor; auto;
      simpl; unfold eval_alu_safe in Heqa'';
      try rewrite <- Heqa''; auto;
      try apply eval_Ebinop with (v1 := Vint a) (v2 := Vint x);
      try apply eval_Eunop with (v1 := Vint a);
      try constructor; auto; crush.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply star_refl.

    econstructor; auto.
    rewrite PTree.gso; [ auto | discriminate ].
    rewrite PTree.gss; auto.
    rewrite PTree.gso; [ auto | discriminate ].
    apply is_tail_cons_left with (i := Salu_safe op); assumption.
    exact MFREE.
    exact MINJ.

  (* Salu_div op *)
  - monadInv TC.
    remember a' as a''.
    subst a'.
    econstructor; split.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].

    destruct op; [ case_eq (Int.eq i Int.zero)
                 | case_eq (Int.eq i Int.zero)
                 | case_eq (Int.eq x Int.zero)
                 | case_eq (Int.eq x Int.zero) ]; simpl; intros.

    Ltac alu_div_0 i tm H :=
      apply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm) Ceq (Vint i) (Vzero)));
      [ apply eval_Ebinop with (v1:=Vint i) (v2:=Vzero); constructor; auto; constructor
      | unfold Val.cmpu; unfold Val.of_optbool; unfold Val.cmpu_bool; simpl; rewrite H; constructor ].
    Ltac alu_div_1f :=
      rewrite Int.eq_false; [ idtac | discriminate ].
    Ltac alu_div_2 :=
      eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ repeat constructor | idtac | auto ].
    Ltac alu_div_3 :=
      eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    Ltac alu_div_4 :=
      eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_div_0 i tm H.
    alu_div_1f.
    alu_div_2.
    alu_div_3.
    alu_div_4.
    simpl in Heqa''.  unfold Int.divu in Heqa''.

    cut (i = Int.zero); intros;
    [ rewrite H0 in Heqa''; rewrite Int.unsigned_zero in Heqa'';
      rewrite Zdiv_0_r in Heqa''; unfold Int.zero at 2; rewrite <- Heqa'';
      apply star_refl
    | replace (i = Int.zero) with (if Int.eq i Int.zero then i=Int.zero else i<>Int.zero);
      [ apply Int.eq_spec | rewrite H; reflexivity ] ].

    Ltac alu_div_1t :=
      rewrite Int.eq_true.
    Ltac alu_div_2t a i H Heqa'' :=
      apply eval_Ebinop with (v1:=Vint a) (v2:=Vint i); try constructor; auto;
      simpl; rewrite H; simpl in Heqa''; rewrite <- Heqa''; auto.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_div_0 i tm H.
    alu_div_1t.
    alu_div_2.  alu_div_2t a i H Heqa''.
    alu_div_3.
    alu_div_4.
    apply star_refl.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_div_0 i tm H.
    alu_div_1f.
    alu_div_2.
    alu_div_3.
    alu_div_4.

    simpl in Heqa''.  unfold Int.modu in Heqa''.
    cut (i = Int.zero); intros;
    [ rewrite H0 in Heqa''; rewrite Int.unsigned_zero in Heqa'';
      rewrite Zmod_0_r in Heqa''; unfold Int.zero at 2; rewrite <- Heqa'';
      apply star_refl
    | replace (i = Int.zero) with (if Int.eq i Int.zero then i=Int.zero else i<>Int.zero);
      [ apply Int.eq_spec | rewrite H; reflexivity ] ].

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_div_0 i tm H.
    alu_div_1t.
    alu_div_2.  alu_div_2t a i H Heqa''.
    alu_div_3.
    alu_div_4.
    apply star_refl.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_div_0 x tm H.
    alu_div_1f.
    alu_div_2.
    alu_div_3.
    alu_div_4.

    simpl in Heqa''.  unfold Int.divu in Heqa''.
    cut (x = Int.zero); intros;
    [ rewrite H0 in Heqa''; rewrite Int.unsigned_zero in Heqa'';
      rewrite Zdiv_0_r in Heqa''; unfold Int.zero at 2; rewrite <- Heqa'';
      apply star_refl
    | replace (x = Int.zero) with (if Int.eq x Int.zero then x=Int.zero else x<>Int.zero);
      [ apply Int.eq_spec | rewrite H; reflexivity ] ].

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_div_0 x tm H.
    alu_div_1t.
    alu_div_2.  alu_div_2t a x H Heqa''.
    alu_div_3.
    alu_div_4.
    apply star_refl.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_div_0 x tm H.
    alu_div_1f.
    alu_div_2.
    alu_div_3.
    alu_div_4.

    simpl in Heqa''.  unfold Int.modu in Heqa''.
    cut (x = Int.zero); intros;
    [ rewrite H0 in Heqa''; rewrite Int.unsigned_zero in Heqa'';
      rewrite Zmod_0_r in Heqa''; unfold Int.zero at 2; rewrite <- Heqa'';
      apply star_refl
    | replace (x = Int.zero) with (if Int.eq x Int.zero then x=Int.zero else x<>Int.zero);
      [ apply Int.eq_spec | rewrite H; reflexivity ] ].

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_div_0 x tm H.
    alu_div_1t.
    alu_div_2.  alu_div_2t a x H Heqa''.
    alu_div_3.
    alu_div_4.
    apply star_refl.

    econstructor; auto.
    rewrite PTree.gso; [ auto | discriminate ].
    rewrite PTree.gss; auto.
    rewrite PTree.gso; [ auto | discriminate ].
    apply is_tail_cons_left with (i := Salu_div op); assumption.
    exact MFREE.
    exact MINJ.

  (* Salu_shift op *)
  - monadInv TC.
    remember a' as a''.
    subst a'.
    econstructor; split.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].

    destruct op; [ case_eq (Int.ltu i Int.iwordsize)
                 | case_eq (Int.ltu i Int.iwordsize)
                 | case_eq (Int.ltu x Int.iwordsize)
                 | case_eq (Int.ltu x Int.iwordsize) ]; simpl; intros.

    Ltac alu_shift_0 i tm H :=
      apply step_ifthenelse with (v:=Val.of_optbool (Val.cmpu_bool (Mem.valid_pointer tm)
                                                                   Clt
                                                                   (Vint i) (Vint Int.iwordsize)));
      [ apply eval_Ebinop with (v1:=Vint i) (v2:=Vint Int.iwordsize); constructor; auto; constructor
      | unfold Val.cmpu; unfold Val.of_optbool; unfold Val.cmpu_bool; simpl; rewrite H; constructor ].
    Ltac alu_shift_1f :=
      rewrite Int.eq_false; [ idtac | discriminate ].
    Ltac alu_shift_2 a i :=
      eapply star_step  with (t1:=Events.E0) (t2:=Events.E0);
      [ repeat constructor; apply eval_Ebinop with (v1:=Vint a) (v2:=Vint i);
        constructor; auto
      | idtac | auto ].
    Ltac alu_shift_3 :=
      eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    Ltac alu_shift_4 :=
      eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_shift_0 i tm H.
    alu_shift_1f.
    alu_shift_2 a i.
    alu_shift_3.
    alu_shift_4.
    simpl in Heqa''.

    cut (Vint a'' = Val.shl (Vint a) (Vint i)).
    intros; rewrite <- H0; apply star_refl.

    rewrite Heqa''.  simpl.  rewrite H.  auto.

    Ltac alu_shift_1t :=
      rewrite Int.eq_true.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_shift_0 i tm H.
    alu_shift_1t.
    alu_shift_2 a i.
    alu_shift_3.
    alu_shift_4.
    simpl in Heqa''.

    cut (Vint a'' = Vint Int.zero).
    intros; rewrite <- H0; apply star_refl.

    rewrite Heqa''; rewrite oversize_shl_zero; auto.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_shift_0 i tm H.
    alu_shift_1f.
    alu_shift_2 a i.
    alu_shift_3.
    alu_shift_4.
    simpl in Heqa''.

    cut (Vint a'' = Val.shru (Vint a) (Vint i)).
    intros; rewrite <- H0; apply star_refl.

    rewrite Heqa''.  simpl.  rewrite H.  auto.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_shift_0 i tm H.
    alu_shift_1t.
    alu_shift_2 a i.
    alu_shift_3.
    alu_shift_4.
    simpl in Heqa''.

    cut (Vint a'' = Vint Int.zero).
    intros; rewrite <- H0; apply star_refl.

    rewrite Heqa''; rewrite oversize_shru_zero; auto.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_shift_0 x tm H.
    alu_shift_1f.
    alu_shift_2 a x.
    alu_shift_3.
    alu_shift_4.
    simpl in Heqa''.

    cut (Vint a'' = Val.shl (Vint a) (Vint x)).
    intros; rewrite <- H0; apply star_refl.

    rewrite Heqa''.  simpl.  rewrite H.  auto.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_shift_0 x tm H.
    alu_shift_1t.
    alu_shift_2 a x.
    alu_shift_3.
    alu_shift_4.
    simpl in Heqa''.

    cut (Vint a'' = Vint Int.zero).
    intros; rewrite <- H0; apply star_refl.

    rewrite Heqa''; rewrite oversize_shl_zero; auto.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_shift_0 x tm H.
    alu_shift_1f.
    alu_shift_2 a x.
    alu_shift_3.
    alu_shift_4.
    simpl in Heqa''.

    cut (Vint a'' = Val.shru (Vint a) (Vint x)).
    intros; rewrite <- H0; apply star_refl.

    rewrite Heqa''.  simpl.  rewrite H.  auto.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    alu_shift_0 x tm H.
    alu_shift_1t.
    alu_shift_2 a x.
    alu_shift_3.
    alu_shift_4.
    simpl in Heqa''.

    cut (Vint a'' = Vint Int.zero).
    intros; rewrite <- H0; apply star_refl.

    rewrite Heqa''; rewrite oversize_shru_zero; auto.

    econstructor; auto.
    rewrite PTree.gso; [ auto | discriminate ].
    rewrite PTree.gss; auto.
    rewrite PTree.gso; [ auto | discriminate ].
    apply is_tail_cons_left with (i := Salu_shift op); assumption.
    exact MFREE.
    exact MINJ.

  (* Sjmp_ja k *)
  - monadInv TC.
    monadInv TF.
    monadInv EQ0.

    destruct (transl_code_suffix b x1 (skipn (nat_of_Z off) b));
      [ auto | apply is_tail_skipn | idtac ].
    subst off.

    econstructor; split.
    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].

    rewrite length_skipn_pos' ; [ idtac | destruct (Int.unsigned_range k); auto ].

    simpl.    (* remove transl_funbody's preamble from find_label's arg *)
    apply transl_code_label with (b:=f); crush.

    apply is_tail_trans with (l2:=b);
      [ apply is_tail_skipn
      | apply is_tail_trans with (l2:=Sjmp_ja k :: b); crush ].

    apply Z.le_lt_trans with (m:=(list_length_z b));
      [ apply list_length_z_skipn
      | apply list_length_z_istail with (v:=(Sjmp_ja k)); auto ].

    apply star_refl.

    econstructor; crush.
    unfold transl_function; unfold transl_funbody; crush.
    apply is_tail_trans with (l2:=b).
    apply is_tail_skipn.
    apply is_tail_trans with (l2:=Sjmp_ja k :: b); crush.

  (* Sjmp_jc cond jt jf *)
  - remember tf as tf_orig; generalize Heqtf_orig; generalize tf_orig.
    remember ts as ts_orig; generalize Heqts_orig; generalize ts_orig.
    (* What a silly way to get around monadInv clearing things... *)
    monadInv TC.
    monadInv TF.
    monadInv EQ0.
    intros; rewrite Heqtf_orig; rewrite Heqts_orig.

    destruct (transl_code_suffix b x1 (skipn (nat_of_Z off) b));
      [ auto | apply is_tail_skipn | idtac ].
    subst off.

    econstructor; split.
    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    destruct (cond_match cond a x sm f (Sjmp_jc cond jt jf :: b) p m
                              tf_orig ts_orig tk (Vptr b0 Int.zero) te tm); crush.
    apply step_ifthenelse with (v:=x3); [ auto | exact H3 ].

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    destruct (eval_cond cond a x); constructor.

    (* true branch *)
    rewrite length_skipn_pos' ; [ idtac | destruct (Byte.unsigned_range jt); auto ].

    rewrite Heqtf_orig; simpl.    (* remove transl_funbody's preamble from find_label's arg *)
    apply transl_code_label with (b:=f); crush.

    apply is_tail_trans with (l2:=b);
      [ apply is_tail_skipn
      | apply is_tail_trans with (l2:=Sjmp_jc cond jt jf :: b); crush ].

    apply Z.le_lt_trans with (m:=(list_length_z b));
      [ apply list_length_z_skipn
      | apply list_length_z_istail with (v:=(Sjmp_jc cond jt jf)); auto ].

    (* false branch *)
    rewrite length_skipn_pos' ; [ idtac | destruct (Byte.unsigned_range jf); auto ].

    rewrite Heqtf_orig; simpl.    (* remove transl_funbody's preamble from find_label's arg *)
    apply transl_code_label with (b:=f); crush.

    apply is_tail_trans with (l2:=b);
      [ apply is_tail_skipn
      | apply is_tail_trans with (l2:=Sjmp_jc cond jt jf :: b); crush ].

    apply Z.le_lt_trans with (m:=(list_length_z b));
      [ apply list_length_z_skipn
      | apply list_length_z_istail with (v:=(Sjmp_jc cond jt jf)); auto ].

    apply star_refl.

    econstructor; crush.
    unfold transl_function; unfold transl_funbody; crush.
    apply is_tail_trans with (l2:=b).
    apply is_tail_skipn.
    apply is_tail_trans with (l2:=Sjmp_jc cond jt jf :: b); crush.

  (* Sld_w_abs k *)
  - monadInv TC.
    remember a' as a''.
    subst a'.  subst off.
    econstructor; split.
    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply eval_Eload with (vaddr:=Vptr p k).
    apply eval_Ebinop with (v1:=Vptr p Int.zero) (v2:=Vint k).
    constructor.  auto.
    constructor.  auto.
    simpl.  rewrite Int.add_zero_l.  auto.
    unfold Mem.loadv.

    destruct (Mem.load_inj inject_id m tm' Mint32 p (Int.unsigned k) p 0 (Vint a'')).
    exact MINJ.  exact H1.  crush. 
    destruct H2; rewrite Z.add_0_r in H2.

    rewrite Mem.load_free_2 with (m2:=tm') (bf:=b0) (lo:=0) (hi:=(fn_stackspace tf)) (v:=x0).
    inversion H3.  auto.  auto.  auto.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply star_refl.
    econstructor; try rewrite PTree.gss; try rewrite PTree.gso; auto; try discriminate.
    apply is_tail_cons_left with (i:=Sld_w_abs k); assumption.
    exact MFREE.
    exact MINJ.

  (* Sld_w_len *)
  - monadInv TC.
    econstructor; split.
    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    constructor.
    constructor.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply star_refl.
    econstructor; try rewrite PTree.gss; try rewrite PTree.gso; auto; try discriminate.
    apply is_tail_cons_left with (i := Sld_w_len); assumption.
    exact MFREE.
    exact MINJ.

  (* Sldx_w_len *)
  - monadInv TC.
    econstructor; split.
    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    constructor.
    constructor.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply star_refl.
    econstructor; try rewrite PTree.gss; try rewrite PTree.gso; auto; try discriminate.
    apply is_tail_cons_left with (i := Sldx_w_len); assumption.
    exact MFREE.
    exact MINJ.

  (* Sret_a *)
  - monadInv TC.
    econstructor; split.
    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    constructor; rewrite <- MA; auto.
    exact MFREE.

    apply star_refl.
    constructor; auto.

  (* Sret_k *)
  - monadInv TC.
    econstructor; split.
    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    constructor; constructor.
    exact MFREE.

    apply star_refl.
    constructor; auto.

  (* CallState -> State *)
  - monadInv TF.
    monadInv EQ.
    monadInv EQ0.
    econstructor; split.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ idtac | idtac | auto ].
    apply step_internal_function with
      (m' := (fst (Mem.alloc tm 0 (seccomp_memwords * 4))))
      (sp := (snd (Mem.alloc tm 0 (seccomp_memwords * 4)))); auto.
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor; constructor; constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor; constructor; constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor; constructor; constructor | idtac | auto ].
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply star_refl.

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
    constructor.
    exact e.

    apply (free_alloc_inj tm
      (fst (Mem.alloc tm 0 (seccomp_memwords * 4)))
      (snd (Mem.alloc tm 0 (seccomp_memwords * 4)))
      0 (seccomp_memwords * 4) _) in e.
    apply (inj_trans m tm _); auto.
    auto.
Qed.

Theorem transl_program_correct:
  forward_simulation (Seccompspec.semantics prog) (Cminorp.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step.
Qed.

End TRANSLATION.
