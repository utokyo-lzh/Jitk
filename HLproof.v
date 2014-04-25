Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import CpdtTactics.
Require Import HLspec.
Require Import MiscLemmas.
Require Import Seccompconf.
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

Lemma function_ptr_translated:
  forall (b: block) (fd: HLspec.fundef),
  Genv.find_funct_ptr ge b = Some fd ->
  exists tfd, Genv.find_funct_ptr tge b = Some tfd /\ transl_fundef fd = OK tfd.
Proof.
  exact (Genv.find_funct_ptr_transf_partial _ _ TRANSL).
Qed.

Definition match_packet (m1: mem) (b1: block) (m2: mem) (b2: block) : Prop :=
  Mem.load Mint32 m1 b1 0 = Mem.load Mint32 m2 b2 0.

Inductive match_states: HLspec.state -> Seccomp.state -> Prop :=
  | match_state:
    forall f c p m ta tx tsm tf tc tp tm m1
      (MP: match_packet m p tm tp)
      (TF: HLspec.transl_function f = tf)
      (TC: HLspec.transl_code c f = tc)
      (TAIL: is_tail c f.(fn_body))
      (MINJ: mem_inj m tm)
      (MSTORE: Mem.storebytes m1 p 0 (Memdata.inj_bytes seccomp_data) = Some m),
      match_states (HLspec.State f c p m)
                   (Seccomp.State ta tx tsm tf tc tp tm)
  | match_callstate:
    forall fd p m tfd tp tm m1
      (MP: match_packet m p tm tp)
      (TF: HLspec.transl_fundef fd = OK tfd)
      (MINJ: mem_inj m tm)
      (MSTORE: Mem.storebytes m1 p 0 (Memdata.inj_bytes seccomp_data) = Some m),
      match_states (HLspec.Callstate fd p m)
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
  induction 1.
  exploit function_ptr_translated; eauto.
  intros (tf, (A, B)).

  econstructor; split.

  (* initial_state tprog R *)
  - econstructor.
    + apply (Genv.init_mem_transf_partial _ _ TRANSL); eauto.
    + rewrite (transform_partial_program_main _ _ TRANSL).
      fold tge.
      rewrite symbols_preserved.
      eauto.
    + eexact A.
    + eexact H2.
    + eexact H3.

  (* match states S R *)
  - apply match_callstate with (m1:=m1); auto.
    constructor.
    apply inj_refl.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> HLspec.final_state S r -> Seccomp.final_state R r.
Proof.
  intros.
  inv H0.
  inv H.
  constructor.
Qed.

Lemma transl_step:
  forall S1 t S2, HLspec.step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2, plus Seccomp.step tge R1 t R2 /\ match_states S2 R2.
Proof.
  induction 1; intros R1 MST; inversion MST.

  (* exec_rule *)
  - inv TC.
    econstructor; split.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ];
    try rewrite Int.unsigned_repr_eq ; try rewrite Zmod_0_l; auto.

    exact sizeof_seccomp_data_pos.
    crush.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    destruct b;
    destruct (Seccomp.eval_cond (Seccomp.Jeqimm (rl_syscall r)) (rl_syscall r) tx);
    rewrite list_length_nat_z; unfold Byte.zero; unfold Byte.one;
    auto; admit.

    case_eq (Seccomp.eval_cond (Seccomp.Jeqimm (rl_syscall r)) (rl_syscall r) tx); intros.
    rewrite Byte.unsigned_zero; simpl.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    eapply star_refl.

    unfold Seccomp.eval_cond in H0.
    rewrite Int.eq_true in H0.
    crush.

    constructor.  auto.  auto.

  (* exec_skip *)
  - inv TC.
    econstructor; split.

    assert (Mem.load Mint32 m p 0 = Some (Vint (Int.repr (decode_int (firstn 4 seccomp_data))))).

    destruct (Mem.storebytes_split m1 p 0 (firstn 4 (inj_bytes seccomp_data))
                                          (skipn 4 (inj_bytes seccomp_data)) m);
    [ rewrite firstn_skipn; auto | destruct H0 ].
    rewrite (Mem.load_storebytes_other x p _ _ _ H1).
    rewrite (Mem.load_store_same Mint32 m1 _ _ (Vint (Int.repr (decode_int (firstn 4 seccomp_data))))).
    crush.
    apply Mem.storebytes_store.
    unfold encode_val.
    rewrite decode_encode_int_4.  rewrite <- firstn_inj_bytes.  auto.
    admit.
    crush.
    right.  left.  admit.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ];
    try rewrite Int.unsigned_repr_eq ; try rewrite Zmod_0_l; auto.

    exact sizeof_seccomp_data_pos.
    rewrite <- MP.
    exact H0.

    unfold eval_rule in H.
    rewrite H0 in H.
    case_eq (Seccomp.eval_cond (Seccomp.Jeqimm (rl_syscall r)) (Int.repr (decode_int (firstn 4 seccomp_data))) tx);
    intros.
    unfold Seccomp.eval_cond in H1.
    generalize (Int.eq_spec (Int.repr (decode_int (firstn 4 seccomp_data))) (rl_syscall r)).
    rewrite H1.
    intros.
    crush.

    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    rewrite H1.
    admit.
    rewrite H1.
    apply star_refl.

    apply match_state with (m1:=m1); auto.
    admit.

  (* exec_default *)
  - inv TC.
    econstructor; split.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply star_refl.
    apply match_returnstate; auto.

  (* exec_call *)
  - inv TF.
    econstructor; split.

    eapply plus_left with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply star_refl.
    apply match_state with (m1:=m1); auto.
    crush.
Qed.

Theorem transl_program_correct:
  forward_simulation (semantics prog) (Seccompspec.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step.
Qed.
