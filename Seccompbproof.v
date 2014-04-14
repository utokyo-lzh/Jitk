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
Require Import Seccomp.
Require Import Seccompspec.
Require Import Seccompfilter.
Require Import MiscLemmas.
Require Import CpdtTactics.

Lemma list_length_z_exists:
  forall A:Type,
  forall z,
  exists l:list A,
  list_length_z l = z.
Proof.
  (* XXX *)
Admitted.

(* CPDT GeneralRec *)
Definition length_order (A:Type) (ls1 ls2: list A) :=
  (length ls1 < length ls2)%nat.

Hint Constructors Acc.

Lemma length_order_wf':
  forall A, forall len, forall ls,
  (length ls <= len -> Acc (length_order A) ls)%nat.
Proof.
  unfold length_order; induction len; crush.
Qed.

Lemma length_order_wf:
  forall A, well_founded (length_order A).
Proof.
  intro; red; intro; eapply length_order_wf'; eauto.
Qed.

Lemma seccomp_func_filter_skipn:
  forall c n,
  true = seccomp_func_filter c ->
  true = seccomp_func_filter (skipn n c).
Proof.
  admit.
(*
  induction n.
  - crush.
  - intros.
    cut (true = seccomp_func_filter (skipn n c)); [ idtac | crush ].
    intros.
    simpl.
*)
Qed.

Theorem step_terminates:
  forall ge f x sm p m c a,
  true = seccomp_func_filter c ->
  exists r,
  star step ge (State a x sm f c p m) Events.E0 (Returnstate r m).
Proof.
  induction c using (well_founded_ind (length_order_wf instruction)).
  destruct x0.
  crush.
  intros.
  destruct i; simpl in H0;
    repeat (case (Bool.andb_true_eq _ _ H0); clear H0; intros);
    crush.

  - destruct H with (y:=x0) (a:=(eval_alu_safe a0 a x)); unfold length_order; crush.
    econstructor.
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply H1.

  - destruct H with (y:=x0) (a:=(eval_alu_div a0 a x)); unfold length_order; crush.
    econstructor.
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply H1.

  - destruct H with (y:=x0) (a:=(eval_alu_shift a0 a x)); unfold length_order; crush.
    econstructor.
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply H1.

  -
(*
  destruct (Mem.valid_access_load m Mint32 p (Int.unsigned i)).
  admit.  (*XXX*)
  econstructor.  eapply star_step.  constructor.
  apply Zlt_is_lt_bool; auto.
  apply Z.eqb_eq; auto.
  apply H2.
  *)
    admit.

  - destruct H with (y:=(skipn (nat_of_Z (Int.unsigned i)) x0)) (a:=a).
    unfold length_order.  simpl.  apply Lt.le_lt_n_Sm.  apply length_skipn.
    apply seccomp_func_filter_skipn; auto.
    econstructor.
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply Zlt_is_lt_bool; auto.
    apply H2.

  - destruct H with (y:=(skipn (nat_of_Z (Byte.unsigned i)) x0)) (a:=a).
    unfold length_order.  simpl.  apply Lt.le_lt_n_Sm.  apply length_skipn.
    apply seccomp_func_filter_skipn; auto.
    destruct H with (y:=(skipn (nat_of_Z (Byte.unsigned i0)) x0)) (a:=a).
    unfold length_order.  simpl.  apply Lt.le_lt_n_Sm.  apply length_skipn.
    apply seccomp_func_filter_skipn; auto.
    case_eq (eval_cond c a x); intros.
    + econstructor.
      eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
      apply Zlt_is_lt_bool; crush.
      rewrite H5.  apply H3.
    + econstructor.
      eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
      apply Zlt_is_lt_bool; crush.
      rewrite H5.  apply H4.

  - econstructor.
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply star_refl.

  - econstructor.
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0); [ constructor | idtac | auto ].
    apply star_refl.
Qed.

Theorem seccomp_terminates:
  forall prog,
  true = seccomp_filter prog ->
  exists r,
  program_behaves (Seccompspec.semantics prog) (Terminates Events.E0 r).
Proof.
  intros.
  destruct prog.
  destruct prog_defs; crush.
  destruct p.
  destruct g; [ idtac | crush ].
  destruct f; crush.
  destruct prog_defs ; [ idtac | crush ].

  unfold seccomp_filter in H.  simpl in H.
  destruct (Bool.andb_true_eq _ _ H); auto.
  clear H.
  cut (i=prog_main); [ intros; inv H | apply Peqb_true_eq; auto ].
  clear H0.

  (* introduce some symbols early on, to help with existential variables *)
  case_eq (Mem.alloc Mem.empty 0 1); intros.
  destruct (Mem.range_perm_drop_2 m b 0 1 Nonempty); unfold Mem.range_perm; intros.
  apply (Mem.perm_alloc_2 Mem.empty 0 1); auto.

  destruct (list_length_z_exists memval Seccompconf.sizeof_seccomp_data).
  case_eq (Mem.alloc x 0 Seccompconf.sizeof_seccomp_data); intros.
  destruct (Mem.range_perm_storebytes m0 b0 0 x0).
  rewrite <- list_length_nat_z; rewrite H0; simpl.
  unfold Mem.range_perm; intros.
  destruct (Mem.valid_access_freeable_any m0 Mint8unsigned b0 ofs Writable).
  unfold Mem.valid_access.  split.
  unfold Mem.range_perm; intros.
  apply (Mem.perm_alloc_2 x 0 Seccompconf.sizeof_seccomp_data); auto.
  crush.  crush.  unfold Mem.range_perm in H4.  apply H4.  crush.

  destruct (step_terminates
    (Genv.globalenv {|
       prog_defs := (prog_main, Gfun (Internal f)) :: nil;
       prog_main := prog_main |})
    f Int.zero (ZMap.init Int.zero) b0 x1 f Int.zero); auto.

  (* split program_behaves into initial_state and state_behaves *)
  econstructor.
  econstructor.

  (* initial_state *)
  - econstructor.
    + unfold Genv.init_mem.
      simpl.  rewrite H.  rewrite e.  auto.
    + unfold Genv.find_symbol.  simpl.  apply PTree.gss.
    + unfold Genv.find_funct_ptr.  simpl.  auto.
    + exact H0.
    + exact H2.
    + exact e0.

  (* state_behaves *)
  - econstructor; simpl; [ idtac | constructor ].
    instantiate (1:=x1).
    eapply star_step with (t1:=Events.E0) (t2:=Events.E0);
      [ constructor | idtac | auto ].
    apply H3.
Qed.

Theorem transl_terminates:
  forall prog tprog,
  Seccompfilter.transl_program_filter prog = OK tprog ->
  exists t r,
  program_behaves (Cminor.semantics tprog) (Terminates t r).
Proof.
  intros.
  unfold transl_program_filter in H.
  case_eq (seccomp_filter prog); intros; rewrite H0 in H; [ idtac | crush ].
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
