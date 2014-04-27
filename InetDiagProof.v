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

Admitted.

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
