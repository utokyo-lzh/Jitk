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
Require Import CpdtTactics.
Require Import MiscLemmas.
Import ListNotations.

Definition port := int.

Inductive location : Type :=
  | Reject : location
  | Loc : nat -> location
  .

Record hostcond : Type := mkhostcond {
  hcfamily : int;
  hcprefixlen : int;
  hcport : port;
  hcaddr : int
}.

Inductive instruction : Type :=
  | Nop : instruction
  | Jmp : location -> instruction
  | Sge : port -> location -> instruction
  | Sle : port -> location -> instruction
  | Dge : port -> location -> instruction
  | Dle : port -> location -> instruction
  | Scond : hostcond -> location -> instruction
  | Dcond : hostcond -> location -> instruction
  .

Definition code := list instruction.

Section SEMANTICS.

Definition function := code.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.
Definition genv := Genv.t fundef unit.

Definition checkhc (hc: hostcond) (e: block) := false. (* XXX TODO *)

Inductive state : Type :=
  | State:
    forall (c: code)             (**r current program point *)
           (f: function)         (**r current function *)
           (e: block)            (**r input entry *)
           (m: mem),             (**r memory state *)
    state
  | Callstate:
    forall (fd: fundef)          (**r calling function *)
           (e: block)            (**r input entry *)
           (m: mem),             (**r memory state *)
    state
  | Returnstate:
    forall (v: int)              (**r local return value *)
           (m: mem),             (**r memory state *)
    state
  .

Definition field : Type := (memory_chunk * Z)%type.

Definition e_saddr     : field := (Mint32, 0).
Definition e_daddr     : field := (Mint32, 4).
Definition e_sport     : field := (Mint16unsigned, 8).
Definition e_dport     : field := (Mint16unsigned, 10).
Definition e_family    : field := (Mint16unsigned, 12).
Definition e_userlocks : field := (Mint16unsigned, 14).

Definition load_field (f: field) (e: block) (m: mem) : option val :=
  match f with
  | (mc, ofs) => Mem.load mc m e ofs
  end.

Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | ST_Accept : forall f e m,
    step ge (State nil f e m) E0 (Returnstate Int.one m)
  | ST_Nop : forall r f e m,
    step ge (State (Nop :: r) f e m) E0 (State r f e m)
  | ST_Jmp_Reject : forall r f e m,
    step ge (State (Jmp Reject :: r) f e m) E0 (Returnstate Int.zero m)
  | ST_Jmp_Loc : forall r f e m n,
    step ge (State (Jmp (Loc n) :: r) f e m) E0 (State (skipn n r) f e m)
  | ST_Sge : forall r f e m p sp n,
    load_field e_sport e m = Some (Vint sp) ->
    let r' := if Int.cmpu Cge sp p then r else Jmp n :: r in
    step ge (State (Sge p n :: r) f e m) E0 (State r' f e m)
  | ST_Sle : forall r f e m p sp n,
    load_field e_sport e m = Some (Vint sp) ->
    let r' := if Int.cmpu Cle sp p then r else Jmp n :: r in
    step ge (State (Sle p n :: r) f e m) E0 (State r' f e m)
  | ST_Dge : forall r f e m p dp n,
    load_field e_dport e m = Some (Vint dp) ->
    let r' := if Int.cmpu Cge dp p then r else Jmp n :: r in
    step ge (State (Dge p n :: r) f e m) E0 (State r' f e m)
  | ST_Dle : forall r f e m p dp n,
    load_field e_dport e m = Some (Vint dp) ->
    let r' := if Int.cmpu Cle dp p then r else Jmp n :: r in
    step ge (State (Dle p n :: r) f e m) E0 (State r' f e m)
  | ST_Scond : forall r f e m hc n,
    let r' := if checkhc hc e then r else Jmp n :: r in
    step ge (State (Scond hc n :: r) f e m) E0 (State r' f e m)
  | ST_Dcond : forall r f e m hc n,
    let r' := if checkhc hc e then r else Jmp n :: r in
    step ge (State (Dcond hc n :: r) f e m) E0 (State r' f e m)
  .

Parameter entry_input : list byte.
Definition sizeof_entry := 16.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b fd m0 m1 m2 pkt,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some fd ->
    Mem.alloc m0 0 sizeof_entry = (m1, pkt) ->
    Mem.storebytes m1 pkt 0 (Memdata.inj_bytes entry_input) = Some m2 ->
    initial_state p (Callstate fd pkt m2).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall v m,
      final_state (Returnstate v m) v.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

End SEMANTICS.

(* jit translator *)

Open Local Scope error_monad_scope.

Definition reg_entry: ident := 1%positive.

Definition transl_load_field (f: field) : Cminor.expr :=
  match f with
  | (ty, offset) =>
    let addr := Ebinop Oadd (Evar reg_entry) (Econst (Ointconst (Int.repr offset))) in
    Eload ty addr
  end.

Definition transl_jmp (loc: location) (nextlbl: nat) : Cminor.stmt :=
  match loc with
  | Reject => Sreturn (Some (Econst (Ointconst Int.zero)))
  | Loc n => Sgoto (P_of_succ_nat (nextlbl - n))
  end.

Definition transl_cmp (cmp: comparison) (f: field) (p: port) (loc: location) (nextlbl: nat) : Cminor.stmt :=
  let cond := Ebinop (Ocmpu (negate_comparison cmp)) (transl_load_field f) (Econst (Ointconst p)) in
  Sifthenelse cond (transl_jmp loc nextlbl) Sskip.

Definition transl_instr (instr: instruction) (nextlbl: nat) : Cminor.stmt :=
  match instr with
  | Nop => Sskip
  | Jmp loc => transl_jmp loc nextlbl
  | Sge p loc => transl_cmp Cge e_sport p loc nextlbl
  | Sle p loc => transl_cmp Cle e_sport p loc nextlbl
  | Dge p loc => transl_cmp Cge e_dport p loc nextlbl
  | Dle p loc => transl_cmp Cle e_dport p loc nextlbl
  | _ => Sskip (* TODO *)
  end.

Fixpoint transl_code (c: code) : res Cminor.stmt :=
  match c with
  | nil => OK (Sreturn (Some (Econst (Ointconst Int.one))))
  | instr :: rest =>
    let n := length rest in
    do ts <- transl_code rest;
    let hs := transl_instr instr (S n) in
    OK (Sseq hs (Slabel (P_of_succ_nat n) ts))
  end.

Definition Tpointer := Tint. (* assume 32-bit pointers *)
Definition signature_main := mksignature [ Tpointer ] (Some Tint) cc_default.

Definition transl_function (f: function) : res Cminor.function :=
  do body <- transl_code f;
  let params := [ reg_entry ] in
  let vars := [] in
  let stackspace := 0 in
  OK (Cminor.mkfunction signature_main params vars stackspace body).

Definition transl_fundef (fd: fundef) : res Cminor.fundef :=
  match fd with
  | Internal f => do f' <- transl_function f; OK (Internal f')
  | External f => Error (msg "no external function allowed")
  end.

Definition transl_program (p: program) : res Cminor.program :=
  transform_partial_program transl_fundef p.

Definition example1 :=
  [ Sge (Int.repr 21) Reject
  ; Sge (Int.repr 1024) (Loc 1)
  ; Jmp Reject
  ; Nop
  ].

(* equivalence proof *)

Section TRANSLATION.

Variable prog: program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

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
