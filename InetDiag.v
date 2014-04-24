Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import Cminorp.
Import ListNotations.

Definition port := int.

Inductive location : Type :=
  | Reject : location
  | Loc : nat -> location
  .

Record entry : Type := mkentry {
  saddr : int;
  daddr : int;
  sport : port;
  dport : port;
  family : int;
  userlocks : int
}.

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

Definition function := code.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.
Definition genv := Genv.t fundef unit.


(*
(* this probably needs something like GeneralRec in CPDT *)
Fixpoint eval (pgm: code) (e: entry) {struct pgm} : bool :=
  match pgm with
  | nil => true
  | Nop :: is => eval is e
  | Jmp loc :: is => jmp loc is e
  | Sge p loc :: is => if Int.cmpu Cge e.(sport) p then eval is e else jmp loc is e
  | Sle p loc :: is => if Int.cmpu Cle e.(sport) p then eval is e else jmp loc is e
  | Dge p loc :: is => if Int.cmpu Cge e.(dport) p then eval is e else jmp loc is e
  | Dle p loc :: is => if Int.cmpu Cle e.(dport) p then eval is e else jmp loc is e
  | Scond hc loc :: is => false (* XXX TODO *)
  | Dcond hc loc :: is => false
  end
with jmp (loc: location) (p: code) (e: entry) {struct p} : bool :=
  match loc with
  | Reject => false
  | Loc n => eval (skipn n p) e
  end.
*)

Definition checkhc (hc: hostcond) (e: entry) := false. (* XXX TODO *)

Inductive state : Type :=
  | State : code -> entry -> state
  | Returnstate : int -> state
  .

Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | ST_Accept : forall e,
    step ge (State nil e) E0 (Returnstate Int.one)
  | ST_Nop : forall r e,
    step ge (State (Nop :: r) e) E0 (State r e)
  | ST_Jmp_Reject : forall r e,
    step ge (State (Jmp Reject :: r) e) E0 (Returnstate Int.zero)
  | ST_Jmp_Loc : forall r e n,
    step ge (State (Jmp (Loc n) :: r) e) E0 (State (skipn n r) e)
  | ST_Sge : forall r e p n,
    let r' := if Int.cmpu Cge e.(sport) p then r else Jmp n :: r in
    step ge (State (Sge p n :: r) e) E0 (State r' e)
  | ST_Sle : forall r e p n,
    let r' := if Int.cmpu Cle e.(sport) p then r else Jmp n :: r in
    step ge (State (Sle p n :: r) e) E0 (State r' e)
  | ST_Dge : forall r e p n,
    let r' := if Int.cmpu Cge e.(dport) p then r else Jmp n :: r in
    step ge (State (Dge p n :: r) e) E0 (State r' e)
  | ST_Dle : forall r e p n,
    let r' := if Int.cmpu Cle e.(dport) p then r else Jmp n :: r in
    step ge (State (Dle p n :: r) e) E0 (State r' e)
  | ST_Scond : forall r e hc n,
    let r' := if checkhc hc e then r else Jmp n :: r in
    step ge (State (Scond hc n :: r) e) E0 (State r' e)
  | ST_Dcond : forall r e hc n,
    let r' := if checkhc hc e then r else Jmp n :: r in
    step ge (State (Dcond hc n :: r) e) E0 (State r' e)
  .

Parameter entry_input : entry.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b code m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some (Internal code) ->
    initial_state p (State code entry_input).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall v,
      final_state (Returnstate v) v.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

Definition reg_entry: ident := 1%positive.

Definition field : Type := (memory_chunk * Z)%type.

Definition e_saddr     : field := (Mint32, 0).
Definition e_daddr     : field := (Mint32, 4).
Definition e_sport     : field := (Mint16unsigned, 8).
Definition e_dport     : field := (Mint16unsigned, 10).
Definition e_family    : field := (Mint16unsigned, 12).
Definition e_userlocks : field := (Mint16unsigned, 14).

Definition load_field (f: field) : Cminor.expr :=
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
  let cond := Ebinop (Ocmpu (negate_comparison cmp)) (load_field f) (Econst (Ointconst p)) in
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

Fixpoint transl_code (c: code) (nextlbl: nat) : Cminor.stmt :=
  match c with
  | nil => Sreturn (Some (Econst (Ointconst Int.one)))
  | instr :: rest =>
    let hs := transl_instr instr nextlbl in
    let ts := transl_code rest (nextlbl - 1) in
    Sseq hs (Slabel (P_of_succ_nat nextlbl) ts)
  end.

Definition Tpointer := Tint. (* assume 32-bit pointers *)
Definition signature_main := mksignature [ Tpointer ] (Some Tint) cc_default.

Definition transl_function (f: function) : Cminor.function :=
  let body := transl_code f (length f) in
  let params := [ reg_entry ] in
  let vars := [] in
  let stackspace := 0 in
  Cminor.mkfunction signature_main params vars stackspace body.

Definition transl_fundef (fd: fundef) : res Cminor.fundef :=
  match fd with
  | Internal f => let f' :=  transl_function f in OK (Internal f')
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

Variable prog: program.
Variable tprog: Cminor.program.

Theorem transl_program_correct:
  forward_simulation (semantics prog) (Cminorp.semantics tprog).
Proof.
  eapply forward_simulation_plus.
Admitted.
