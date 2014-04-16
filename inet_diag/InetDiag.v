Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

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

Definition program := list instruction.

(*
(* this probably needs something like GeneralRec in CPDT *)
Fixpoint eval (pgm: program) (e: entry) {struct pgm} : bool :=
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
with jmp (loc: location) (p: program) (e: entry) {struct p} : bool :=
  match loc with
  | Reject => false
  | Loc n => eval (skipn n p) e
  end.
*)

Definition checkhc (hc: hostcond) (e: entry) := false. (* XXX TODO *)

Inductive state : Type :=
  | State : program -> entry -> state
  | RejectState : state
  | AcceptState : state
  .

Inductive step : state -> state -> Prop :=
  | ST_Accept : forall e,
    step (State nil e) AcceptState
  | ST_Nop : forall r e,
    step (State (Nop :: r) e) (State r e)
  | ST_Jmp_Reject : forall r e,
    step (State (Jmp Reject :: r) e) RejectState
  | ST_Jmp_Loc : forall r e n,
    step (State (Jmp (Loc n) :: r) e) (State (skipn n r) e)
  | ST_Sge : forall r e p n,
    let r' := if Int.cmpu Cge e.(sport) p then r else Jmp n :: r in
    step (State (Sge p n :: r) e) (State r' e)
  | ST_Sle : forall r e p n,
    let r' := if Int.cmpu Cle e.(sport) p then r else Jmp n :: r in
    step (State (Sle p n :: r) e) (State r' e)
  | ST_Dge : forall r e p n,
    let r' := if Int.cmpu Cge e.(dport) p then r else Jmp n :: r in
    step (State (Dge p n :: r) e) (State r' e)
  | ST_Dle : forall r e p n,
    let r' := if Int.cmpu Cle e.(dport) p then r else Jmp n :: r in
    step (State (Dle p n :: r) e) (State r' e)
  | ST_Scond : forall r e hc n,
    let r' := if checkhc hc e then r else Jmp n :: r in
    step (State (Scond hc n :: r) e) (State r' e)
  | ST_Dcond : forall r e hc n,
    let r' := if checkhc hc e then r else Jmp n :: r in
    step (State (Dcond hc n :: r) e) (State r' e)
  .
