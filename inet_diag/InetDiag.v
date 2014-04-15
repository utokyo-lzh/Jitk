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
  | Loc n => eval p e
  end.
