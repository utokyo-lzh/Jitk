Require Import compcert.backend.RTL.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Op.
Require Import Seccomp.

Parameter seccomp_memwords: Z.

Inductive state: Type :=
  | empty_state: state
  | code_state:   (* pcmap maps Seccomp.v pc's to RTL.code ep's *)
    forall (code: RTL.code) (entry: node) (pcmap: PTree.t node), state.

Definition next_ep (s: state) :=
  match s with
  | empty_state => 1%positive
  | code_state _ ep _ => (Psucc ep)
  end.

Definition st_code (s: state) :=
  match s with
  | empty_state => PTree.empty RTL.instruction
  | code_state c _ _ => c
  end.

Definition st_map (s: state) :=
  match s with
  | empty_state => PTree.empty node
  | code_state _ _ m => m
  end.

Definition st_ep (s: state) : res node :=
  match s with
  | empty_state => Error (msg "No entry point for empty function")
  | code_state _ ep _ => OK ep
  end.

Definition add_instr (instr: RTL.instruction) (st: state)
                     (opc: option positive) : state :=
  let new_ep := next_ep st in
  let new_map := match opc with
    | None => st_map st
    | Some pc => (PTree.set pc new_ep (st_map st))
    end in
  code_state (PTree.set new_ep instr (st_code st)) new_ep new_map.

Definition reg_a:   ident := 1%positive.
Definition reg_x:   ident := 2%positive.
Definition reg_mem: ident := 3%positive.

Open Local Scope error_monad_scope.

Definition transl_instr (instr: Seccomp.instruction) (pc: positive)
                        (st: state) : res state :=
  match st, instr with
  | code_state _ ep _, Salu_add_k k =>
    OK (add_instr (Iop (Oaddimm k) (reg_a::nil) reg_a ep) st (Some pc))
  | _, Sret_a =>
    OK (add_instr (Ireturn (Some reg_a)) st (Some pc))
  | empty_state, _ => Error (msg "No trailing ret")
  | _, _ => Error (msg "FIXME")
  end.

Fixpoint transl_code (src: Seccomp.code) (pc: positive)
                     (st: state) : res state :=
  match src with
  | nil => OK st
  | hd::tl =>
    do st <- transl_code tl (Psucc pc) st;
    transl_instr hd pc st
  end.


Record fnmap: Type := mkfnmap {
  fn: RTL.function;
  map: PTree.t node
}.

Definition transl_function (f: Seccomp.function) : res fnmap :=
  do st <- transl_code f 1 empty_state;
  let sig := mksignature nil (Some Tint) in
  let stacksize := (Zmult seccomp_memwords 4) in
  (* FIXME: memset(mem, 0, sizeof(mem)) *)
  do ep <- st_ep st;
  let st := add_instr (Iop (Oaddrstack Int.zero) nil reg_mem ep) st None in
  do ep <- st_ep st;
  let st := add_instr (Iop (Ointconst Int.zero) nil reg_x ep) st None in
  do ep <- st_ep st;
  let st := add_instr (Iop (Ointconst Int.zero) nil reg_a ep) st None in
  do ep <- st_ep st;
  OK (mkfnmap (RTL.mkfunction sig nil stacksize (st_code st) ep)
              (st_map st)).

Local Open Scope string_scope.

Definition transl_fundef (fd: fundef) :=
  match fd with
  | Internal f => do f' <- transl_function f; OK (Internal f'.(fn))
  | External ef => Error (msg "no external function allowed")
  end.

Definition transl_program (p: Seccomp.program) : res RTL.program :=
  transform_partial_program transl_fundef p.
