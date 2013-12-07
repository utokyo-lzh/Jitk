Require Import compcert.backend.RTL.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Op.
Require Import Seccomp.

Parameter seccomp_memwords: Z.

Record state: Type := mkstate {
  st_code: RTL.code;
  st_ep: node;
  st_map: ZMap.t node
}.

Record fnmap: Type := mkfnmap {
  fn: RTL.function;
  map: ZMap.t node
}.

Inductive state_incr: state -> state -> Prop :=
  state_incr_intro:
    forall (s1 s2: state),
    Ple s1.(st_ep) s2.(st_ep) ->
    (forall pc,
      s1.(st_code)!pc = None \/ s2.(st_code)!pc = s1.(st_code)!pc) ->
    state_incr s1 s2.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros.
  apply state_incr_intro.
  apply Ple_refl.
  intros; auto.
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros.
  inv H; inv H0.
  apply state_incr_intro.
  apply Ple_trans with s2.(st_ep); assumption.

  intros.
  generalize (H2 pc) (H3 pc).
  intuition congruence.
Qed.

Definition add_instr (instr: RTL.instruction) (st: state) : state :=
  let n := Psucc st.(st_ep) in
  mkstate (PTree.set n instr st.(st_code)) n st.(st_map).

Definition add_map (pc: Z) (st: state) : state :=
  mkstate st.(st_code) st.(st_ep) (ZMap.set pc st.(st_ep) st.(st_map)).

Definition reg_a:   ident := 1%positive.
Definition reg_x:   ident := 2%positive.
Definition reg_mem: ident := 3%positive.

Open Local Scope error_monad_scope.

Definition transl_instr (instr: Seccomp.instruction) (pc: Z) (st: state) : res state :=
  match instr with
  | Salu_add_k k =>
    OK (add_instr (Iop (Oaddimm k) (reg_a::nil) reg_a st.(st_ep)) st)
  | Sret_a =>
    OK (add_instr (Ireturn (Some reg_a)) st)
  | _ => Error (msg "FIXME")
  end.

Fixpoint transl_code (src: Seccomp.code) (pc: Z) (st: state) : res state :=
  match src with
  | nil => OK st
  | hd::tl =>
    do st <- transl_code tl (Zsucc pc) st;
    do st <- transl_instr hd pc st;
    OK (add_map pc st)
  end.

Definition transl_function (f: Seccomp.function) : res fnmap :=
  let st := mkstate (PTree.empty RTL.instruction) 1%positive (ZMap.init 1%positive) in
  do st <- transl_code f 0 st;
  let sig := mksignature nil (Some Tint) in
  let stacksize := (Zmult seccomp_memwords 4) in
  (* FIXME: memset(mem, 0, sizeof(mem)) *)
  let st := add_instr (Iop (Oaddrstack Int.zero) nil reg_mem st.(st_ep)) st in
  let st := add_instr (Iop (Ointconst Int.zero) nil reg_x st.(st_ep)) st in
  let st := add_instr (Iop (Ointconst Int.zero) nil reg_a st.(st_ep)) st in
  OK (mkfnmap (RTL.mkfunction sig nil stacksize st.(st_code) st.(st_ep)) st.(st_map)).

Local Open Scope string_scope.

Definition transl_fundef (fd: fundef) :=
  match fd with
  | Internal f => do f' <- transl_function f; OK (Internal f'.(fn))
  | External ef => Error (msg "no external function allowed")
  end.

Definition transl_program (p: Seccomp.program) : res RTL.program :=
  transform_partial_program transl_fundef p.
