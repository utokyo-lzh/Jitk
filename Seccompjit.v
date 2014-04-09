Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Seccomp.

Parameter seccomp_memwords: Z.

Definition reg_a:   ident := 1%positive.
Definition reg_x:   ident := 2%positive.
Definition reg_mem: ident := 3%positive.

Open Local Scope error_monad_scope.

Definition transl_instr (instr: Seccomp.instruction)
                        (nextlbl: Z) : res Cminor.stmt :=
  match instr with
  | Salu_add_k k =>
    OK (Sassign reg_a (Ebinop Oadd (Evar reg_a) (Econst (Ointconst k))))
  | Sjmp_ja k =>
    match nextlbl - (Int.unsigned k) with
    | Zpos p => OK (Sgoto p)
    | _ => Error (msg "Illegal offset")
    end
  | Sret_a =>
    OK (Sreturn (Some (Evar reg_a)))
  | _ => Error (msg "FIXME")
  end.

Fixpoint transl_code (c: Seccomp.code) : res Cminor.stmt :=
  match c with
  | nil => OK Sskip
  | hd::tl =>
    let n := length tl in
    do t <- transl_code tl;
    do h <- transl_instr hd (Z_of_nat (S n));
    OK (Sseq h (Slabel (P_of_succ_nat n) t))
  end.

Definition transl_funbody (f: Seccomp.function) : res Cminor.stmt :=
  do b <- transl_code f;
  (* FIXME: memset(mem, 0, sizeof(mem)) *)
  let init_a := (Sassign reg_a (Econst (Ointconst Int.zero))) in
  let init_x := (Sassign reg_x (Econst (Ointconst Int.zero))) in
  let init_mem := (Sassign reg_mem (Econst (Oaddrstack Int.zero))) in
  OK (Sseq init_a (Sseq init_x (Sseq init_mem b))).

Definition transl_function (f: Seccomp.function) : res Cminor.function :=
  do body <- transl_funbody f;
  let sig := mksignature nil (Some Tint) cc_default in
  let vars := reg_a::reg_x::reg_mem::nil in
  let stackspace := (Zmult seccomp_memwords 4) in
  OK (Cminor.mkfunction sig nil vars stackspace body).

Local Open Scope string_scope.

Definition transl_fundef (fd: fundef) :=
  match fd with
  | Internal f => do f' <- transl_function f; OK (Internal f')
  | External ef => Error (msg "no external function allowed")
  end.

Definition transl_program (p: Seccomp.program) : res Cminor.program :=
  transform_partial_program transl_fundef p.
