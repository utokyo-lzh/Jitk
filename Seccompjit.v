Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.cfrontend.Clight.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Seccomp.

Parameter seccomp_memwords: Z.

Definition id_a:   ident := 1%positive.
Definition id_x:   ident := 2%positive.
Definition id_mem: ident := 3%positive.

Definition u32: type := Tint I32 Unsigned noattr.

Open Local Scope error_monad_scope.

Definition transl_instr (instr: Seccomp.instruction) (n: label) : res statement :=
  match instr with
  | Salu_add_k k =>
    OK (Sset id_a (Ebinop Oadd (Etempvar id_a u32) (Econst_int k u32) u32))
  | Sret_k k =>
    OK (Sreturn (Some (Econst_int k type_int32s)))
  | Sret_a =>
    OK (Sreturn (Some (Ecast (Etempvar id_a u32) type_int32s)))
  | _ => Error (msg "FIXME")
  end.

Fixpoint transl_code (src: Seccomp.code) (n: label) : res statement :=
  match src with
  | nil => OK Sskip
  | hd::tl =>
    do bodytl <- transl_code tl (Psucc n);
    do bodyhd <- transl_instr hd n;
    OK (Slabel n (Ssequence bodyhd bodytl))
  end.

Definition transl_function (f: Seccomp.function) : res Clight.function :=
  do body <- transl_code f xH;
  let vars := (id_mem, Tarray u32 seccomp_memwords noattr)::nil in
  let temps := (id_a, u32)::(id_x, u32)::nil in
  (* FIXME: memset(mem, 0, sizeof(mem)) *)
  let body := Ssequence (Sset id_x (Econst_int Int.zero u32)) body in
  let body := Ssequence (Sset id_a (Econst_int Int.zero u32)) body in
  OK (Clight.mkfunction type_int32s nil vars temps body).

Definition transl_fundef (fd: Seccomp.fundef) : res Clight.fundef :=
  match fd with
  | AST.Internal f => do tf <- transl_function f; OK (Clight.Internal tf)
  | _ => Error (msg "external function not allowed")
  end.

Local Open Scope string_scope.

Definition transl_program (p: Seccomp.program) : res Clight.program :=
  transform_partial_program transl_fundef p.
