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

Local Open Scope string_scope.
Definition id_a: ident := ident_of_string "A".
Definition id_x: ident := ident_of_string "X".
Definition id_mem: ident := ident_of_string "mem".
Definition u32: type := Tint I32 Unsigned noattr.

Fixpoint transf_code (src: Seccomp.code) (n: label) : res statement :=
  match src with
  | nil => OK Sskip
  | hd::tl => match transf_code tl (Psucc n) with
    | Error msg => Error msg
    | OK bodytl =>
      match (match hd with
      | Salu_add_k k =>
        OK (Sset id_a (Ebinop Oadd (Etempvar id_a u32) (Econst_int k u32) u32))
      | Sret_k k =>
        OK (Sreturn (Some (Econst_int k u32)))
      | Sret_a =>
        OK (Sreturn (Some (Etempvar id_a u32)))
      | _ => Error (msg "FIXME")
      end) with
      | Error msg => Error msg
      | OK bodyhd => OK (Slabel n (Ssequence bodyhd bodytl))
      end
    end
  end.

Definition transf_function (f: Seccomp.function) : res Clight.function :=
  match transf_code f xH with
  | Error msg => Error msg
  | OK body =>
    let vars := (id_mem, Tarray u32 seccomp_memwords noattr)::nil in
    let temps := (id_a, u32)::(id_x, u32)::nil in
    (* FIXME: memset(mem, 0, sizeof(mem)) *)
    let body := Ssequence (Sset id_x (Econst_int Int.zero u32)) body in
    let body := Ssequence (Sset id_a (Econst_int Int.zero u32)) body in
    OK (Clight.mkfunction u32 nil vars temps body)
  end.

Open Local Scope error_monad_scope.

Definition transf_fundef (fd: Seccomp.fundef) : res Clight.fundef :=
  match fd with
  | AST.Internal f => do f' <- transf_function f; OK (Clight.Internal f')
  | _ => Error (msg "external function not allowed")
  end.

Definition transf_program (p: Seccomp.program) : res Clight.program :=
  let transf_var := fun v => Error (msg "global variable not allowed") in
  transform_partial_program2 transf_fundef transf_var p.
