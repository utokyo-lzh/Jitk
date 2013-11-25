Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Seccomp.

Record state: Type := mkstate {
  st_vars: list ident;
  st_body: stmt
}.

Parameter seccomp_memwords: Z.

Local Open Scope string_scope.
Definition id_a: ident := ident_of_string "A".
Definition id_x: ident := ident_of_string "X".
Definition id_mem: ident := ident_of_string "mem".

Fixpoint transf_code (src: Seccomp.code) (n: label) (st: state) : res state :=
  match src with
  | nil => OK st
  | hd::tl => match transf_code tl (Psucc n) st with
    | Error msg => Error msg
    | OK st =>
      let vars := st.(st_vars) in
      let body := st.(st_body) in
      match hd with
      | Salu_add_k k =>
        let body := Slabel n (Sseq (Sassign id_a (Ebinop Oadd (Evar id_a) (Econst (Ointconst k)))) body) in
        OK (mkstate vars body)
      | Sret_k k =>
        let body := Slabel n (Sseq (Sreturn (Some (Econst (Ointconst k)))) body) in
        OK (mkstate vars body)
      | Sret_a =>
        let body := Slabel n (Sseq (Sreturn (Some (Evar id_a))) body) in
        OK (mkstate vars body)
      | _ => Error (msg "FIXME")
      end
    end
  end.

Definition transf_function (f: Seccomp.function) : res Cminor.function :=
  let st := mkstate (id_a::id_x::id_mem::nil) Sskip in
  match transf_code f xH st with
  | Error msg => Error msg
  | OK st =>
    let sig := mksignature nil (Some Tint) in
    let vars := st.(st_vars) in
    let stackspace := Zmult seccomp_memwords 4 in
    let body := st.(st_body) in
    (* FIXME: memset(mem, 0, sizeof(mem)) *)
    let body := Sseq (Sassign id_mem (Econst (Oaddrstack Int.zero))) body in
    let body := Sseq (Sassign id_x (Econst (Ointconst Int.zero))) body in
    let body := Sseq (Sassign id_a (Econst (Ointconst Int.zero))) body in
    OK (Cminor.mkfunction sig nil vars stackspace body)
  end.

Definition transf_fundef (f: Seccomp.fundef) : res Cminor.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Seccomp.program) : res Cminor.program :=
  transform_partial_program transf_fundef p.
