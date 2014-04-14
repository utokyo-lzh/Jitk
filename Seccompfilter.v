Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Seccomp.
Require Import Seccompjit.
Import ListNotations.

Fixpoint seccomp_func_filter (f: Seccomp.code) : bool :=
  match f with
  | [] => false   (* no return *)
  | [ Sret_k k ] => true
  | [ Sret_a ] => true
  | Sjmp_ja off :: rest =>
    (Int.unsigned off <? list_length_z rest) &&
    (seccomp_func_filter rest)
  | Sjmp_jc cond jt jf :: rest =>
    (Byte.unsigned jt <? list_length_z rest) &&
    (Byte.unsigned jf <? list_length_z rest) &&
    (seccomp_func_filter rest)
  | _ :: rest =>
    seccomp_func_filter rest
  end.

Definition seccomp_filter (p: Seccomp.program) : bool :=
  let defs := p.(prog_defs) in
  let main := p.(prog_main) in
  match defs with
  (* Just one identifier *)
  | [ (id, Gfun (Internal f)) ] =>
    (id =? main)%positive &&
    seccomp_func_filter f
  | _ => false
  end.

Definition transl_program_filter (p: Seccomp.program) : res Cminor.program :=
  match seccomp_filter p with
  | true  => transl_program p
  | false => Error (msg "filter reject")
  end.

