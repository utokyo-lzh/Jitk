Require Import compcert.backend.Cminor.  Require Import
compcert.common.AST.  Require Import compcert.common.Errors.  Require
Import compcert.lib.Coqlib.  Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.  Require Import Seccomp.  Import
ListNotations.

Definition seccomp_ends_with_ret (f: Seccomp.code) : bool :=
  match f with
  | [] => false
  | _ => true
  end &&
  let lastop := last f Sret_a in
  match lastop with
  | Sret_k k => true
  | Sret_a => true
  | _ => false
  end.

Fixpoint seccomp_inbound_jumps (f: Seccomp.code) : bool :=
  match f with
  | [] => true
  | op :: rest =>
    match op with
    | Sjmp_ja off =>
      Int.unsigned off <? list_length_z rest
    | Sjmp_jc cond jt jf =>
      (Byte.unsigned jt <? list_length_z rest) &&
      (Byte.unsigned jf <? list_length_z rest)
    | _ => true
    end &&
    seccomp_inbound_jumps rest
  end.

Definition seccomp_func_filter (f: Seccomp.code) : bool :=
  seccomp_ends_with_ret f &&
  seccomp_inbound_jumps f.

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

