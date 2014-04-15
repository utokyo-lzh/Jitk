Require Import compcert.lib.Integers.
Require Import ZArith.
Require Import Seccomp.
Require Import List.
Import ListNotations.

Notation SECCOMP_NR_OFFSET := 0%Z.

Parameter SECCOMP_RET_ALLOW : Z.  (* 0x7fff0000 *)
Parameter SECCOMP_RET_ERRNO : Z.  (* 0x00050000 + errno *)
Parameter SECCOMP_RET_TRAP  : Z.  (* 0x00030000 *)
Parameter SECCOMP_RET_KILL  : Z.  (* 0 *)

Inductive hlspec_rule : Type :=
  | Allow: int -> hlspec_rule
  | Deny: int -> hlspec_rule
  .

Fixpoint hlspec_compile (l: list hlspec_rule) : Seccomp.code :=
  match l with
  | nil => [ Sret_k (Int.repr SECCOMP_RET_ALLOW) ]
  | Allow num :: rest =>
    [ Sld_w_abs (Int.repr SECCOMP_NR_OFFSET);
      Sjmp_jc (Jeqimm num) Byte.zero Byte.one;
      Sret_k (Int.repr SECCOMP_RET_ALLOW) ] ++ hlspec_compile rest
  | Deny num :: rest =>
    [ Sld_w_abs (Int.repr SECCOMP_NR_OFFSET);
      Sjmp_jc (Jeqimm num) Byte.zero Byte.one;
      Sret_k (Int.repr SECCOMP_RET_ERRNO) ] ++ hlspec_compile rest
  end.

Fixpoint semantics (l: list hlspec_rule) (sysnum: int) : bool :=
  match l with
  | nil => true
  | Allow num :: rest =>
    if (Int.eq num sysnum) then true else semantics rest sysnum
  | Deny num :: rest =>
    if (Int.eq num sysnum) then false else semantics rest sysnum
  end.

