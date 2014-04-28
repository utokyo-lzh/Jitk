Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import Seccomp.
Require Import Seccompconf.
Require Import Seccompenc.
Require Import HLspec.
Import ListNotations.

Section TRANSL.

Open Local Scope error_monad_scope.

Definition transl_rule (r: rule) : Seccomp.code :=
  [
    Sld_w_abs (Int.repr SECCOMP_NR_OFFSET);
    Sjmp_jc (Jeqimm r.(rl_syscall)) Byte.zero Byte.one;
    Sret_k (action_enc r.(rl_action))
  ].

Fixpoint transl_code (c: code) (f: function) : Seccomp.code :=
  match c with
  | nil => [ Sret_k (action_enc f.(fn_default)) ]
  | hd :: tl => (transl_rule hd) ++ (transl_code tl f)
  end.

Definition transl_function (f: function) : Seccomp.function :=
  transl_code f.(fn_body) f.

Definition transl_fundef (fd: fundef) :=
  match fd with
  | Internal f => OK (Internal (transl_function f))
  | External ef => Error (msg "no external function allowed")
  end.

Definition transl_program (p: program) : res Seccomp.program :=
  transform_partial_program transl_fundef p.

End TRANSL.
