Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Seccomp.

Section SEMANTICS.

(** access struct seccomp_data *)
Variable seccomp_bpf_load : int -> int -> Prop.

(* Variable ge: genv. *)

End SEMANTICS.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
