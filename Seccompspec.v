Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import compcert.lib.Coqlib.
Require Import Seccomp.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
