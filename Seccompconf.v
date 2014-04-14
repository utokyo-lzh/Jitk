Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Import ListNotations.

Parameter sizeof_seccomp_data : Z. (**r sizeof struct seccomp_data *)
Axiom sizeof_nonneg: 0 <= sizeof_seccomp_data.

Definition Tpointer := Tint. (* assume 32-bit pointers *)

Definition signature_main := mksignature [ Tpointer ] (Some Tint) cc_default.
