Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Import ListNotations.


Parameter entry_input : list byte.
Definition sizeof_entry := 16.

Definition Tpointer := Tint. (* assume 32-bit pointers *)

Definition signature_main := mksignature [ Tpointer ] (Some Tint) cc_default.

