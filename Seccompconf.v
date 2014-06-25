Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Import ListNotations.

Parameter ident_of_string : String.string -> ident.

Parameter sizeof_seccomp_data : Z. (**r sizeof struct seccomp_data *)
Axiom sizeof_seccomp_data_pos: 0 < sizeof_seccomp_data.
Axiom sizeof_mul4: sizeof_seccomp_data mod 4 = 0.

Parameter seccomp_data : list byte.
Axiom length_seccomp_data : list_length_z seccomp_data = sizeof_seccomp_data.

Parameter seccomp_memwords : Z.
Axiom seccomp_memwords_range: 0 < seccomp_memwords <= 1024.

Definition Tpointer := Tint. (* assume 32-bit pointers *)

Definition signature_main := mksignature [ Tpointer ] (Some Tint) cc_default.
Definition signature_populate := mksignature nil (Some Tpointer) cc_default.

Local Open Scope string_scope.

Definition main_id := ident_of_string "seccomp_main".
Definition populate_id := ident_of_string "seccomp_populate".
