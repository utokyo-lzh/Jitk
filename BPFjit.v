Require Import compcert.backend.RTL.
Require Import compcert.common.AST.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import BPF.

Definition Tpointer := Tint.

Definition transl_code (f: BPF.program) : RTL.code :=
  (* TODO *)
  PTree.empty RTL.instruction.

Definition transl_program (f: BPF.program) : RTL.program :=
  let sig := mksignature (Tpointer::nil) (Some Tint) in
  let c := transl_code f in
  let f := Internal (RTL.mkfunction sig (1%positive::nil) 64 c 1%positive) in
  mkprogram ((1%positive, Gfun f)::nil) 1%positive.
