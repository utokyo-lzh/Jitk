Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.driver.Compiler.
Require Import compcert.arm.Asm.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import Seccompconf.

Require Cminorp.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0 m1 m2 bytes pkt,
      Genv.init_mem p = Some m0 ->
      list_length_z bytes = sizeof_seccomp_data ->
      Mem.alloc m0 0 sizeof_seccomp_data = (m1, pkt) ->
      Mem.storebytes m1 pkt 0 bytes = Some m2 ->
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Int.zero)
        # IR14 <- Vzero
        # IR13 <- Vzero
        # IR0 <- (Vptr pkt Int.zero) in
      initial_state p (State rs0 m2).

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
