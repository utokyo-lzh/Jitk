Require Export compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Export Seccompconf.
Import ListNotations.

Inductive initial_state (p: Cminor.program): Cminor.state -> Prop :=
  | initial_state_intro: forall b f m0 m1 m2 pkt,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      Mem.alloc m0 0 sizeof_seccomp_data = (m1, pkt) ->
      Mem.storebytes m1 pkt 0 (Memdata.inj_bytes seccomp_data) = Some m2 ->
      initial_state p (Callstate f [ Vptr pkt Int.zero ] Kstop m2).

Definition semantics (p: Cminor.program) :=
  Semantics Cminor.step (initial_state p) Cminor.final_state (Genv.globalenv p).
