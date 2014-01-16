Require Import CpdtTactics.
Require Import putget.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Events.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.

Definition putdef := Internal f_put.
Definition getdef := Internal f_get.

Section s.

  Variable ge: genv.
  Variable vput: Integers.Int.int.
  Variable vget: Integers.Int.int.
  Variable vputret: val.
  Variable m: Memory.Mem.mem.
  Variable m1: Memory.Mem.mem.
  Definition putcall := Callstate putdef (Vint vput :: nil)%list Kstop m.
  Definition putret := Returnstate vputret Kstop m1.

  Variable m2: Memory.Mem.mem.
  Definition getcall := Callstate getdef nil Kstop m1.
  Definition getret := Returnstate (Vint vget) Kstop m2.

  Theorem putget_ok:
    Smallstep.star step2 ge putcall E0 putret /\
    Smallstep.star step2 ge getcall E0 getret ->
    vput = vget.

(*
End s.
*)
