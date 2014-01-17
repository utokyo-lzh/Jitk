Require Import CpdtTactics.
Require Import putgetidx.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.

Definition putdef := Internal f_put.
Definition getdef := Internal f_get.

Section s.

  Variable ge: genv.
  Variable vidx: Integers.Int.int.
  Variable vput: Integers.Int.int.
  Variable vget: Integers.Int.int.
  Variable m: Memory.Mem.mem.
  Variable m1: Memory.Mem.mem.
  Definition putcall := Callstate putdef (Vint vidx :: Vint vput :: nil)%list Kstop m.
  Definition putret := Returnstate (Vint Integers.Int.zero) Kstop m1.

  Variable m2: Memory.Mem.mem.
  Definition getcall := Callstate getdef (Vint vidx :: nil)%list Kstop m1.
  Definition getret := Returnstate (Vint vget) Kstop m2.

  Theorem putget_ok:
    Smallstep.star step2 ge putcall E0 putret /\
    Smallstep.star step2 ge getcall E0 getret ->
    vput = vget.
  Proof.
    destruct 1.

    (* expand out all of the star steps *)
    repeat match goal with
      | [ H: _ = (if ?b then _ else _) |- _ ] => destruct b; crush
      | [ H: step2 ge _ _ _ |- _ ] => inv H
      | [ H: star step2 _ _ _ _ |- _ ] => inv H
    end;

    (* function args *)
    repeat match goal with
      | [ H: function_entry2 _ _ _ _ _ _ |- _ ] => inv H
    end; crush.

