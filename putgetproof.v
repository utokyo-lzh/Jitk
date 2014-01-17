Require Import CpdtTactics.
Require Import putget.
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
  Proof.
    destruct 1.

    (* expand out all of the steps *)
    repeat match goal with
      | [ H: step2 ge _ _ _ |- _ ] => inv H
      | [ H: star step2 _ _ _ _ |- _ ] => inv H
      | [ H: function_entry2 _ _ _ _ _ _ |- _ ] => inv H
    end; crush.

    (* expand out expression evaluation *)
    repeat match goal with
      | [ H: Cop.sem_cast _ _ _ = Some _ |- _ ] => unfold Cop.sem_cast in H
      | [ H: alloc_variables _ _ _ _ _ |- _ ] => inv H
      | [ H: eval_expr _ _ _ _ _ _ |- _ ] => inv H
      | [ H: assign_loc _ _ _ _ _ _ |- _ ] => inv H
      | [ H: eval_lvalue _ _ _ _ _ _ _ |- _ ] => inv H; crush
        (* crush needed to kill some dead-end goals *)
      | [ H: deref_loc _ _ _ _ _ |- _ ] => inv H; crush
        (* crush needed to kill some dead-end goals *)
    end; crush.

    (* all _v's are in the same place *)
    match goal with
      | [ H: Globalenvs.Genv.find_symbol ge _v = Some _ |- _ ] =>
        rewrite H in *
    end; crush.

    (* match the memory store and load *)
    match goal with
      | [ H: Mem.store _ _ _ _ _ = Some _ |- _ ] =>
        apply Mem.load_store_same in H
    end.

    match goal with
      | [ H: Mem.load _ _ _ _ = Some _ |- _ ] => rewrite H in *
    end.

    crush.
  Qed.

End s.
