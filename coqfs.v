Require Import Arith.
Require Import CpdtTactics.

Inductive diskblock :=
  | Data : forall (data:nat), diskblock
  | Log : forall (addr0:nat) (data0:nat) (addr1:nat) (data1:nat), diskblock
  | EmptyLog : diskblock.

Definition disk := nat -> diskblock.

Definition empty_disk : disk :=
  fun n => Data 0.

Definition disk_write (addr:nat) (val:diskblock) (d:disk) : disk :=
  fun n => if eq_nat_dec n addr then val else d n.

Definition disk_read (addr:nat) (d:disk) : diskblock :=
  d addr.


Inductive flaky_disk :=
  | FlakyDisk : disk -> nat -> flaky_disk
  | GoodDisk : disk -> flaky_disk.

Definition flaky_init (d:disk) (n:nat) := FlakyDisk d n.

Definition flaky_fix (fd:flaky_disk) : flaky_disk :=
  match fd with
  | FlakyDisk d _ => GoodDisk d
  | GoodDisk d => GoodDisk d
  end.

Definition flaky_write (addr:nat) (val:diskblock) (fd:flaky_disk) : flaky_disk :=
  match fd with
  | FlakyDisk _ 0 => fd
  | FlakyDisk d (S k) => FlakyDisk (disk_write addr val d) k
  | GoodDisk d => GoodDisk (disk_write addr val d)
  end.

Definition flaky_read (addr:nat) (fd:flaky_disk) : diskblock :=
  match fd with
  | FlakyDisk d _ => disk_read addr d
  | GoodDisk d => disk_read addr d
  end.


Definition inc (addr:nat) (fd:flaky_disk) : flaky_disk :=
  match flaky_read addr fd with
  | Data x => flaky_write addr (Data (x+1)) fd
  | _ => fd
  end.


Theorem inc_ok:
  forall fd fd' addr k,
  flaky_read addr fd = Data k /\ inc addr fd = fd' ->
  flaky_read addr fd = Data k \/ flaky_read addr fd = Data (k+1).
Proof.
  crush.
Qed.


Definition log_apply (fd:flaky_disk) : flaky_disk :=
  match flaky_read 0 fd with
  | Log a0 d0 a1 d1 =>
    flaky_write 0 EmptyLog (flaky_write a0 (Data d0) (flaky_write a1 (Data d1) fd))
  | _ => fd
  end.

Definition block_inc (b:diskblock) : nat :=
  match b with
  | Data x => x+1
  | _ => 0
  end.

Definition log_doubleinc (addr:nat) (fd:flaky_disk) : flaky_disk :=
  let fd0 := log_apply fd in
  let d0 := flaky_read (addr+1) fd0 in
  let d1 := flaky_read (addr+2) fd0 in
  let fd1 := flaky_write 0 (Log (addr+1) (block_inc d0)
                                (addr+2) (block_inc d1)) fd0 in
  log_apply fd1.

Definition log_read (addr:nat) (fd:flaky_disk) : nat :=
  let fd0 := log_apply fd in
  match flaky_read (S addr) fd0 with
  | Data x => x
  | _ => 0
  end.


Lemma disk_read_same:
  forall d a a' x,
  a = a' -> disk_read a (disk_write a' x d) = x.
Proof.
  intros; unfold disk_read; unfold disk_write.
  destruct (eq_nat_dec a a'); crush.
Qed.

Lemma disk_read_other:
  forall d a a' x,
  a <> a' -> disk_read a (disk_write a' x d) = disk_read a d.
Proof.
  intros; unfold disk_read; unfold disk_write.
  destruct (eq_nat_dec a a'); crush.
Qed.

(*
 * Sketchy heuristics for what is "same" and what is "other".
 * Can easily run into non-provable situations (e.g. applying
 * disk_read_other when the addresses are actually equal..)
 *)
Ltac rewrite_disk_ops :=
  simpl;
  repeat (rewrite disk_read_other with (a:=S _) (a':=0) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+1) (a':=0) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+2) (a':=0) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=0) (a':=S _) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=0) (a':=_+1) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=0) (a':=_+2) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=S (_+1)) (a':=_+2) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=S _) (a':=_+2) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=S (_+1)) (a':=_+1) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=_+1) (a':=_+1) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=_+2) (a':=_+2) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=0) (a':=0) in *; [idtac|crush]);
  repeat (rewrite disk_read_same with (a:=S _) (a':=_+1) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+1) (a':=_+2) in *; [idtac|crush]);
  repeat (rewrite disk_read_other with (a:=_+2) (a':=_+1) in *; [idtac|crush]).

Theorem doubleinc_init_nocrash:
  forall fd addr,
  log_doubleinc addr (flaky_fix (flaky_init empty_disk 0)) = fd ->
  log_read addr     fd = 1 /\
  log_read (addr+1) fd = 1.
Proof.
  intros.
  unfold log_doubleinc in H.
  unfold log_apply in H.
  unfold flaky_read in H.
  unfold log_read.
  unfold log_apply.
  rewrite <- H; clear H.

  repeat rewrite_disk_ops; auto.
Qed.

Theorem doubleinc_init_crash:
  forall n fd addr,
  log_doubleinc addr (flaky_init empty_disk n) = fd ->
  (log_read addr     (flaky_fix fd) = 0 /\
   log_read (addr+1) (flaky_fix fd) = 0) \/
  (log_read addr     (flaky_fix fd) = 1 /\
   log_read (addr+1) (flaky_fix fd) = 1).
Proof.
  intros.
  destruct (lt_dec n 1).

  (* crash before commit point *)
  left.  destruct n; crush.

  (* crash after commit point *)
  right.
  unfold log_doubleinc in H.
  unfold log_apply in H.
  unfold flaky_read in H.
  unfold log_read.
  unfold log_apply.
  rewrite <- H; clear H.
  simpl.

  destruct n.  crush.
  repeat rewrite_disk_ops.
  destruct n.
  repeat rewrite_disk_ops; auto.
  repeat rewrite_disk_ops.
  destruct n.
  repeat rewrite_disk_ops; auto.
  repeat rewrite_disk_ops.
  destruct n.
  repeat rewrite_disk_ops; auto.
  repeat rewrite_disk_ops; auto.
Qed.

