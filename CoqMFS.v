Require Import Arith.
Require Import CpdtTactics.
Require Import FunctionalExtensionality.


Inductive diskblock :=
  | Data : nat -> diskblock.

Definition disk := nat -> diskblock.

Definition empty_disk : disk :=
  fun n => Data 0.

Definition disk_write (addr:nat) (val:nat) (d:disk) : disk :=
  fun n => if eq_nat_dec n addr then Data val else d n.

Definition disk_read (addr:nat) (d:disk) : nat :=
  match d addr with
  | Data n => n
  end.

Lemma disk_rw_same:
  forall a a' v d,
  a = a' ->
  (disk_read a (disk_write a' v d)) = v.
Proof.
  unfold disk_read; unfold disk_write.
  intros; destruct (eq_nat_dec a a'); crush.
Qed.

Lemma disk_rw_other:
  forall a a' v d,
  a <> a' ->
  (disk_read a (disk_write a' v d)) = disk_read a d.
Proof.
  unfold disk_read; unfold disk_write.
  intros; destruct (eq_nat_dec a a'); crush.
Qed.

Opaque disk.
Opaque disk_read.
Opaque disk_write.


Inductive fdisk :=
  | FlakyDisk : disk -> nat -> fdisk.

Definition fdisk_reset (fd:fdisk) (n:nat) :=
  match fd with
  | FlakyDisk d _ => FlakyDisk d n
  end.

Definition fdisk_write (addr:nat) (val:nat) (fd:fdisk) : option fdisk :=
  match fd with
  | FlakyDisk _ 0 => None
  | FlakyDisk d (S k) => Some (FlakyDisk (disk_write addr val d) k)
  end.

Definition fdisk_read (addr:nat) (fd:fdisk) : nat :=
  match fd with
  | FlakyDisk d _ => disk_read addr d 
  end.

Lemma fdisk_rw_same:
  forall a a' v fd fd',
  a = a' /\ fdisk_write a' v fd = Some fd' ->
  fdisk_read a fd' = v.
Proof.
  intros.
  destruct fd.
  destruct n; crush; apply disk_rw_same; auto.
Qed.

Lemma fdisk_rw_other:
  forall a a' v fd fd',
  a <> a' /\ fdisk_write a' v fd = Some fd' ->
  fdisk_read a fd' = fdisk_read a fd.
Proof.
  intros.
  destruct fd.
  destruct n; crush; apply disk_rw_other; auto.
Qed.

Lemma fdisk_crash:
  forall a v fd,
  fdisk_write a v fd = None ->
  forall a' v',
  fdisk_write a' v' fd = None.
Proof.
  intros; destruct fd; destruct n; crush.
Qed.


(* Monadic flaky disk *)
Definition mfdisk (R:Type) := fdisk -> (fdisk * option R).

Definition mret {R:Type} (x:R) : mfdisk R :=
  fun fd => (fd, Some x).

Definition mbind {A:Type} {B:Type} (a:mfdisk A) (f:A->mfdisk B) : mfdisk B :=
  fun fd =>
    match a fd with
    | (fd', Some av) => f av fd'
    | (fd', None) => (fd', None)
    end.

Definition mfdisk_write (addr:nat) (val:nat) : mfdisk unit :=
  fun fd =>
    match fdisk_write addr val fd with
    | None => (fd, None)
    | Some fd' => (fd', Some tt)
    end.

Definition mfdisk_read (addr:nat) : mfdisk nat :=
  fun fd =>
    (fd, Some (fdisk_read addr fd)).

Notation "'do' x <- y ; z" := (mbind y (fun x => z))
  (left associativity, at level 200, x ident, y at level 100, z at level 200).


Definition mfdisk_test_inc (addr:nat) : mfdisk unit :=
  do x <- mfdisk_read addr;
  do _ <- mfdisk_write addr (x+1);
  mret tt.

Lemma mfdisk_test_inc_works:
  forall fd fd' a,
  fd' = fst (mfdisk_test_inc a fd) ->
  (forall a', a <> a' -> fdisk_read a' fd' = fdisk_read a' fd) /\
  (fdisk_read a fd' = fdisk_read a fd \/
   fdisk_read a fd' = fdisk_read a fd + 1).
Proof.
  unfold mfdisk_test_inc; unfold mfdisk_read; unfold mfdisk_write.
  unfold mbind; unfold mret; unfold fdisk_write.
  intros.
  destruct fd.
  destruct n.
  - crush.
  - split.
    + crush; apply disk_rw_other; crush.
    + right; crush; apply disk_rw_same; crush.
Qed.



