Require Import compcert.common.Errors.
Require Import compcert.common.Memdata.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import Seccomp.
Require Import Seccompenc.
Require Import CpdtTactics.
Import List.ListNotations.

Lemma encode_decode_inst:
  forall i e,
  encode_inst i = OK e -> decode_inst e = OK i.
Proof.
  induction i; crush; try destruct a; try destruct c; crush.
Qed.

Lemma length_1:
  forall A:Type,
  forall l:list A,
  length l = 1%nat ->
  exists a:A, l = a :: nil.
Proof.
  intros.
  destruct l; crush.
  destruct l; crush.
  exists a; auto.
Qed.

Lemma length_2:
  forall A:Type,
  forall l:list A,
  length l = 2%nat ->
  exists a b:A, l = a :: b :: nil.
Proof.
  intros.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  exists a; exists a0; auto.
Qed.

Lemma length_4:
  forall A:Type,
  forall l:list A,
  length l = 4%nat ->
  exists a b c d:A, l = a :: b :: c :: d :: nil.
Proof.
  intros.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  exists a; exists a0; exists a1; exists a2; auto.
Qed.

Lemma length_8:
  forall A:Type,
  forall l:list A,
  length l = 8%nat ->
  exists a b c d e f g h:A, l = [a;b;c;d;e;f;g;h].
Proof.
  intros.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  destruct l; crush.
  exists a; exists a0; exists a1; exists a2; exists a3;
    exists a4; exists a5; exists a6; auto.
Qed.

Lemma encode_bytes_length:
  forall e l,
  encode_bytes e = OK l -> length l = 8%nat.
Proof.
  intros.
  monadInv H.
  repeat rewrite app_length.
  repeat rewrite encode_int_length.
  auto.
Qed.

(* From http://compcert.inria.fr/doc/html/Memdata.html *)
Lemma decode_encode_int_1':
  forall x, Byte.repr (decode_int (encode_int 1 (Byte.unsigned x))) = x.
Proof.
  intros. rewrite decode_encode_int. transitivity (Byte.repr (Byte.unsigned x)).
  decEq. apply Zmod_small. apply Byte.unsigned_range. apply Byte.repr_unsigned.
Qed.

Lemma decode_encode_int_2':
  forall x, Short.repr (decode_int (encode_int 2 (Short.unsigned x))) = x.
Proof.
  intros. rewrite decode_encode_int. transitivity (Short.repr (Short.unsigned x)).
  decEq. apply Zmod_small. apply Short.unsigned_range. apply Short.repr_unsigned.
Qed.

Lemma encode_decode_bytes:
  forall e l,
  encode_bytes e = OK l -> decode_bytes l = OK e.
Proof.
  destruct e.
  intros.
  monadInv H.
  destruct (length_2 byte (encode_int 2 (Short.unsigned enc_code)) (encode_int_length _ _)).
  destruct (length_1 byte (encode_int 1 (Byte.unsigned enc_jt)) (encode_int_length _ _)).
  destruct (length_1 byte (encode_int 1 (Byte.unsigned enc_jf)) (encode_int_length _ _)).
  destruct (length_4 byte (encode_int 4 (Int.unsigned enc_k)) (encode_int_length _ _)).
  destruct H.
  destruct H2; destruct H2; destruct H2.
  rewrite H; rewrite H0; rewrite H1; rewrite H2; simpl.
  rewrite <- H; rewrite <- H0; rewrite <- H1; rewrite <- H2.
  rewrite decode_encode_int_2'.
  rewrite decode_encode_int_1'.
  rewrite decode_encode_int_1'.
  rewrite decode_encode_int_4.
  auto.
Qed.

(* This is so that "monadInv H" below doesn't unfold encode_bytes *)
Opaque encode_bytes.
Opaque decode_bytes.

Theorem seccomp_encode_decode:
  forall c l,
  seccomp_encode c = OK l -> seccomp_decode l = OK c.
Proof.
  induction c.
  - crush.
  - intros.
    monadInv H.
    destruct (length_8 byte x0 (encode_bytes_length _ _ EQ1)).
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    destruct H.
    rewrite H; simpl.
    rewrite (encode_decode_bytes x); simpl.
    rewrite (encode_decode_inst a); simpl.
    rewrite IHc; simpl; auto.
    crush.
    crush.
Qed.
