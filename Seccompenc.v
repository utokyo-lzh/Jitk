Require Import ZArith.
Require Import Coq.Lists.List.
Import List.ListNotations.
Require Import compcert.common.Errors.
Require Import compcert.common.Memdata.
Require Import compcert.lib.Integers.
Require Import Seccomp.
Require Import CpdtTactics.

Open Local Scope list_scope.
Open Local Scope error_monad_scope.

Module Wordsize_16.
  Definition wordsize := 16%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof.
    unfold wordsize; congruence.
  Qed.
End Wordsize_16.

Module Short := Make(Wordsize_16).
Notation short := Short.int.

Record encoding : Type :=
  mkenc { enc_code: short; enc_jt: byte; enc_jf: byte; enc_k: int }.
Definition zerobyte := Byte.repr 0.
Definition zeroint := Int.repr 0.

Definition encode_inst (i: Seccomp.instruction) : res encoding :=
  match i with
  | Sret_a =>
    OK (mkenc (Short.repr 2)  zerobyte zerobyte zeroint)
  | Salu_add_k k =>
    OK (mkenc (Short.repr 3)  zerobyte zerobyte k)
  | Sjmp_ja k =>
    OK (mkenc (Short.repr 41) zerobyte zerobyte k)
  | _ => Error (msg "unknown Seccomp.instruction")
  end.

Definition decode_inst (e: encoding) : res Seccomp.instruction :=
  match e with
  | mkenc c jt jf k =>
    match Short.unsigned c with
    | 2%Z   => OK (Sret_a)
    | 3%Z   => OK (Salu_add_k k)
    | 41%Z  => OK (Sjmp_ja k)
    | _ => Error (msg "unknown opcode")
    end
  end.

Lemma encode_decode_inst:
  forall i e,
  encode_inst i = OK e -> decode_inst e = OK i.
Proof.
  induction i; crush.
Qed.

Definition encode_bytes (e: encoding) : res (list byte) :=
  OK ((encode_int 2 (Short.unsigned (enc_code e))) ++
      (encode_int 1 (Byte.unsigned  (enc_jt   e))) ++
      (encode_int 1 (Byte.unsigned  (enc_jf   e))) ++
      (encode_int 4 (Int.unsigned   (enc_k    e)))).

Definition decode_bytes (l: list byte) : res encoding :=
  match l with
  | [ a; b; c; d; e; f; g; h ] =>
    OK (mkenc (Short.repr (decode_int [ a; b ]))
              (Byte.repr (decode_int [ c ]))
              (Byte.repr (decode_int [ d ]))
              (Int.repr (decode_int [ e; f; g; h ])))
  | _ => Error (msg "missing 8 bytes")
  end.

Lemma encode_decode_bytes:
  forall e l,
  encode_bytes e = OK l -> decode_bytes l = OK e.
Proof.
  (* XXX *)
Admitted.

Fixpoint seccomp_encode (c: Seccomp.code) : res (list byte) :=
  match c with
  | nil => OK nil
  | hd::tl =>
    do e <- encode_inst hd;
    do eb <- encode_bytes e;
    do tt <- seccomp_encode tl;
    OK (eb ++ tt)
  end.

Fixpoint seccomp_decode (l: list byte) : res Seccomp.code :=
  match l with
  | nil => OK nil
  | a::b::c::d::e::f::g::h::tl =>
    do enc <- decode_bytes [a; b; c; d; e; f; g; h];
    do i <- decode_inst enc;
    do tt <- seccomp_decode tl;
    OK (i :: tt)
  | _ => Error (msg "uneven bytes")
  end.

Theorem seccomp_encode_decode:
  forall c l,
  seccomp_encode c = OK l -> seccomp_decode l = OK c.
Proof.
  (* XXX *)
Admitted.

