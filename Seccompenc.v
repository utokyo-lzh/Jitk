Require Import compcert.common.Errors.
Require Import compcert.common.Memdata.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import Seccomp.
Require Import CpdtTactics.
Import List.ListNotations.

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

Record encoding : Type := mkenc {
  enc_code: short;
  enc_jt: byte;
  enc_jf: byte;
  enc_k: int
}.

(* linux-git/include/uapi/linux/filter.h *)
Notation BPF_S_RET_K      := 6.
Notation BPF_S_RET_A      := 22.
Notation BPF_S_LD_W_ABS   := 32.
Notation BPF_S_JMP_JA     := 5.
Notation BPF_S_JMP_JEQ_K  := 21.
Notation BPF_S_JMP_JSET_K := 69.
Notation BPF_S_ALU_ADD_K  := 4.
Notation BPF_S_ALU_ADD_X  := 12.

Definition mkencx (c:Z) (jt jf:byte) (k:int) :=
  mkenc (Short.repr c) jt jf k.

Definition encode_inst (i: Seccomp.instruction) : res encoding :=
  match i with
  | Sret_a =>
    OK (mkencx BPF_S_RET_A Byte.zero Byte.zero Int.zero)
  | Sret_k k =>
    OK (mkencx BPF_S_RET_K Byte.zero Byte.zero k)

  | Sld_w_abs k =>
    OK (mkencx BPF_S_LD_W_ABS Byte.zero Byte.zero k)

  | Salu (Aaddimm k) =>
    OK (mkencx BPF_S_ALU_ADD_K Byte.zero Byte.zero k)
  | Salu Aadd =>
    OK (mkencx BPF_S_ALU_ADD_X Byte.zero Byte.zero Int.zero)

  | Sjmp_ja k =>
    OK (mkencx BPF_S_JMP_JA Byte.zero Byte.zero k)
  | Sjmp_jc (Jeqimm k) t f =>
    OK (mkencx BPF_S_JMP_JEQ_K t f k)
  | Sjmp_jc (Jsetimm k) t f =>
    OK (mkencx BPF_S_JMP_JSET_K t f k)

  | _ => Error (msg "unknown Seccomp.instruction")
  end.

Definition decode_inst (e: encoding) : res Seccomp.instruction :=
  let k := e.(enc_k) in
  let t := e.(enc_jt) in
  let f := e.(enc_jf) in
  match Short.unsigned e.(enc_code) with
  | BPF_S_RET_A      => OK (Sret_a)
  | BPF_S_RET_K      => OK (Sret_k k)

  | BPF_S_LD_W_ABS   => OK (Sld_w_abs k)

  | BPF_S_ALU_ADD_K  => OK (Salu (Aaddimm k))
  | BPF_S_ALU_ADD_X  => OK (Salu Aadd)

  | BPF_S_JMP_JA     => OK (Sjmp_ja k)
  | BPF_S_JMP_JEQ_K  => OK (Sjmp_jc (Jeqimm k) t f)
  | BPF_S_JMP_JSET_K => OK (Sjmp_jc (Jsetimm k) t f)

  | Zpos x => Error (MSG "unknown opcode: " :: POS x :: nil)
  | _ => Error (msg "unknown opcode")
  end.

Definition encode_bytes (e: encoding) : res (list byte) :=
  OK ((encode_int 2 (Short.unsigned (enc_code e))) ++
      (encode_int 1 (Byte.unsigned  (enc_jt   e))) ++
      (encode_int 1 (Byte.unsigned  (enc_jf   e))) ++
      (encode_int 4 (Int.unsigned   (enc_k    e)))).

Definition decode_bytes (l: list byte) : res encoding :=
  match l with
  | [ a; b; c; d; e; f; g; h ] =>
    OK (mkenc (Short.repr (decode_int [ a; b ]))
              (Byte.repr  (decode_int [ c ]))
              (Byte.repr  (decode_int [ d ]))
              (Int.repr   (decode_int [ e; f; g; h ])))
  | _ => Error (msg "missing 8 bytes")
  end.

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

