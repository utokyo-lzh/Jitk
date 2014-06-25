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

(* Reference:
    linux-git/include/uapi/linux/filter.h
    linux-git/net/core/filter.c
*)
Notation BPF_S_RET_K      := 6.
Notation BPF_S_RET_A      := 22.
Notation BPF_S_JMP_JA     := 5.
Notation BPF_S_JMP_JEQ_K  := 21.
Notation BPF_S_JMP_JEQ_X  := 29.
Notation BPF_S_JMP_JGE_K  := 53.
Notation BPF_S_JMP_JGE_X  := 61.
Notation BPF_S_JMP_JGT_K  := 37.
Notation BPF_S_JMP_JGT_X  := 45.
Notation BPF_S_JMP_JSET_K := 69.
Notation BPF_S_JMP_JSET_X := 77.
Notation BPF_S_ALU_ADD_K  := 4.
Notation BPF_S_ALU_ADD_X  := 12.
Notation BPF_S_ALU_SUB_K  := 20.
Notation BPF_S_ALU_SUB_X  := 28.
Notation BPF_S_ALU_MUL_K  := 36.
Notation BPF_S_ALU_MUL_X  := 44.
Notation BPF_S_ALU_DIV_K  := 52.
Notation BPF_S_ALU_DIV_X  := 60.
Notation BPF_S_ALU_MOD_K  := 148.
Notation BPF_S_ALU_MOD_X  := 156.
Notation BPF_S_ALU_AND_K  := 84.
Notation BPF_S_ALU_AND_X  := 92.
Notation BPF_S_ALU_OR_K   := 68.
Notation BPF_S_ALU_OR_X   := 76.
Notation BPF_S_ALU_XOR_K  := 164.
Notation BPF_S_ALU_XOR_X  := 172.
Notation BPF_S_ALU_LSH_K  := 100.
Notation BPF_S_ALU_LSH_X  := 108.
Notation BPF_S_ALU_RSH_K  := 116.
Notation BPF_S_ALU_RSH_X  := 124.
Notation BPF_S_ALU_NEG    := 132.
Notation BPF_S_LD_W_ABS   := 32.
Notation BPF_S_LD_W_LEN   := 128.
Notation BPF_S_LDX_W_LEN  := 129.
Notation BPF_S_LD_MEM     := 96.
Notation BPF_S_LDX_MEM    := 97.
Notation BPF_S_ST         := 2.
Notation BPF_S_STX        := 3.
(* TODO: rest of BPF_LD series *)
(* TODO: rest of BPF_LDX series *)
(* TODO: BPF_MISC series *)
(* TODO: BPF_ST series *)
(* TODO: BPF_STX series *)

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
  | Sld_w_len =>
    OK (mkencx BPF_S_LD_W_LEN Byte.zero Byte.zero Int.zero)
  | Sldx_w_len =>
    OK (mkencx BPF_S_LDX_W_LEN Byte.zero Byte.zero Int.zero)

  | Sld_mem k =>
    OK (mkencx BPF_S_LD_MEM Byte.zero Byte.zero k)
  | Sldx_mem k =>
    OK (mkencx BPF_S_LDX_MEM Byte.zero Byte.zero k)
  | Sst k =>
    OK (mkencx BPF_S_ST Byte.zero Byte.zero k)
  | Sstx k =>
    OK (mkencx BPF_S_STX Byte.zero Byte.zero k)

  | Salu_safe (Aaddimm k) =>
    OK (mkencx BPF_S_ALU_ADD_K Byte.zero Byte.zero k)
  | Salu_safe Aadd =>
    OK (mkencx BPF_S_ALU_ADD_X Byte.zero Byte.zero Int.zero)
  | Salu_safe (Asubimm k) =>
    OK (mkencx BPF_S_ALU_SUB_K Byte.zero Byte.zero k)
  | Salu_safe Asub =>
    OK (mkencx BPF_S_ALU_SUB_X Byte.zero Byte.zero Int.zero)
  | Salu_safe (Amulimm k) =>
    OK (mkencx BPF_S_ALU_MUL_K Byte.zero Byte.zero k)
  | Salu_safe Amul =>
    OK (mkencx BPF_S_ALU_MUL_X Byte.zero Byte.zero Int.zero)
  | Salu_safe (Aandimm k) =>
    OK (mkencx BPF_S_ALU_AND_K Byte.zero Byte.zero k)
  | Salu_safe Aand =>
    OK (mkencx BPF_S_ALU_AND_X Byte.zero Byte.zero Int.zero)
  | Salu_safe (Aorimm k) =>
    OK (mkencx BPF_S_ALU_OR_K Byte.zero Byte.zero k)
  | Salu_safe Aor =>
    OK (mkencx BPF_S_ALU_OR_X Byte.zero Byte.zero Int.zero)
  | Salu_safe (Axorimm k) =>
    OK (mkencx BPF_S_ALU_XOR_K Byte.zero Byte.zero k)
  | Salu_safe Axor =>
    OK (mkencx BPF_S_ALU_XOR_X Byte.zero Byte.zero Int.zero)
  | Salu_safe Aneg =>
    OK (mkencx BPF_S_ALU_NEG Byte.zero Byte.zero Int.zero)

  | Salu_div (Adivimm k) =>
    OK (mkencx BPF_S_ALU_DIV_K Byte.zero Byte.zero k)
  | Salu_div Adiv =>
    OK (mkencx BPF_S_ALU_DIV_X Byte.zero Byte.zero Int.zero)
  | Salu_div (Amodimm k) =>
    OK (mkencx BPF_S_ALU_MOD_K Byte.zero Byte.zero k)
  | Salu_div Amod =>
    OK (mkencx BPF_S_ALU_MOD_X Byte.zero Byte.zero Int.zero)

  | Salu_shift (Alshimm k) =>
    OK (mkencx BPF_S_ALU_LSH_K Byte.zero Byte.zero k)
  | Salu_shift Alsh =>
    OK (mkencx BPF_S_ALU_LSH_X Byte.zero Byte.zero Int.zero)
  | Salu_shift (Arshimm k) =>
    OK (mkencx BPF_S_ALU_RSH_K Byte.zero Byte.zero k)
  | Salu_shift Arsh =>
    OK (mkencx BPF_S_ALU_RSH_X Byte.zero Byte.zero Int.zero)

  | Sjmp_ja k =>
    OK (mkencx BPF_S_JMP_JA Byte.zero Byte.zero k)
  | Sjmp_jc (Jeqimm k) t f =>
    OK (mkencx BPF_S_JMP_JEQ_K t f k)
  | Sjmp_jc Jeq t f =>
    OK (mkencx BPF_S_JMP_JEQ_X t f Int.zero)
  | Sjmp_jc (Jgeimm k) t f =>
    OK (mkencx BPF_S_JMP_JGE_K t f k)
  | Sjmp_jc Jge t f =>
    OK (mkencx BPF_S_JMP_JGE_X t f Int.zero)
  | Sjmp_jc (Jgtimm k) t f =>
    OK (mkencx BPF_S_JMP_JGT_K t f k)
  | Sjmp_jc Jgt t f =>
    OK (mkencx BPF_S_JMP_JGT_X t f Int.zero)
  | Sjmp_jc (Jsetimm k) t f =>
    OK (mkencx BPF_S_JMP_JSET_K t f k)
  | Sjmp_jc Jset t f =>
    OK (mkencx BPF_S_JMP_JSET_X t f Int.zero)

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
  | BPF_S_LD_W_LEN   => OK (Sld_w_len)
  | BPF_S_LDX_W_LEN  => OK (Sldx_w_len)

  | BPF_S_LD_MEM     => OK (Sld_mem k)
  | BPF_S_LDX_MEM    => OK (Sldx_mem k)
  | BPF_S_ST         => OK (Sst k)
  | BPF_S_STX        => OK (Sstx k)

  | BPF_S_ALU_ADD_K  => OK (Salu_safe (Aaddimm k))
  | BPF_S_ALU_ADD_X  => OK (Salu_safe Aadd)
  | BPF_S_ALU_SUB_K  => OK (Salu_safe (Asubimm k))
  | BPF_S_ALU_SUB_X  => OK (Salu_safe Asub)
  | BPF_S_ALU_MUL_K  => OK (Salu_safe (Amulimm k))
  | BPF_S_ALU_MUL_X  => OK (Salu_safe Amul)
  | BPF_S_ALU_AND_K  => OK (Salu_safe (Aandimm k))
  | BPF_S_ALU_AND_X  => OK (Salu_safe Aand)
  | BPF_S_ALU_OR_K   => OK (Salu_safe (Aorimm k))
  | BPF_S_ALU_OR_X   => OK (Salu_safe Aor)
  | BPF_S_ALU_XOR_K  => OK (Salu_safe (Axorimm k))
  | BPF_S_ALU_XOR_X  => OK (Salu_safe Axor)
  | BPF_S_ALU_NEG    => OK (Salu_safe Aneg)

  | BPF_S_ALU_DIV_K  => OK (Salu_div (Adivimm k))
  | BPF_S_ALU_DIV_X  => OK (Salu_div Adiv)
  | BPF_S_ALU_MOD_K  => OK (Salu_div (Amodimm k))
  | BPF_S_ALU_MOD_X  => OK (Salu_div Amod)

  | BPF_S_ALU_LSH_K  => OK (Salu_shift (Alshimm k))
  | BPF_S_ALU_LSH_X  => OK (Salu_shift Alsh)
  | BPF_S_ALU_RSH_K  => OK (Salu_shift (Arshimm k))
  | BPF_S_ALU_RSH_X  => OK (Salu_shift Arsh)

  | BPF_S_JMP_JA     => OK (Sjmp_ja k)
  | BPF_S_JMP_JEQ_K  => OK (Sjmp_jc (Jeqimm k) t f)
  | BPF_S_JMP_JEQ_X  => OK (Sjmp_jc Jeq t f)
  | BPF_S_JMP_JGE_K  => OK (Sjmp_jc (Jgeimm k) t f)
  | BPF_S_JMP_JGE_X  => OK (Sjmp_jc Jge t f)
  | BPF_S_JMP_JGT_K  => OK (Sjmp_jc (Jgtimm k) t f)
  | BPF_S_JMP_JGT_X  => OK (Sjmp_jc Jgt t f)
  | BPF_S_JMP_JSET_K => OK (Sjmp_jc (Jsetimm k) t f)
  | BPF_S_JMP_JSET_X => OK (Sjmp_jc Jset t f)

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

