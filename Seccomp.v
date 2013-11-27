Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.

Inductive instruction : Type :=
  | Salu_add_k: int -> instruction
      (** A <- A + k *)
  | Salu_sub_k: int -> instruction
      (** A <- A - k *)
  | Salu_mul_k: int -> instruction
      (** A <- A * k *)
  | Salu_div_k: int -> instruction
      (** A <- A / k *)
  | Salu_and_k: int -> instruction
      (** A <- A & k *)
  | Salu_or_k: int -> instruction
      (** A <- A | k *)
  | Salu_xor_k: int -> instruction
      (** A <- A ^ k *)
  | Salu_lsh_k: int -> instruction
      (** A <- A << k *)
  | Salu_rsh_k: int -> instruction
      (** A <- A >> k *)
  | Salu_add_x: instruction
      (** A <- A + X *)
  | Salu_sub_x: instruction
      (** A <- A - X *)
  | Salu_mul_x: instruction
      (** A <- A * X *)
  | Salu_div_x: instruction
      (** A <- A / X *)
  | Salu_and_x: instruction
      (** A <- A & X *)
  | Salu_or_x: instruction
      (** A <- A | X *)
  | Salu_xor_x: int -> instruction
      (** A <- A ^ X *)
  | Salu_lsh_x: instruction
      (** A <- A << X *)
  | Salu_rsh_x: instruction
      (** A <- A >> X *)
  | Salu_neg: instruction
      (** A <- -A *)
  | Sld_w_abs: int -> instruction
      (** A <- seccomp_bpf_load(k), access struct seccomp_data *)
  | Sld_w_len: instruction
      (** A <- sizeof(struct seccomp_data) *)
  | Sldx_w_len: instruction
      (** X <- sizeof(struct seccomp_data) *)
  | Sld_imm: int -> instruction
      (** A <- k *)
  | Sld_mem: int -> instruction
      (** A <- [k] *)
  | Sldx_imm: int -> instruction
      (** X <- k *)
  | Sldx_mem: int -> instruction
      (** X <- [k] *)
  | Sst: int -> instruction
      (** [k] <- A *)
  | Sstx: int -> instruction
      (** [k] <- X *)
  | Sjmp_ja: int -> instruction
  | Sjmp_jgt_k: byte -> byte -> int -> instruction
  | Sjmp_jge_k: byte -> byte -> int -> instruction
  | Sjmp_jeq_k: byte -> byte -> int -> instruction
  | Sjmp_jset_k: byte -> byte -> int -> instruction
  | Sjmp_jgt_x: byte -> byte -> instruction
  | Sjmp_jge_x: byte -> byte -> instruction
  | Sjmp_jeq_x: byte -> byte -> instruction
  | Sjmp_jset_x: byte -> byte -> instruction
  | Smisc_tax: instruction
      (** X <- A *)
  | Smisc_txa: instruction
      (** A <- X *)
  | Sret_k: int -> instruction
      (** ret k **)
  | Sret_a: instruction
      (** ret A **)
  .

(** sizeof struct seccomp_data *)
Parameter sizeof_seccomp_data : int.

Definition code := list instruction.

Definition function := code.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.
