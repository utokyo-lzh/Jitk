Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Require Import compcert.cfrontend.Ctypes.

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

Section PROGRAM.

Definition function := code.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef type.

Definition genv := Genv.t fundef type.

End PROGRAM.

Inductive state : Type :=
  | State:
    forall (a: int)              (** accumulator *)
           (x: int)              (** index register *)
           (m: ZMap.t int)       (** scratch memory *)
           (f: function)         (** current function *)
           (pc: Z),              (** program counter *)
    state
  | Callstate:
    forall (fd: fundef),         (** calling function *)
    state
  | Returnstate:
    forall (v: int),             (** local return value *)
    state
  .

Section SEMANTICS.

Definition instruction_at (f: function) (pc: Z) :=
  list_nth_z f pc.

Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | exec_Salu_add_k:
      forall a x m f pc k,
      instruction_at f pc = Some (Salu_add_k k) ->
      let a' := Int.add a k in
      let pc' := pc + 1 in
      step ge (State a x m f pc)
        E0 (State a' x m f pc')
  | exec_Salu_add_x:
      forall a x m f pc,
      instruction_at f pc = Some (Salu_add_x) ->
      let a' := Int.add a x in
      let pc' := pc + 1 in
      step ge (State a x m f pc)
        E0 (State a' x m f pc')
(*
  | exec_Sld_w_abs:
      forall a a' x m f pc k,
      instruction_at f pc = Some (Sld_w_abs k) ->
      seccomp_bpf_load k a' ->
      let pc' := pc + 1 in
      step ge (State a x m f pc)
        E0 (State a' x m f pc')
*)
  | exec_Sld_w_len:
      forall a x m f pc,
      instruction_at f pc = Some (Sld_w_len) ->
      let pc' := pc + 1 in
      step ge (State a x m f pc)
        E0 (State sizeof_seccomp_data x m f pc')
  | exec_Sldx_w_len:
      forall a x m f pc,
      instruction_at f pc = Some (Sld_w_len) ->
      let pc' := pc + 1 in
      step ge (State a x m f pc)
        E0 (State a sizeof_seccomp_data m f pc')
  | exec_Sret_k:
      forall a x m f pc k,
      instruction_at f pc = Some (Sret_k k) ->
      step ge (State a x m f pc)
        E0 (Returnstate k)
  | exec_Sret_a:
      forall a x m f pc,
      instruction_at f pc = Some (Sret_a) ->
      step ge (State a x m f pc)
        E0 (Returnstate a)
  | exec_call:
      forall f,
      step ge (Callstate (Internal f))
        E0 (State Int.zero Int.zero (ZMap.init Int.zero) f 0)
  .

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f,
    let ge := Genv.globalenv p in
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some f ->
    initial_state p (Callstate f).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall v,
      final_state (Returnstate v) v.

End SEMANTICS.
