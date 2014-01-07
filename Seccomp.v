Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Set Implicit Arguments.

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

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  mksignature nil (Some Tint).

End PROGRAM.

Section SEMANTICS.

Definition genv := Genv.t fundef unit.

Inductive state : Type :=
  | State:
    forall (a: int)              (**r accumulator *)
           (x: int)              (**r index register *)
           (sm: ZMap.t int)      (**r scratch memory *)
           (f: function)         (**r current function *)
           (pc: positive)        (**r program counter *)
           (m: mem),             (**r memory state *)
    state
  | Callstate:
    forall (fd: fundef)          (**r calling function *)
           (m: mem),             (**r memory state *)
    state
  | Returnstate:
    forall (v: int)              (**r local return value *)
           (m: mem),             (**r memory state *)
    state
  .

Fixpoint list_nth_pos (A: Type) (l: list A) (n: positive): option A :=
  match l with
  | nil => None
  | hd :: tl => match n with
    | 1%positive => Some hd
    | _ => list_nth_pos tl (Ppred n)
    end
  end.

Definition instruction_at (f: function) (pc: positive) :=
  list_nth_pos f pc.

Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | exec_Salu_add_k:
      forall a x sm f pc k m,
      instruction_at f pc = Some (Salu_add_k k) ->
      let a' := Int.add a k in
      let pc' := (pc + 1)%positive in
      step ge (State a x sm f pc m)
        E0 (State a' x sm f pc' m)
(*
  | exec_Salu_add_x:
      forall a x sm f pc m,
      instruction_at f pc = Some (Salu_add_x) ->
      let a' := Int.add a x in
      let pc' := pc + 1 in
      step ge (State a x sm f pc m)
        E0 (State a' x sm f pc' m)
  | exec_Sld_w_abs:
      forall a a' x m f pc k,
      instruction_at f pc = Some (Sld_w_abs k) ->
      seccomp_bpf_load k a' ->
      let pc' := pc + 1 in
      step ge (State a x m f pc)
        E0 (State a' x m f pc')
  | exec_Sld_w_len:
      forall a x sm f pc m,
      instruction_at f pc = Some (Sld_w_len) ->
      let pc' := pc + 1 in
      step ge (State a x sm f pc m)
        E0 (State sizeof_seccomp_data x sm f pc' m)
  | exec_Sldx_w_len:
      forall a x sm f pc m,
      instruction_at f pc = Some (Sld_w_len) ->
      let pc' := pc + 1 in
      step ge (State a x sm f pc m)
        E0 (State a sizeof_seccomp_data sm f pc' m)
  | exec_Sret_k:
      forall a x sm f pc k m,
      instruction_at f pc = Some (Sret_k k) ->
      step ge (State a x sm f pc m)
        E0 (Returnstate k m)
*)
  | exec_Sret_a:
      forall a x sm f pc m,
      instruction_at f pc = Some (Sret_a) ->
      step ge (State a x sm f pc m)
        E0 (Returnstate a m)
  | exec_call:
      forall f m,
      step ge (Callstate (Internal f) m)
        E0 (State Int.zero Int.zero (ZMap.init Int.zero) f 1 m)
  .

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b fd m0,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some fd ->
    initial_state p (Callstate fd m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall v m,
      final_state (Returnstate v m) v.

End SEMANTICS.
