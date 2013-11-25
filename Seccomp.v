Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
(*
Require Import compcert.common.Smallstep.
*)

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

Definition code := list instruction.

Definition function := code.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Parameter reserve_ident: unit -> ident.

Local Open Scope string_scope.

Definition mkprogram (fs: list function) : program :=
  let g := fun f => (reserve_ident tt, Gfun (Internal f)) in
  let defs := List.map g fs in
  let main := ident_of_string "main" in
  AST.mkprogram defs main.

Definition genv := Genv.t fundef unit.

Inductive state : Type :=
  | State:
    forall (a: int)              (** accumulator *)
           (x: int)              (** index register *)
           (m: ZMap.t int)       (** scratch memory *)
           (f: function)         (** current function *)
           (pc: Z)               (** program counter *)
           (st: state),          (** call state *)
    state
  | Callstate:
    forall (fc: Z)               (** current function *)
           (r: int),             (** return values *)
    state
  | Returnstate:
    forall (v: int)              (** local return value *)
           (st: state),          (** current function *)
    state
  | Haltstate:
    forall (r: int),             (** final return value *)
    state
  .

Definition instruction_at (f: code) (pc: Z) :=
  list_nth_z f pc.

(** sizeof struct seccomp_data *)
Parameter sizeof_seccomp_data : int.

(** mask for return value *)
Parameter seccomp_ret_action : int.

(** default return value *)
Parameter seccomp_ret_allow : int.

Definition seccomp_ret_min (x y: int) : int :=
  let b := Int.cmpu Clt (Int.and x seccomp_ret_action) (Int.and y seccomp_ret_action) in
  if b then x else y.

Section RELSEM.

(** access struct seccomp_data *)
Variable seccomp_bpf_load : int -> int.

Variable ge: genv.

Definition find_function (n: Z) : option fundef :=
  match list_nth_z (PTree.elements ge.(Genv.genv_funs)) n with
  | None => None
  | Some (_, f) => Some f
  end.

Inductive step : state -> trace -> state -> Prop :=
  | exec_Salu_add_k:
      forall st f a x m pc k,
      instruction_at f pc = Some (Salu_add_k k) ->
      let a' := Int.add a k in
      let pc' := pc + 1 in
      step (State a x m f pc st)
        E0 (State a' x m f pc' st)
  | exec_Salu_add_x:
      forall st f a x m pc,
      instruction_at f pc = Some (Salu_add_x) ->
      let a' := Int.add a x in
      let pc' := pc + 1 in
      step (State a x m f pc st)
        E0 (State a' x m f pc' st)
  | exec_Sld_w_abs:
      forall st f a x m pc k,
      instruction_at f pc = Some (Sld_w_abs k) ->
      let a' := seccomp_bpf_load k in
      let pc' := pc + 1 in
      step (State a x m f pc st)
        E0 (State a' x m f pc' st)
  | exec_Sld_w_len:
      forall st f a x m pc,
      instruction_at f pc = Some (Sld_w_len) ->
      let pc' := pc + 1 in
      step (State a x m f pc st)
        E0 (State sizeof_seccomp_data x m f pc' st)
  | exec_Sldx_w_len:
      forall st f a x m pc,
      instruction_at f pc = Some (Sld_w_len) ->
      let pc' := pc + 1 in
      step (State a x m f pc st)
        E0 (State a sizeof_seccomp_data m f pc' st)
  | exec_Sret_k:
      forall st f a x m pc k,
      instruction_at f pc = Some (Sret_k k) ->
      step (State a x m f pc st)
        E0 (Returnstate k st)
  | exec_Sret_a:
      forall st f a x m pc,
      instruction_at f pc = Some (Sret_a) ->
      step (State a x m f pc st)
        E0 (Returnstate a st)
  | exec_call:
      forall fc r f,
      find_function fc = Some (Internal f) ->
      let st := (Callstate fc r) in
      step st
        E0 (State Int.zero Int.zero (ZMap.init Int.zero) f 0 st)
  | exec_return:
      forall fc r v,
      let fc' := fc + 1 in
      let r' := seccomp_ret_min v r in
      step (Returnstate v (Callstate fc r)) E0
           (Callstate fc' r')
  | exec_halt:
      forall fc r,
      find_function fc = None ->
      step (Callstate fc r)
        E0 (Haltstate r)
  .

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro:
      initial_state p (Callstate 0 seccomp_ret_allow).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r,
      final_state (Haltstate r) r.
(*
Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
*)
