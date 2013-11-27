Require Import compcert.common.Smallstep.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import Seccomp.

Inductive state : Type :=
  | State:
    forall (a: int)              (** accumulator *)
           (x: int)              (** index register *)
           (m: ZMap.t int)       (** scratch memory *)
           (f: function)         (** current function *)
           (pc: Z),              (** program counter *)
    state
  | Callstate:
    forall (f: function),        (** calling function *)
    state
  | Returnstate:
    forall (v: int),             (** local return value *)
    state
  .

Section RELSEM.

(** access struct seccomp_data *)
Variable seccomp_bpf_load : int -> int -> Prop.

Variable ge: genv.

Definition instruction_at (f: function) (pc: Z) :=
  list_nth_z f pc.

Inductive step : state -> trace -> state -> Prop :=
  | exec_Salu_add_k:
      forall a x m f pc k,
      instruction_at f pc = Some (Salu_add_k k) ->
      let a' := Int.add a k in
      let pc' := pc + 1 in
      step (State a x m f pc)
        E0 (State a' x m f pc')
  | exec_Salu_add_x:
      forall a x m f pc,
      instruction_at f pc = Some (Salu_add_x) ->
      let a' := Int.add a x in
      let pc' := pc + 1 in
      step (State a x m f pc)
        E0 (State a' x m f pc')
  | exec_Sld_w_abs:
      forall a x m f pc k,
      instruction_at f pc = Some (Sld_w_abs k) ->
      seccomp_bpf_load k a' ->
      let pc' := pc + 1 in
      step (State a x m f pc)
        E0 (State a' x m f pc')
  | exec_Sld_w_len:
      forall a x m f pc,
      instruction_at f pc = Some (Sld_w_len) ->
      let pc' := pc + 1 in
      step (State a x m f pc)
        E0 (State sizeof_seccomp_data x m f pc')
  | exec_Sldx_w_len:
      forall a x m f pc,
      instruction_at f pc = Some (Sld_w_len) ->
      let pc' := pc + 1 in
      step (State a x m f pc)
        E0 (State a sizeof_seccomp_data m f pc')
  | exec_Sret_k:
      forall a x m f pc k,
      instruction_at f pc = Some (Sret_k k) ->
      step (State a x m f pc)
        E0 (Returnstate k)
  | exec_Sret_a:
      forall a x m f pc,
      instruction_at f pc = Some (Sret_a) ->
      step (State a x m f pc)
        E0 (Returnstate a)
  | exec_call:
      forall f,
      step (Callstate f)
        E0 (State Int.zero Int.zero (ZMap.init Int.zero) f 0)
  .

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro:
      initial_state p (Callstate p.(prog_main)).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall v,
      final_state (Returnstate v) v.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
