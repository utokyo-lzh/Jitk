Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Set Implicit Arguments.

Inductive alu : Type :=
  | Aaddimm: int -> alu
  | Asubimm: int -> alu
  | Amulimm: int -> alu
  | Adivimm: int -> alu
  | Amodimm: int -> alu
  | Aandimm: int -> alu
  | Aorimm: int -> alu
  | Axorimm: int -> alu
  | Alshimm: int -> alu
  | Arshimm: int -> alu
  | Aadd: alu
  | Asub: alu
  | Amul: alu
  | Adiv: alu
  | Amod: alu
  | Aand: alu
  | Aor: alu
  | Axor: alu
  | Alsh: alu
  | Arsh: alu
  | Aneg: alu
  .

Inductive condition : Type :=
  | Jgtimm: int -> condition
  | Jgeimm: int -> condition
  | Jeqimm: int -> condition
  | Jsetimm: int -> condition
  | Jgt: condition
  | Jge: condition
  | Jeq: condition
  | Jset: condition
  .

Inductive instruction : Type :=
  | Salu: alu -> instruction
      (** A <- arithmetic *)
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
  | Sjmp_jc: condition -> byte -> byte -> instruction
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
           (c: code)             (**r current program point *)
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

Definition eval_alu (op: alu) (a: int) (x: int): int :=
  match op with
  | Aaddimm k => Int.add a k
  | Asubimm k => Int.sub a k
  | Amulimm k => Int.mul a k
  | Adivimm k => Int.divu a k
  | Amodimm k => Int.modu a k
  | Aandimm k => Int.and a k
  | Aorimm k => Int.or a k
  | Axorimm k => Int.xor a k
  | Alshimm k => Int.shl a k
  | Arshimm k => Int.shru a k
  | Aadd => Int.add a x
  | Asub => Int.sub a x
  | Amul => Int.mul a x
  | Adiv => Int.divu a x
  | Amod => Int.modu a x
  | Aand => Int.and a x
  | Aor => Int.or a x
  | Axor => Int.xor a x
  | Alsh => Int.shl a x
  | Arsh => Int.shru a x
  | Aneg => Int.neg a
  end.

Definition eval_cond (cond: condition) (a: int) (x: int): bool :=
  match cond with
  | Jsetimm k => negb (Int.eq (Int.and a k) Int.zero)
    (* A & k *)
  | Jgtimm k => Int.cmpu Cgt a k
    (* A > k *)
  | Jgeimm k => Int.cmpu Cge a k
    (* A >= k *)
  | Jeqimm k => Int.eq a k
    (* A == k *)
  | Jset => negb (Int.eq (Int.and a x) Int.zero)
    (* A & X *)
  | Jgt => Int.cmpu Cgt a x
    (* A > X *)
  | Jge => Int.cmpu Cge a x
    (* A >= X *)
  | Jeq => Int.eq a x
    (* A == X *)
  end.

Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | exec_Salu:
      forall op a x sm f b m,
      let a' := eval_alu op a x in
      step ge (State a x sm f (Salu op :: b) m)
        E0 (State a' x sm f b m)
  | exec_Sjmp_ja:
      forall a x sm f k b m,
      let off := Int.unsigned k in
      off < (list_length_z b) ->
      step ge (State a x sm f (Sjmp_ja k :: b) m)
        E0 (State a x sm f (skipn (nat_of_Z off) b) m)
  | exec_Sjmp_jc:
      forall cond jt jf a x sm f b m,
      let off := Byte.unsigned (if (eval_cond cond a x) then jt else jf) in
      off < (list_length_z b) ->
      step ge (State a x sm f (Sjmp_jc cond jt jf :: b) m)
        E0 (State a x sm f (skipn (nat_of_Z off) b) m)
(*
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
*)
  | exec_Sret_a:
      forall a x sm f b m,
      step ge (State a x sm f (Sret_a :: b) m)
        E0 (Returnstate a m)
  | exec_Sret_k:
      forall a x sm f k b m,
      step ge (State a x sm f (Sret_k k :: b) m)
        E0 (Returnstate k m)
  | exec_call:
      forall f m,
      step ge (Callstate (Internal f) m)
        E0 (State Int.zero Int.zero (ZMap.init Int.zero) f f m)
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
