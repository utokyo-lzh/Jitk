Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.

Set Implicit Arguments.

Inductive alu_safe : Type :=
  | Aaddimm: int -> alu_safe
  | Asubimm: int -> alu_safe
  | Amulimm: int -> alu_safe
  | Aandimm: int -> alu_safe
  | Aorimm: int -> alu_safe
  | Axorimm: int -> alu_safe
  | Aadd: alu_safe
  | Asub: alu_safe
  | Amul: alu_safe
  | Aand: alu_safe
  | Aor: alu_safe
  | Axor: alu_safe
  | Aneg: alu_safe
  .

Inductive alu_div : Type :=
  | Adivimm: int -> alu_div
  | Amodimm: int -> alu_div
  | Adiv: alu_div
  | Amod: alu_div
  .

Inductive alu_shift : Type :=
  | Alshimm: int -> alu_shift
  | Arshimm: int -> alu_shift
  | Alsh: alu_shift
  | Arsh: alu_shift
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
  | Salu_safe: alu_safe -> instruction
      (** A <- arithmetic *)
  | Salu_div: alu_div -> instruction
      (** A <- arithmetic *)
  | Salu_shift: alu_shift -> instruction
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
Parameter sizeof_seccomp_data : Z.

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
           (p: block)            (**r input packet *)
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

Definition eval_alu_safe (op: alu_safe) (a: int) (x: int): int :=
  match op with
  | Aaddimm k => Int.add a k
  | Asubimm k => Int.sub a k
  | Amulimm k => Int.mul a k
  | Aandimm k => Int.and a k
  | Aorimm k => Int.or a k
  | Axorimm k => Int.xor a k
  | Aadd => Int.add a x
  | Asub => Int.sub a x
  | Amul => Int.mul a x
  | Aand => Int.and a x
  | Aor => Int.or a x
  | Axor => Int.xor a x
  | Aneg => Int.neg a
  end.

Definition eval_alu_div (op: alu_div) (a: int) (x: int): int :=
  match op with
  | Adivimm k => Int.divu a k
  | Amodimm k => Int.modu a k
  | Adiv => Int.divu a x
  | Amod => Int.modu a x
  end.

Definition eval_alu_shift (op: alu_shift) (a: int) (x: int): int :=
  match op with
  | Alshimm k => Int.shl a k
  | Arshimm k => Int.shru a k
  | Alsh => Int.shl a x
  | Arsh => Int.shru a x
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
  | exec_Salu_safe:
      forall op a x sm f b p m,
      let a' := eval_alu_safe op a x in
      step ge (State a x sm f (Salu_safe op :: b) p m)
        E0 (State a' x sm f b p m)
  | exec_Salu_div:
      forall op a x sm f b p m,
      let a' := eval_alu_div op a x in
      step ge (State a x sm f (Salu_div op :: b) p m)
        E0 (State a' x sm f b p m)
  | exec_Salu_shift:
      forall op a x sm f b p m,
      let a' := eval_alu_shift op a x in
      step ge (State a x sm f (Salu_shift op :: b) p m)
        E0 (State a' x sm f b p m)
  | exec_Sjmp_ja:
      forall a x sm f k b p m,
      let off := Int.unsigned k in
      off < (list_length_z b) ->
      step ge (State a x sm f (Sjmp_ja k :: b) p m)
        E0 (State a x sm f (skipn (nat_of_Z off) b) p m)
  | exec_Sjmp_jc:
      forall cond jt jf a x sm f b p m,
      let off := Byte.unsigned (if (eval_cond cond a x) then jt else jf) in
      off < (list_length_z b) ->
      step ge (State a x sm f (Sjmp_jc cond jt jf :: b) p m)
        E0 (State a x sm f (skipn (nat_of_Z off) b) p m)
  | exec_Sld_w_abs:
      forall a a' k x sm f b p m,
      let off := Int.unsigned k in
      off < sizeof_seccomp_data ->
      off mod 4 = 0 ->
      Mem.load Mint32 m p off = Some (Vint a') ->
      step ge (State a x sm f (Sld_w_abs k :: b) p m)
        E0 (State a' x sm f b p m)
(*
  | exec_Sld_w_len:
      forall a x sm f b p m,
      let a' := Int.repr sizeof_seccomp_data in
      step ge (State a x sm f (Sld_w_len :: b) p m)
        E0 (State a' x sm f b p m)
  | exec_Sldx_w_len:
      forall a x sm f b p m,
      let x' := Int.repr sizeof_seccomp_data in
      step ge (State a x sm f (Sld_w_len :: b) p m)
        E0 (State a x' sm f b p m)
*)
  | exec_Sret_a:
      forall a x sm f b p m,
      step ge (State a x sm f (Sret_a :: b) p m)
        E0 (Returnstate a m)
  | exec_Sret_k:
      forall a x sm f k b p m,
      step ge (State a x sm f (Sret_k k :: b) p m)
        E0 (Returnstate k m)
  | exec_call:
      forall f p m m' m'' bytes,
      list_length_z bytes = sizeof_seccomp_data ->
      Mem.alloc m 0 sizeof_seccomp_data = (m', p) ->
      Mem.storebytes m' p 0 bytes = Some m'' ->
      step ge (Callstate (Internal f) m)
        E0 (State Int.zero Int.zero (ZMap.init Int.zero) f f p m')
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
