Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import Seccomp.
Require Import Seccompconf.
Require Import Seccompenc.
Import ListNotations.

Inductive action : Type :=
  | Akill: action
  | Atrap: short -> action
  | Aerrno: short -> action
  | Atrace: short -> action
  | Aallow: action
  .

Parameter SECCOMP_RET_KILL  : Z.  (* 0 *)
Parameter SECCOMP_RET_TRAP  : Z.  (* 0x00030000 | si_errno *)
Parameter SECCOMP_RET_ERRNO : Z.  (* 0x00050000 | errno *)
Parameter SECCOMP_RET_TRACE : Z.  (* 0x7ff00000 | message *)
Parameter SECCOMP_RET_ALLOW : Z.  (* 0x7fff0000 *)

Notation SECCOMP_NR_OFFSET := 0%Z.

Definition action_enc (a: action) :=
  match a with
  | Akill    => Int.repr SECCOMP_RET_KILL
  | Atrap k  => Int.or (Int.repr SECCOMP_RET_TRAP) (Int.repr (Short.unsigned k))
  | Aerrno k => Int.or (Int.repr SECCOMP_RET_ERRNO) (Int.repr (Short.unsigned k))
  | Atrace k => Int.or (Int.repr SECCOMP_RET_ERRNO) (Int.repr (Short.unsigned k))
  | Aallow   => Int.repr SECCOMP_RET_ALLOW
  end.

Record rule : Type := mkrule {
  rl_action: action;
  rl_syscall: int
  (* TODO: arg predicates *)
}.

Section PROGRAM.

Definition code := list rule.

Record function : Type := mkfunction {
  fn_default: action;
  fn_body: code
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

End PROGRAM.

Section SEMANTICS.

Definition genv := Genv.t fundef unit.

(*
Record seccompdata : Type := mkseccompdata {
  sd_syscall: int;
  sd_arch: int;
  sd_ip: int64;
  sd_args: list int64
}.
*)

Inductive state : Type :=
  | State:
    forall (f: function)         (**r function *)
           (c: code)             (**r current program point *)
           (p: block)            (**r input packet *)
           (m: mem),             (**r memory state *)
    state
  | Callstate:
    forall (fd: fundef)          (**r calling function *)
           (p: block)            (**r input packet *)
           (m: mem),             (**r memory state *)
    state
  | Returnstate:
    forall (a: action),          (**r action *)
    state
  .

Definition eval_rule (r: rule) (m: mem) (b: block) :=
  Some (Vint r.(rl_syscall)) = Mem.load Mint32 m b SECCOMP_NR_OFFSET.

Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | exec_rule:
    forall f r b p m,
    eval_rule r m p ->
    step ge (State f (r :: b) p m)
         E0 (Returnstate r.(rl_action))
  | exec_skip:
    forall f r b p m,
    ~ eval_rule r m p ->
    step ge (State f (r :: b) p m)
         E0 (State f b p m)
  | exec_default:
    forall f p m,
    step ge (State f nil p m)
         E0 (Returnstate f.(fn_default))
  | exec_call:
    forall f p m,
    step ge (Callstate (Internal f) p m)
         E0 (State f f.(fn_body) p m)
  .

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b fd m0 m1 m2 pkt,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some fd ->
    Mem.alloc m0 0 sizeof_seccomp_data = (m1, pkt) ->
    Mem.storebytes m1 pkt 0 (Memdata.inj_bytes seccomp_data) = Some m2 ->
    initial_state p (Callstate fd pkt m2).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall a,
      final_state (Returnstate a) (action_enc a).

End SEMANTICS.
