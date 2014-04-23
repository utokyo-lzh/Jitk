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
    forall (a: action)           (**r action *)
           (m: mem),             (**r memory state *)
    state
  .

Definition eval_rule (r: rule) (m: mem) (b: block) :=
  Some (Vint r.(rl_syscall)) = Mem.load Mint32 m b SECCOMP_NR_OFFSET.

Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | exec_rule:
    forall f r b p m,
    eval_rule r m p ->
    step ge (State f (r :: b) p m)
         E0 (Returnstate r.(rl_action) m)
  | exec_skip:
    forall f r b p m,
    ~ eval_rule r m p ->
    step ge (State f (r :: b) p m)
         E0 (State f b p m)
  | exec_default:
    forall f p m,
    step ge (State f nil p m)
         E0 (Returnstate f.(fn_default) m)
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
  | final_state_intro: forall a m,
      final_state (Returnstate a m) (action_enc a).

End SEMANTICS.

Section TRANSL.

Open Local Scope error_monad_scope.

Definition transl_rule (r: rule) : Seccomp.code :=
  [
    Sld_w_abs (Int.repr SECCOMP_NR_OFFSET);
    Sjmp_jc (Jeqimm r.(rl_syscall)) Byte.zero Byte.one;
    Sret_k (action_enc r.(rl_action))
  ].

Fixpoint transl_code (c: code) : Seccomp.code :=
  match c with
  | nil => nil
  | hd :: tl => (transl_rule hd) ++ (transl_code tl)
  end.

Definition transl_function (f: function) : Seccomp.function :=
  transl_code f.(fn_body) ++ [ Sret_k (action_enc f.(fn_default)) ].

Definition transl_fundef (fd: fundef) :=
  match fd with
  | Internal f => OK (Internal (transl_function f))
  | External ef => Error (msg "no external function allowed")
  end.

Definition transl_program (p: program) : res Seccomp.program :=
  transform_partial_program transl_fundef p.

End TRANSL.
