Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import MiscLemmas.
Require Import InetDiagConf.
Import ListNotations.

Definition port := int.

Inductive location : Type :=
  | Reject : location
  | Loc : nat -> location
  .

Record hostcond : Type := mkhostcond {
  hcfamily : int;
  hcprefixlen : int;
  hcport : port;
  hcaddr : int
}.

Inductive condition : Type :=
  | Sge : port -> condition
  | Sle : port -> condition
  | Dge : port -> condition
  | Dle : port -> condition
  .
(* TODO Scond and Dcond *)

Inductive instruction : Type :=
  | Nop : instruction
  | Jmp : location -> instruction
  | Cjmp : condition -> location -> instruction
  .

Definition code := list instruction.

Section SEMANTICS.

Definition function := code.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.
Definition genv := Genv.t fundef unit.

Definition checkhc (hc: hostcond) (e: block) := false. (* XXX TODO *)

Inductive state : Type :=
  | State:
    forall (c: code)             (**r current program point *)
           (f: function)         (**r current function *)
           (e: block)            (**r input entry *)
           (m: mem),             (**r memory state *)
    state
  | Callstate:
    forall (fd: fundef)          (**r calling function *)
           (e: block)            (**r input entry *)
           (m: mem),             (**r memory state *)
    state
  | Returnstate:
    forall (v: int)              (**r local return value *)
           (m: mem),             (**r memory state *)
    state
  .

Definition field : Type := (memory_chunk * Z)%type.

Definition e_saddr     : field := (Mint32, 0).
Definition e_daddr     : field := (Mint32, 4).
Definition e_sport     : field := (Mint16unsigned, 8).
Definition e_dport     : field := (Mint16unsigned, 10).
Definition e_family    : field := (Mint16unsigned, 12).
Definition e_userlocks : field := (Mint16unsigned, 14).

Definition load_field (f: field) (e: block) (m: mem) : option val :=
  match f with
  | (mc, ofs) => Mem.load mc m e ofs
  end.

Definition cond_field (cond: condition) : field :=
  match cond with
  | Sge _ | Sle _ => e_sport
  | Dge _ | Dle _ => e_dport
  end.

Definition eval_cond (cond: condition) (v: int) : bool :=
  match cond with
  | Sge p | Dge p => Int.cmpu Cge v p
  | Sle p | Dle p => Int.cmpu Cle v p
  end.

Inductive step (ge: genv) : state -> trace -> state -> Prop :=
  | ST_Accept : forall f e m,
    step ge (State nil f e m) E0 (Returnstate Int.one m)
  | ST_Nop : forall r f e m,
    step ge (State (Nop :: r) f e m) E0 (State r f e m)
  | ST_Jmp_Reject : forall r f e m,
    step ge (State (Jmp Reject :: r) f e m) E0 (Returnstate Int.zero m)
  | ST_Jmp_Loc : forall r f e m n,
    (n <= length r)%nat ->
    step ge (State (Jmp (Loc n) :: r) f e m) E0 (State (skipn n r) f e m)
  | ST_Cjmp_true : forall r f e m v cond loc,
    load_field (cond_field cond) e m = Some (Vint v) ->
    Is_true (eval_cond cond v) ->
    step ge (State (Cjmp cond loc :: r) f e m) E0 (State r f e m)
  | ST_Cjmp_Reject : forall r f e m v cond,
    load_field (cond_field cond) e m = Some (Vint v) ->
    ~ Is_true (eval_cond cond v) ->
    step ge (State (Cjmp cond Reject :: r) f e m) E0 (Returnstate Int.zero m)
  | ST_Cjmp_Loc : forall r f e m v cond n,
    (n <= length r)%nat ->
    load_field (cond_field cond) e m = Some (Vint v) ->
    ~ Is_true (eval_cond cond v) ->
    step ge (State (Cjmp cond (Loc n) :: r) f e m) E0 (State (skipn n r) f e m)
  .

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b fd m0 m1 m2 pkt,
    let ge := Genv.globalenv p in
    Genv.init_mem p = Some m0 ->
    Genv.find_symbol ge p.(prog_main) = Some b ->
    Genv.find_funct_ptr ge b = Some fd ->
    Mem.alloc m0 0 sizeof_entry = (m1, pkt) ->
    Mem.storebytes m1 pkt 0 (Memdata.inj_bytes entry_input) = Some m2 ->
    initial_state p (Callstate fd pkt m2).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall v m,
      final_state (Returnstate v m) v.

End SEMANTICS.
