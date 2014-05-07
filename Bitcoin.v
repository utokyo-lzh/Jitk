Require Import ZArith.
Require Import List.
Import ListNotations.

Definition stackdata := list Z.

Inductive instruction : Type :=
  (* Constants: OP_FALSE, OP_PUSHDATAn, OP_1NEGATE, OP_TRUE, .. *)
  | Op_push: stackdata -> instruction

  (* Flow control *)
  | Op_nop: instruction
  | Op_if: instruction
  | Op_notif: instruction
  | Op_else: instruction
  | Op_endif: instruction
  | Op_verify: instruction
  | Op_return: instruction

  (* Stack *)
  | Op_to_alt_stack: instruction
  | Op_from_alt_stack: instruction
  | Op_ifdup: instruction
  | Op_depth: instruction
  | Op_drop: instruction
  | Op_dup: instruction
  | Op_nip: instruction
  | Op_over: instruction
  | Op_pick: Z -> instruction
  | Op_roll: Z -> instruction
  | Op_rot: instruction
  | Op_swap: instruction
  | Op_tuck: instruction
  | Op_2drop: instruction
  | Op_2dup: instruction
  | Op_3dup: instruction
  | Op_2over: instruction
  | Op_2rot: instruction
  | Op_2swap: instruction

  (* Splice *)
  | Op_size: instruction

  (* Bitwise logic *)
  | Op_equal: instruction
  | Op_equalverify: instruction

  (* Arithmetic *)
  | Op_1add: instruction
  | Op_1sub: instruction
  | Op_negate: instruction
  | Op_abs: instruction
  | Op_not: instruction
  (* ... *)

  (* Crypto *)
  | Op_ripemd160: instruction
  | Op_sha1: instruction
  | Op_sha256: instruction
  | Op_hash160: instruction
  | Op_hash256: instruction
  | Op_codeseparator: instruction
  | Op_checksig: instruction
  (* ... *)
  .

Inductive state : Type :=
  | running:
    forall (stack: list stackdata)
           (altstack: list stackdata),
    state
  | invalid:
    state.

Fixpoint is_false (v: stackdata) : bool :=
  (* Not quite right: need to account for negative-zero? *)
  match v with
  | nil => true
  | a::b => if Z.eqb a 0%Z then is_false b else false
  end.

Definition is_true (v: stackdata) : bool :=
  if is_false v then false else true.

Fixpoint stackdata_eqb (a: stackdata) (b: stackdata) : bool :=
  match a with
  | nil =>
    match b with
    | nil => true
    | _ => false
    end
  | ahd::atl =>
    match b with
    | nil => false
    | bhd::btl => if Z.eqb ahd bhd then stackdata_eqb atl btl else false
    end
  end.

Parameter transaction: Type.

Parameter sha256: stackdata -> stackdata.
Parameter ripemd160: stackdata -> stackdata.
Parameter checksig: transaction -> transaction -> stackdata (* sig *) -> stackdata (* pubkey *) -> bool.

Definition step_stacks (stk: list stackdata) (alt: list stackdata) (txprev: transaction) (txnew: transaction) (inst: instruction) : state :=
  match inst with
  | Op_dup =>
    match stk with
    | top::rest => running (top::top::rest) alt
    | nil => invalid
    end
  | Op_push d => running (d::stk) alt
  | Op_return => invalid
  | Op_verify =>
    match stk with
    | top::rest =>
      if is_true top then running rest alt else invalid
    | nil => invalid
    end
  | Op_equal =>
    match stk with
    | a::b::rest => running ((if stackdata_eqb a b then [1%Z] else [0%Z])::rest) alt
    | _ => invalid
    end
  | Op_ripemd160 =>
    match stk with
    | top::rest => running ((ripemd160 top)::rest) alt
    | _ => invalid
    end
  | Op_sha256 =>
    match stk with
    | top::rest => running ((sha256 top)::rest) alt
    | _ => invalid
    end
  | Op_hash160 =>
    match stk with
    | top::rest => running ((ripemd160 (sha256 top))::rest) alt
    | _ => invalid
    end
  | Op_checksig =>
    match stk with
    | pubkey::sig::rest => running ((if checksig txprev txnew sig pubkey then [1%Z] else [0%Z])::rest) alt
    | _ => invalid
    end
  | _ => invalid
  end.

Definition step (txprev: transaction) (txnew: transaction) (s: state) (inst: instruction) : state :=
  match s with
  | invalid => invalid
  | running stk alt => step_stacks stk alt txprev txnew inst
  end.

