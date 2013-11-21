Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.Memdata.

Inductive instruction : Type :=
  | ld_w_abs : int -> instruction
  | ld_h_abs : int -> instruction
  | ld_b_abs : int -> instruction
  | ld_w_len : instruction
  | ld_imm   : int -> instruction
  | ld_mem   : int -> instruction
  | ldx_w_imm: int -> instruction
  | ldx_w_mem: int -> instruction
  | ldx_w_len: instruction
  | ldx_b_msh: int -> instruction
  | st       : int -> instruction
  | stx      : int -> instruction
  | add_k    : int -> instruction
  | add_x    : instruction
  | ja       : int -> instruction
  | jeq_k    : Byte.int -> Byte.int -> int -> instruction
  | jeq_x    : Byte.int -> Byte.int -> instruction
  | ret_k    : int -> instruction
  | ret_a    : instruction
  | tax      : instruction
  | txa      : instruction
  .

Record state : Type := mkstate {
  A   : int;
  X   : int;
  mem : ZMap.t int;
  pc  : Z
}.

Definition empty_state := mkstate Int.zero Int.zero (ZMap.init Int.zero) 0.

Definition program := list instruction.

Definition packet := list byte.

Definition instruction_at (p: program) (st: state) :=
  list_nth_z p st.(pc).

Definition packet_length (b: packet) : Z :=
  list_length_z b.

Definition rev_if_le (l: packet) : packet :=
  if big_endian then l else List.rev l.

Fixpoint packet_firstn (n: Z) (b: packet) : packet :=
  if zeq n 0 then nil else match b with
  | nil => nil
  | hd::tl => hd::(packet_firstn (Z.pred n) tl)
  end.

Fixpoint packet_skipn (n: Z) (b: packet) : packet :=
  if zeq n 0 then b else match b with
  | nil => nil
  | hd::tl => packet_skipn (Z.pred n) tl
  end.

Definition packet_decode_int (pos: int) (len: Z) (b: packet) : option int :=
  let s := packet_firstn len (packet_skipn (Int.unsigned pos) b) in
  if zeq (packet_length s) len
  then Some (Int.repr (int_of_bytes (rev_if_le s)))
  else None.

Fixpoint interpret (fuel: nat) (p: program) (b: packet) (st: state) : state * int :=
  match fuel with
  | O => (st, Int.zero)
  | S fuel' => match instruction_at p st with
    | Some (ld_w_abs k) =>
      match packet_decode_int k 4 b with
      | None => (st, Int.zero)
      | Some v => interpret fuel' p b (mkstate v st.(X) st.(mem) (st.(pc) + 1))
      end
    | Some (ld_h_abs k) =>
      match packet_decode_int k 2 b with
      | None => (st, Int.zero)
      | Some v => interpret fuel' p b (mkstate v st.(X) st.(mem) (st.(pc) + 1))
      end
    | Some (ld_b_abs k) =>
      match packet_decode_int k 1 b with
      | None => (st, Int.zero)
      | Some v => interpret fuel' p b (mkstate v st.(X) st.(mem) (st.(pc) + 1))
      end
    | Some (ld_w_len) =>
      interpret fuel' p b (mkstate (Int.repr (packet_length b)) st.(X) st.(mem) (st.(pc) + 1))
    | Some (ld_imm k) =>
      interpret fuel' p b (mkstate k st.(X) st.(mem) (st.(pc) + 1))
    | Some (ld_mem k) =>
      interpret fuel' p b (mkstate (ZMap.get (Int.unsigned k) st.(mem)) st.(X) st.(mem) (st.(pc) + 1))
    | Some (st k) =>
      interpret fuel' p b (mkstate st.(A) st.(X) (ZMap.set (Int.unsigned k) st.(A) st.(mem)) (st.(pc) + 1))
    | Some (stx k) =>
      interpret fuel' p b (mkstate st.(A) st.(X) (ZMap.set (Int.unsigned k) st.(X) st.(mem)) (st.(pc) + 1))
    | Some (add_k k) =>
      interpret fuel' p b (mkstate (Int.add st.(A) k) st.(X) st.(mem) (st.(pc) + 1))
    | Some (add_x) =>
      interpret fuel' p b (mkstate (Int.add st.(A) st.(X)) st.(X) st.(mem) (st.(pc) + 1))
    | Some (ja k) =>
      interpret fuel' p b (mkstate st.(A) st.(X) st.(mem) (st.(pc) + 1 + (Int.unsigned k)))
    | Some (jeq_k jt jf k) =>
      interpret fuel' p b (mkstate st.(A) st.(X) st.(mem) (st.(pc) + 1 + (Byte.unsigned (if (Int.eq st.(A) k) then jt else jf))))
    | Some (jeq_x jt jf) =>
      interpret fuel' p b (mkstate st.(A) st.(X) st.(mem) (st.(pc) + 1 + (Byte.unsigned (if (Int.eq st.(A) st.(X)) then jt else jf))))
    | Some (ret_k k) => (st, k)
    | Some (ret_a) => (st, st.(A))
    | Some (tax) =>
      interpret fuel' p b (mkstate st.(A) st.(A) st.(mem) (st.(pc) + 1))
    | Some (txa) =>
      interpret fuel' p b (mkstate st.(X) st.(X) st.(mem) (st.(pc) + 1))
    | _ => (st, Int.zero)
    end
  end.

Definition interpret_main (p: program) (b: packet) :=
  snd (interpret (length p) p b empty_state).

(*     ldh [12]
       jeq #ETHERTYPE_IP, L1, L2
   L1: ret #TRUE
   L2: ret #0
 *)
Definition prog1 := 
  (ld_h_abs (Int.repr 12))::        
  (jeq_k Byte.zero Byte.one (Int.repr 2048))::
  (ret_k Int.mone)::
  (ret_k Int.zero)::nil.
