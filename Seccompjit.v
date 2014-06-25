Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Seccomp.
Require Import Seccompconf.
Import ListNotations.

Definition reg_pkt: ident := 1%positive.
Definition reg_a:   ident := 2%positive.
Definition reg_x:   ident := 3%positive.

Open Local Scope error_monad_scope.

Definition transl_alu_safe (op: Seccomp.alu_safe) : Cminor.expr :=
  match op with
  | Aaddimm k => Ebinop Oadd (Evar reg_a) (Econst (Ointconst k))
  | Asubimm k => Ebinop Osub (Evar reg_a) (Econst (Ointconst k))
  | Amulimm k => Ebinop Omul (Evar reg_a) (Econst (Ointconst k))
  | Aandimm k => Ebinop Oand (Evar reg_a) (Econst (Ointconst k))
  | Aorimm k => Ebinop Oor (Evar reg_a) (Econst (Ointconst k))
  | Axorimm k => Ebinop Oxor (Evar reg_a) (Econst (Ointconst k))
  | Aadd => Ebinop Oadd (Evar reg_a) (Evar reg_x)
  | Asub => Ebinop Osub (Evar reg_a) (Evar reg_x)
  | Amul => Ebinop Omul (Evar reg_a) (Evar reg_x)
  | Aand => Ebinop Oand (Evar reg_a) (Evar reg_x)
  | Aor => Ebinop Oor (Evar reg_a) (Evar reg_x)
  | Axor => Ebinop Oxor (Evar reg_a) (Evar reg_x)
  | Aneg => Eunop Onegint (Evar reg_a)
  end.

Definition transl_alu_div (op: Seccomp.alu_div) : Cminor.expr :=
  match op with
  | Adivimm k => Ebinop Odivu (Evar reg_a) (Econst (Ointconst k))
  | Amodimm k => Ebinop Omodu (Evar reg_a) (Econst (Ointconst k))
  | Adiv      => Ebinop Odivu (Evar reg_a) (Evar reg_x)
  | Amod      => Ebinop Omodu (Evar reg_a) (Evar reg_x)
  end.

Definition transl_alu_div_guard (op: Seccomp.alu_div) : Cminor.expr :=
  match op with
  | Adivimm k => Econst (Ointconst k)
  | Amodimm k => Econst (Ointconst k)
  | Adiv      => Evar reg_x
  | Amod      => Evar reg_x
  end.

Definition transl_alu_shift (op: Seccomp.alu_shift) : Cminor.expr :=
  match op with
  | Alshimm k => Ebinop Oshl (Evar reg_a) (Econst (Ointconst k))
  | Arshimm k => Ebinop Oshru (Evar reg_a) (Econst (Ointconst k))
  | Alsh      => Ebinop Oshl (Evar reg_a) (Evar reg_x)
  | Arsh      => Ebinop Oshru (Evar reg_a) (Evar reg_x)
  end.

Definition transl_alu_shift_guard (op: Seccomp.alu_shift) : Cminor.expr :=
  match op with
  | Alshimm k => Econst (Ointconst k)
  | Arshimm k => Econst (Ointconst k)
  | Alsh      => Evar reg_x
  | Arsh      => Evar reg_x
  end.

Definition transl_cond (cond: Seccomp.condition) :=
  match cond with
  | Jsetimm k => Ebinop Oand (Evar reg_a) (Econst (Ointconst k))
    (* A & k *)
  | Jgtimm k => Ebinop (Ocmpu Cgt) (Evar reg_a) (Econst (Ointconst k))
    (* A > k *)
  | Jgeimm k => Ebinop (Ocmpu Cge) (Evar reg_a) (Econst (Ointconst k))
    (* A >= k *)
  | Jeqimm k => Ebinop (Ocmpu Ceq) (Evar reg_a) (Econst (Ointconst k))
    (* A == k *)
  | Jset => Ebinop Oand (Evar reg_a) (Evar reg_x)
    (* A & X *)
  | Jgt => Ebinop (Ocmpu Cgt) (Evar reg_a) (Evar reg_x)
    (* A > X *)
  | Jge => Ebinop (Ocmpu Cge) (Evar reg_a) (Evar reg_x)
    (* A >= X *)
  | Jeq => Ebinop (Ocmpu Ceq) (Evar reg_a) (Evar reg_x)
    (* A == X *)
  end.

Definition transl_instr (instr: Seccomp.instruction)
                        (nextlbl: Z) : res Cminor.stmt :=
  match instr with
  | Salu_safe op =>
    OK (Sassign reg_a (transl_alu_safe op))
  | Salu_div op =>
    OK (Sifthenelse (Ebinop (Ocmpu Ceq) (transl_alu_div_guard op)
                                        (Econst (Ointconst Int.zero)))
                    (Sassign reg_a (Econst (Ointconst Int.zero)))
                    (Sassign reg_a (transl_alu_div op)))
  | Salu_shift op =>
    OK (Sifthenelse (Ebinop (Ocmpu Clt) (transl_alu_shift_guard op)
                                        (Econst (Ointconst Int.iwordsize)))
                    (Sassign reg_a (transl_alu_shift op))
                    (Sassign reg_a (Econst (Ointconst Int.zero))))
  | Sjmp_ja k =>
    OK (Sgoto (Z.to_pos (nextlbl - (Int.unsigned k))))
  | Sjmp_jc cond jt jf =>
    OK (Sifthenelse (transl_cond cond)
          (Sgoto (Z.to_pos (nextlbl - (Byte.unsigned jt))))
          (Sgoto (Z.to_pos (nextlbl - (Byte.unsigned jf)))))
  | Sld_w_abs k =>
    let addr := Ebinop Oadd (Evar reg_pkt) (Econst (Ointconst k)) in
    OK (Sassign reg_a (Eload Mint32 addr))
  | Sld_w_len =>
    OK (Sassign reg_a (Econst (Ointconst (Int.repr sizeof_seccomp_data))))
  | Sldx_w_len =>
    OK (Sassign reg_x (Econst (Ointconst (Int.repr sizeof_seccomp_data))))
  | Sld_mem k =>
    let ofs := Int.mul (Int.repr 4) k in
    let addr := Econst (Oaddrstack ofs) in
    OK (Sassign reg_a (Eload Mint32 addr))
  | Sret_a =>
    OK (Sreturn (Some (Evar reg_a)))
  | Sret_k k =>
    OK (Sreturn (Some (Econst (Ointconst k))))
  | _ => Error (msg "FIXME")
  end.

Fixpoint transl_code (c: Seccomp.code) : res Cminor.stmt :=
  match c with
  | nil => OK Sskip
  | hd::tl =>
    let n := length tl in
    do t <- transl_code tl;
    do h <- transl_instr hd (Z_of_nat (S n));
    OK (Sseq h (Slabel (P_of_succ_nat n) t))
  end.

(*
Fixpoint memzero (n: nat) :=
  let addr := Econst (Oaddrstack (Int.repr (4 * (Z.of_nat n)))) in
  let v := Econst (Ointconst Int.zero) in
  let s := Sstore Mint32 addr v in
  match n with
  | O => s
  | S n' => Sseq (memzero n') s
  end.
*)

Definition transl_funbody (f: Seccomp.function) : res Cminor.stmt :=
  do b <- transl_code f;
  let init_a := (Sassign reg_a (Econst (Ointconst Int.zero))) in
  let init_x := (Sassign reg_x (Econst (Ointconst Int.zero))) in
  OK (Sseq init_a (Sseq init_x b)).

Definition transl_function (f: Seccomp.function) : res Cminor.function :=
  do body <- transl_funbody f;
  let params := [ reg_pkt ] in
  let vars := [ reg_a; reg_x ] in
  let stackspace := 4 * seccomp_memwords in
  OK (Cminor.mkfunction signature_main params vars stackspace body).

Definition transl_fundef (fd: Seccomp.fundef) :=
  match fd with
  | Internal f => do f' <- transl_function f; OK (Internal f')
  | External ef => Error (msg "no external function allowed")
  end.

Definition transl_program (p: Seccomp.program) : res Cminor.program :=
  transform_partial_program transl_fundef p.

(* Transforming from Cminorp to Cminor.. *)

Definition wrap_funbody (b: Cminor.stmt) : Cminor.stmt :=
  (Sseq (Scall (Some reg_pkt) signature_populate
               (Econst (Oaddrsymbol populate_id Int.zero)) nil)
        b).

Definition wrap_function (f: Cminor.function) : Cminor.function :=
  let sig := mksignature nil (Some Tint) cc_default in
  let vars := [ reg_a; reg_x; reg_pkt ] in
  let stackspace := 4 * seccomp_memwords in
  let body := wrap_funbody f.(fn_body) in
  Cminor.mkfunction sig nil vars stackspace body.

Definition wrap_fundef (fd: Cminor.fundef) :=
  match fd with
  | Internal f => Internal (wrap_function f)
  | External e => External e
  end.

Definition wrap_cminorp (p: Cminor.program) : Cminor.program :=
  transform_program wrap_fundef p.
