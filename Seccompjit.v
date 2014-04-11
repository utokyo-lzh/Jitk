Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Seccomp.

Parameter seccomp_memwords: Z.

Definition reg_a:   ident := 1%positive.
Definition reg_x:   ident := 2%positive.
Definition reg_mem: ident := 3%positive.

Open Local Scope error_monad_scope.

Definition transl_op (op: Seccomp.alu) : Cminor.expr :=
  match op with
  | Aaddimm k => Ebinop Oadd (Evar reg_a) (Econst (Ointconst k))
  | Asubimm k => Ebinop Osub (Evar reg_a) (Econst (Ointconst k))
  | Amulimm k => Ebinop Omul (Evar reg_a) (Econst (Ointconst k))
  | Adivimm k => Ebinop Odivu (Evar reg_a) (Econst (Ointconst k))
  | Amodimm k => Ebinop Omodu (Evar reg_a) (Econst (Ointconst k))
  | Aandimm k => Ebinop Oand (Evar reg_a) (Econst (Ointconst k))
  | Aorimm k => Ebinop Oor (Evar reg_a) (Econst (Ointconst k))
  | Axorimm k => Ebinop Oxor (Evar reg_a) (Econst (Ointconst k))
  | Alshimm k => Ebinop Oshl (Evar reg_a) (Econst (Ointconst k))
  | Arshimm k => Ebinop Oshru (Evar reg_a) (Econst (Ointconst k))
  | Aadd => Ebinop Oadd (Evar reg_a) (Evar reg_x)
  | Asub => Ebinop Osub (Evar reg_a) (Evar reg_x)
  | Amul => Ebinop Omul (Evar reg_a) (Evar reg_x)
  | Adiv => Ebinop Odivu (Evar reg_a) (Evar reg_x)
  | Amod => Ebinop Omodu (Evar reg_a) (Evar reg_x)
  | Aand => Ebinop Oand (Evar reg_a) (Evar reg_x)
  | Aor => Ebinop Oor (Evar reg_a) (Evar reg_x)
  | Axor => Ebinop Oxor (Evar reg_a) (Evar reg_x)
  | Alsh => Ebinop Oshl (Evar reg_a) (Evar reg_x)
  | Arsh => Ebinop Oshru (Evar reg_a) (Evar reg_x)
  | Aneg => Eunop Onegint (Evar reg_a)
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
  | Salu op =>
    OK (Sassign reg_a (transl_op op))
  | Sjmp_ja k =>
    match nextlbl - (Int.unsigned k) with
    | Zpos p => OK (Sgoto p)
    | _ => Error (msg "Illegal offset")
    end
  | Sjmp_jc cond jt jf =>
    match nextlbl - (Byte.unsigned jt), nextlbl - (Byte.unsigned jf) with
    | Zpos pt, Zpos pf => OK (Sifthenelse (transl_cond cond) (Sgoto pt) (Sgoto pf))
    | _, _ => Error (msg "Illegal offset")
    end
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

Definition transl_funbody (f: Seccomp.function) : res Cminor.stmt :=
  do b <- transl_code f;
  (* FIXME: memset(mem, 0, sizeof(mem)) *)
  let init_a := (Sassign reg_a (Econst (Ointconst Int.zero))) in
  let init_x := (Sassign reg_x (Econst (Ointconst Int.zero))) in
  let init_mem := (Sassign reg_mem (Econst (Oaddrstack Int.zero))) in
  OK (Sseq init_a (Sseq init_x (Sseq init_mem b))).

Definition transl_function (f: Seccomp.function) : res Cminor.function :=
  do body <- transl_funbody f;
  let sig := mksignature nil (Some Tint) cc_default in
  let vars := reg_a::reg_x::reg_mem::nil in
  let stackspace := (Zmult seccomp_memwords 4) in
  OK (Cminor.mkfunction sig nil vars stackspace body).

Local Open Scope string_scope.

Definition transl_fundef (fd: fundef) :=
  match fd with
  | Internal f => do f' <- transl_function f; OK (Internal f')
  | External ef => Error (msg "no external function allowed")
  end.

Definition transl_program (p: Seccomp.program) : res Cminor.program :=
  transform_partial_program transl_fundef p.
