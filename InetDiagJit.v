Require Import compcert.backend.Cminor.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import InetDiag.
Require Import InetDiagConf.
Import ListNotations.

Open Local Scope error_monad_scope.

Definition reg_entry: ident := 1%positive.

Definition transl_load_field (f: field) : Cminor.expr :=
  match f with
  | (ty, offset) =>
    let addr := Ebinop Oadd (Evar reg_entry) (Econst (Ointconst (Int.repr offset))) in
    Eload ty addr
  end.

Definition transl_jmp (loc: location) (nextlbl: nat) : Cminor.stmt :=
  match loc with
  | Reject => Sreturn (Some (Econst (Ointconst Int.zero)))
  | Loc n => Sgoto (P_of_succ_nat (nextlbl - n - 1))
  end.

Definition transl_cond (cond: InetDiag.condition) :=
  let v := transl_load_field (cond_field cond) in
  match cond with
  | Sge p => Ebinop (Ocmpu Cge) v (Econst (Ointconst p))
  | Sle p => Ebinop (Ocmpu Cle) v (Econst (Ointconst p))
  | Dge p => Ebinop (Ocmpu Cge) v (Econst (Ointconst p))
  | Dle p => Ebinop (Ocmpu Cle) v (Econst (Ointconst p))
  end.

Definition transl_instr (instr: instruction) (nextlbl: nat) : Cminor.stmt :=
  match instr with
  | Nop => Sskip
  | Jmp loc => transl_jmp loc nextlbl
  | Cjmp cond loc => Sifthenelse (transl_cond cond) Sskip (transl_jmp loc nextlbl)
  end.

Fixpoint transl_code (c: code) : res Cminor.stmt :=
  match c with
  | nil => OK (Sreturn (Some (Econst (Ointconst Int.one))))
  | instr :: rest =>
    let n := length rest in
    do ts <- transl_code rest;
    let hs := transl_instr instr (S n) in
    OK (Sseq hs (Slabel (P_of_succ_nat n) ts))
  end.

Definition transl_function (f: function) : res Cminor.function :=
  do body <- transl_code f;
  let params := [ reg_entry ] in
  let vars := [] in
  let stackspace := 0 in
  OK (Cminor.mkfunction signature_main params vars stackspace body).

Definition transl_fundef (fd: fundef) : res Cminor.fundef :=
  match fd with
  | Internal f => do f' <- transl_function f; OK (Internal f')
  | External f => Error (msg "no external function allowed")
  end.

Definition transl_program (p: program) : res Cminor.program :=
  transform_partial_program transl_fundef p.

Definition example1 :=
  [ Cjmp (Sge (Int.repr 21)) Reject
  ; Cjmp (Sge (Int.repr 1024)) (Loc 1)
  ; Jmp Reject
  ; Nop
  ].
