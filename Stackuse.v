Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.lib.Coqlib.
Require Import Arch.
Require Import CpdtTactics.
Require Import MiscLemmas.

Open Local Scope error_monad_scope.

Parameter MaxStackSize : Z.

Definition stacksize (f: Asm.function) :=
  match f.(fn_code) with
  | nil => Error (msg "empty function")
  | hd :: tl => match hd with
    | Pallocframe sz _ _ => OK sz
    | _ => Error (msg "missing Pallocframe")
    end
  end.

(* any function from Asmgen should have Pallocframe *)
Lemma stacksize_wf (f: function):
  forall f f', Asmgen.transl_function f' = OK f ->
  exists sz, stacksize f = OK sz.
Proof.
  intros.
  eexists.
  monadInv H.
  crush.
Qed.

Definition check_function (f: Asm.function) :=
  do sz <- stacksize f;
  if (zle sz MaxStackSize) then OK f else Error (msg "stack overflow").

Definition check_fundef (fd: Asm.fundef) :=
  match fd with
  | Internal f => do f' <- check_function f; OK fd
  | External ef => Error (msg "no external function allowed")
  end.

Definition check_program (p: Asm.program) : res Asm.program :=
  transform_partial_program check_fundef p.

Lemma bounded_stack_useage:
  forall f sz, check_function f = OK f ->
  stacksize f = OK sz -> sz <= MaxStackSize.
Proof.
  intros.
  monadInv H.
  assert (x = sz).
  crush.
  rewrite H in *.
  break_if; crush.
Qed.
