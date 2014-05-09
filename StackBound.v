(* CompCert's Asm doesn't really manipulate SP - instead, it allocates
 * a linked list of stack memory, and the allocations never fail, as
 * in the formal semantics.  It's just that PrintAsm.ml magically prints
 * instructions that change ESP, which is never proved.  Therefore,
 * there's no point for checking for stack overflow in current CompCert,
 * though one could use this file at the end of Asm generation to "bound"
 * stack usage.
 *)

Require Import Asm.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.lib.Coqlib.

Parameter MaxStackSize : Z.

Open Local Scope error_monad_scope.

Definition check_function (f: Asm.function) : res Asm.function :=
  match f.(fn_code) with
  | (Pallocframe sz _ _)::tl => if sz <=? MaxStackSize then OK f else Error (msg "stack overflow")
  | _ => Error (msg "illegal function")
  end.

Definition check_fundef (fd: Asm.fundef) :=
  match fd with
  | Internal f => do f' <- check_function f; OK fd
  | External ef => Error (msg "no external function allowed")
  end.

Definition check_program (p: Asm.program) : res Asm.program :=
  transform_partial_program check_fundef p.
