Require Import compcert.backend.RTL.
Require Import compcert.backend.Registers.
Require Import compcert.common.AST.
Require Import compcert.common.Errors.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import Op.
Require Import Seccomp.
Require Import Seccompjit.

Variable tprog: RTL.program.
Let tge := Genv.globalenv tprog.


Definition set_fn (k: int) :=
  let ep0 := 1%positive in
  let code := PTree.empty RTL.instruction in
  let ep1 := Psucc ep0 in
  let code := PTree.set ep1 (Iop (Ointconst k) nil 1%positive ep0) code in
  let sig := mksignature nil (Some Tint) in
  let stacksize := (Zmult seccomp_memwords 4) in
  RTL.mkfunction sig nil stacksize code ep1.

Lemma set_fn_works:
  forall k: int,
  let f0 := set_fn k in
  forall tstack0 tsp0 tregs0 tm0,
  let s0 := RTL.State tstack0 f0 tsp0 f0.(fn_entrypoint) tregs0 tm0 in
  forall tstack1 tsp1 tregs1 tm1 tpc1 f1,
  let s1 := RTL.State tstack1 f1 tsp1 tpc1 tregs1 tm1 in
  RTL.step tge s0 E0 s1 -> (Regmap.get 1%positive tregs1) = (Vint k).
Proof.
  intros.
  inversion H.
  clear H.

  (* RTL.step case: Inop *)
  compute in H1.
  discriminate H1.

  (* RTL.step case: Iop *)
  compute in H2.
  injection H2.
  clear H2.
  intros.
  symmetry in H14.
  rewrite H14.
  rewrite Regmap.gss.
  symmetry in H16.
  rewrite H16 in H13.
  symmetry in H15.
  rewrite H15 in H13.
  unfold eval_operation in H13.
  simpl in H13.
  injection H13.
  auto.

  (* RTL.step case: Iload *)
  compute in H3.
  discriminate H3.

  (* RTL.step case: Istore *)
  compute in H3.
  discriminate H3.

  (* RTL.step case: Ibuiltin *)
  compute in H7.
  discriminate H7.

  (* RTL.step case: Icond *)
  compute in H3.
  discriminate H3.

  (* RTL.step case: Ijumptable *)
  compute in H3.
  discriminate H3.
Qed.


Ltac compdisc H := compute in H; discriminate H.

Definition add_fn (k: int) :=
  let ep0 := 1%positive in
  let code := PTree.empty RTL.instruction in
  let ep1 := Psucc ep0 in
  let code := PTree.set ep1 (Iop (Oaddimm k) (1%positive::nil) 1%positive ep0) code in
  let sig := mksignature nil (Some Tint) in
  let stacksize := (Zmult seccomp_memwords 4) in
  RTL.mkfunction sig nil stacksize code ep1.

Lemma add_fn_works:
  forall x: int,
  forall k: int,
  let f0 := add_fn k in
  forall tstack0 tsp0 tregs0 tm0,
  let s0 := RTL.State tstack0 f0 tsp0 f0.(fn_entrypoint) tregs0 tm0 in
  forall tstack1 tsp1 tregs1 tm1 tpc1 f1,
  let s1 := RTL.State tstack1 f1 tsp1 tpc1 tregs1 tm1 in
  RTL.step tge s0 E0 s1 ->
  (Regmap.get 1%positive tregs0) = (Vint x) ->
  (Regmap.get 1%positive tregs1) = (Vint (Int.add x k)).
Proof.
  intros.
  inversion H; clear H.   (* expand out RTL.step *)
  compdisc H2.            (* Inop *)

  (* Iop *)
  compute in H3; injection H3; clear H3.            (* match fn_code *)
  intros.
  symmetry in H16; rewrite H16 in H14; clear H16.   (* op *)
  symmetry in H15; rewrite H15 in H14; clear H15.   (* args *)
  simpl in H14.
  rewrite H0 in H14.                                (* tregs0!!1 *)
  simpl in H14; injection H14; intros.
  rewrite H15; clear H15.                           (* x+k=v *)
  symmetry in H13; rewrite H3.                      (* res *)
  rewrite Regmap.gss.
  auto.

  compdisc H4.            (* Iload *)
  compdisc H4.            (* Istore *)
  compdisc H8.            (* Ibuiltin *)
  compdisc H4.            (* Icond *)
  compdisc H4.            (* Ijumptable *)
Qed.

