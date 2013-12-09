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
Require Import Seccompproof.

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


Ltac transl_ok H := apply bind_inversion in H; elim H; clear H;
                    intro; intro X; decompose [and] X; clear X.

Lemma rtl_opcode_for_salu_add_at_0:
  forall a x sm f pc m,
  forall tstack tf tsp tpc tregs tm,
  match_states (Seccomp.State a x sm f pc m)
               (RTL.State tstack tf tsp tpc tregs tm) ->
  forall k,
  pc = 0 ->
  instruction_at f pc = Some (Salu_add_k k) ->
  exists tpc',
  (fn_code tf) ! tpc = Some (Iop (Oaddimm k) (reg_a::nil) reg_a tpc').
Proof.
  intros.
  inversion H; clear H.   (* match_states *)
  unfold transl_function in TF; simpl in TF.
  transl_ok TF; injection H2; clear H2; intros.
  induction f.

  (* case 1: f = nil *)
  simpl in H1; discriminate H1.

  (* case 2: f' = a1::f *)
  rewrite H0 in H1.
  compute in H1; injection H1; clear H1; intros.  (* a1 = Salu_add_k k *)
  rewrite H1 in H.    (* plug Salu_add_k into transl_code *)
  simpl in H.
  transl_ok H; injection H16; clear H16; intros.

  (* plug in the add_map for Oaddimm into (tpc = ZMap.get pc jmap) *)
  symmetry in H16; rewrite H16 in H2.
  symmetry in H2; rewrite H2 in MPC.
  rewrite H0 in MPC; simpl in MPC.    (* plug in pc=0 *)
  rewrite ZMap.gss in MPC.

  rewrite H16 in H15; simpl in H15.
  symmetry in H15; rewrite H15; rewrite MPC; simpl.

  exists (st_ep x2).

  rewrite PTree.gsspec; rewrite peq_false.
  rewrite PTree.gsspec; rewrite peq_false.
  rewrite PTree.gsspec; rewrite peq_false.
  rewrite PTree.gsspec; rewrite peq_true.
  auto.

  (* now prove all of the other writes to fn_code were different *)
  apply Pos.succ_discr.
  apply Plt_ne; apply Plt_trans_succ; apply Plt_succ.
  apply Plt_ne; apply Plt_trans_succ; apply Plt_trans_succ; apply Plt_succ.
Qed.

