Require Import Coq.ZArith.Zbool.
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
Require Import CpdtTactics.

Variable tprog: RTL.program.
Let tge := Genv.globalenv tprog.

(* leftovers from old Seccompjit.v:

Inductive state_incr: state -> state -> Prop :=
  state_incr_intro:
    forall (s1 s2: state),
    Ple s1.(st_ep) s2.(st_ep) ->
    (forall pc,
      s1.(st_code)!pc = None \/ s2.(st_code)!pc = s1.(st_code)!pc) ->
    state_incr s1 s2.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros.
  apply state_incr_intro.
  apply Ple_refl.
  intros; auto.
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros.
  inv H; inv H0.
  apply state_incr_intro.
  apply Ple_trans with s2.(st_ep); assumption.

  intros.
  generalize (H2 pc) (H3 pc).
  intuition congruence.
Qed.

*)


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

Lemma pred_of_plus_one:
  forall x: Z,
  Z.pred (x + 1) = x.
Proof.
  firstorder.
Qed.

Lemma list_nth_z_last:
  forall (A: Type) (l: list A) (x: A),
  list_nth_z (l ++ (x :: nil)) (list_length_z l) = Some x.
Proof.
  intros.
  induction l.
  auto.
  rewrite list_length_z_cons.
  simpl.
  rewrite pred_of_plus_one.
  rewrite IHl.
  apply zeq_false.
  cut (list_length_z l >= 0).
  firstorder.
  apply list_length_z_pos.
Qed.

Lemma list_length_z_sum:
  forall (A: Type) (a: list A) (b: list A),
  list_length_z (a ++ b) = (list_length_z a) + (list_length_z b).
Proof.
  intros.
  induction a.
  auto.
  simpl.
  unfold list_length_z; unfold list_length_z in IHa; simpl.
  rewrite list_length_z_aux_shift with (m:=0).
  (* why doesn't this work?
  rewrite list_length_z_aux_shift with (m:=0) at 2.
  *)
  assert (list_length_z_aux a0 1 = list_length_z_aux a0 0 + 1).
  apply list_length_z_aux_shift.
  rewrite H.
  firstorder.
Qed.

Lemma list_length_z_rev:
  forall (A: Type) (l: list A),
  list_length_z l = list_length_z (rev l).
Proof.
  induction l.
  auto.
  rewrite list_length_z_cons.
  simpl.
  rewrite list_length_z_sum.
  firstorder.
Qed.

Lemma skipn_plusone_end:
  forall (A:Type) (l:list A) (n:nat),
  skipn n l = nil -> skipn (S n) l = nil.
Proof.
  induction l.
  auto.
  destruct n.
  discriminate 1.
  intros; apply IHl; auto.
Qed.

Lemma skipn_plusone_middle:
  forall (A:Type) (l:list A) (n:nat) (l':list A) (x:A),
  skipn n l = x::l' -> skipn (S n) l = l'.
Proof.
  induction l.
  destruct n; crush.
  destruct n; [ crush | intros; apply IHl with (x:=x); crush ].
Qed.

