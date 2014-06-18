Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.common.Smallstep.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import CpdtTactics.
Require Import cmp.

Import ListNotations.

Definition loadrange (m: mem) (addr len: val): option (list memval) :=
  match addr, len with
  | Vptr b ofs, Vint n => Mem.loadbytes m b (Int.unsigned ofs) (Int.unsigned n)
  | _, _ => None
  end.

Variable s1 s2 n: val.
Definition vargs := [ s2; s2; n ].
Variable k: cont.
Variable m: mem.
Variable ge: genv.
Definition t := E0.

Definition Call (f: function) := Callstate (Internal f) vargs k m.
Definition Return (res: val)  := Returnstate res k m.

Variable b1 b2: list memval.

Hypothesis input_valid:
  loadrange m s1 n = Some b1 /\
  loadrange m s2 n = Some b2.

Ltac crush_list_norepet :=
  repeat match goal with
  | |- list_norepet nil => apply list_norepet_nil
  | |- list_norepet _ => constructor
  | |- ~ In _ _ => simpl; unfold not; intro
  | H: _ |- False => repeat (inv H)
  end.

Ltac crush_list_disjoint :=
  repeat match goal with
  | |- list_disjoint _ _ => unfold list_disjoint; simpl; intros
  | |- ?x <> ?y => unfold not; intros
  | H: _ |- False => repeat (inv H)
  end.

Theorem bcmp_well_defined:
  exists res,
  star step2 ge (Call f_bcmp) t (Return res).
Proof.
  eexists.

  (* function_entry *)
  econstructor. constructor.
  constructor.
    crush_list_norepet.
    crush_list_norepet.
    crush_list_disjoint.
    constructor.
    constructor.

  eapply star_step. constructor.
  eapply star_step. constructor.
  eapply star_step. constructor. constructor.
  eapply star_step. constructor.
  eapply star_step. constructor.
  eapply star_step. constructor.

  eapply star_step. eapply step_ifthenelse.

  econstructor.
  constructor.
  constructor.
  constructor.
  constructor.

(*
  unfold Cop.sem_binary_operation. simpl.
  unfold Cop.sem_cmp. simpl.
  unfold Cop.sem_binarith. simpl.
  unfold Cop.sem_cast. simpl.
  *)
Admitted.


Theorem bmp_correct:
  forall res,
  star step2 ge (Call f_bcmp) t (Return res) ->
  (b1 = b2 <-> res = Vzero).
Proof.
  intros.
  inv H.
  inv H0.   
  inv H1.
  inv H.  
Admitted.

(*
Theorem hashcmp_well_defined:
  exists res,
  star step2 ge (Call f_hashcmp) t (Return res).
Proof.
  eexists.

  (* function_entry *)
  econstructor. constructor.
  constructor.
    crush_list_norepet.
    crush_list_norepet.
    crush_list_disjoint.
    constructor.
    constructor.

  repeat match goal with
  | |- star step2 _ _ _ _  => econstructor
  | |- step2 _ _ _ _ => repeat constructor
  end.

Admitted.

Theorem hashcmp_correct:
  forall res,
  star step2 ge (Call f_hashcmp) t (Return res) ->
  (b1 = b2 <-> res = Vzero).
Proof.
  intros.
*)
