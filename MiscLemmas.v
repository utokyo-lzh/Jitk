Require Import compcert.common.AST.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import CpdtTactics.

Lemma list_length_nat_z:
  forall A:Type,
  forall l:list A,
  list_length_z l = Z.of_nat (length l).
Proof.
  induction l.
  - crush.
  - rewrite list_length_z_cons; rewrite IHl.
    unfold length.
    rewrite Nat2Z.inj_succ.
    crush.
Qed.

Lemma length_skipn:
  forall A:Type,
  forall x,
  forall l:list A,
  (length (skipn x l) <= length l)%nat.
Proof.
  induction x.
  - crush.
  - induction l; crush.
Qed.

Lemma length_inj_bytes:
  forall l,
  length (Memdata.inj_bytes l) = length l.
Proof.
  induction l; crush.
Qed.

Lemma firstn_inj_bytes:
  forall n l,
  firstn n (Memdata.inj_bytes l) = Memdata.inj_bytes (firstn n l).
Proof.
  induction n.
  - crush.
  - destruct l.
    + crush.
    + crush.
Qed.

Lemma skipn_inj_bytes:
  forall n l,
  skipn n (Memdata.inj_bytes l) = Memdata.inj_bytes (skipn n l).
Proof.
  induction n.
  - crush.
  - destruct l.
    + crush.
    + crush.
Qed.

Lemma oversize_shl_zero:
  forall a i,
  Int.ltu i Int.iwordsize = false ->
  Int.shl a i = Int.zero.
Proof.
  intros.
  rewrite Int.shl_mul_two_p.
  assert (Int.repr (two_p (Int.unsigned i)) = Int.zero).
   apply Int.eqm_samerepr.
   unfold Int.eqm.
   assert (two_p (Int.unsigned i) mod Int.modulus = 0).
    apply Zmod_divides.
     assert (Int.modulus > 0).
      exact Int.wordsize_pos.

      omega.

     exists (two_p (Int.unsigned i - Int.zwordsize)).
     unfold Int.ltu in H.
     destruct (zlt (Int.unsigned i) (Int.unsigned Int.iwordsize)).
      discriminate.

      assert (0 <= Int.zwordsize).
       apply Zlt_le_weak.
       apply Zgt_lt.
       exact Int.wordsize_pos.

       assert (0 <= Int.unsigned i - Int.zwordsize).
        rewrite Int.unsigned_repr_wordsize in *.
        apply Zle_minus_le_0.
        omega.

        assert
         (two_p (Int.zwordsize + (Int.unsigned i - Int.zwordsize)) =
          two_p Int.zwordsize * two_p (Int.unsigned i - Int.zwordsize)).
         apply two_p_is_exp; auto.

         assert
          (Int.zwordsize + (Int.unsigned i - Int.zwordsize) = Int.unsigned i).
          omega.

          rewrite H3 in H2.
          auto.

    assert
     (Int.eqmod Int.modulus (two_p (Int.unsigned i))
        (two_p (Int.unsigned i) mod Int.modulus)).
     apply Int.eqmod_mod.
     exact Int.modulus_pos.

     rewrite H0 in H1.
     auto.

   rewrite H0.
   apply Int.mul_zero.
Qed.

Lemma oversize_shru_zero:
  forall a i,
  Int.ltu i Int.iwordsize = false ->
  Int.shru a i = Int.zero.
Proof.
  intros.
  rewrite Int.shru_div_two_p.
  assert (Int.modulus <= two_p (Int.unsigned i)).

  - rewrite Int.modulus_power.
    apply two_p_monotone.
    crush.
    apply Zlt_le_weak.
    apply Zgt_lt.
    exact Int.wordsize_pos.

    unfold Int.ltu in H.
    destruct (zlt (Int.unsigned i) (Int.unsigned Int.iwordsize)).
    crush.
    apply Zge_le.
    auto.

  - apply Int.eqm_samerepr.
    apply Int.eqm_refl2.
    apply Zdiv_small.

    split.
    apply Int.unsigned_range.
    apply (Zlt_le_trans (Int.unsigned a) Int.modulus (two_p (Int.unsigned i))).
    apply Int.unsigned_range.
    auto.
Qed.

Lemma skipn_more:
  forall A:Type,
  forall n c,
  (n < length c)%nat ->
  exists x:A, skipn n c = x :: skipn (S n) c.
Proof.
  induction n.
  - destruct c.
    + crush.
    + intros.  exists a.  crush.
  - destruct c.
    + simpl.  crush.
    + intros.  apply IHn.  crush.
Qed.

Lemma skipn_nil:
  forall A:Type,
  forall n,
  skipn n nil = @nil A.
Proof.
  induction n; crush.
Qed.

Lemma skipn_last:
  forall A:Type,
  forall n c,
  forall x:A,
  skipn n c = x :: nil -> n = (length c - 1)%nat.
Proof.
  induction n.
  - crush.
  - destruct c.
    + crush.
    + simpl.  intros.  remember (IHn c x H).  clear Heqe.  rewrite e.
      destruct c.
      * rewrite skipn_nil in H.  discriminate.
      * crush.
Qed.

