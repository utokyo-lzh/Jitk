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
  forall l:list A,
  forall n,
  (n <= (length l))%nat ->
  length (skipn n l) = ((length l) - n)%nat.
Proof.
  intros.
  rewrite <- (firstn_skipn n l) at 2.
  rewrite app_length.
  rewrite firstn_length.
  rewrite min_l; crush.
Qed.

Lemma length_skipn_lt:
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

Lemma mod0_lt_le:
  forall a b m,
  m>0 -> (m|a) -> (m|b) ->
  a < b -> m <= b - a.
Proof.
  intros.
  assert (a = m*(a/m)).  apply Znumtheory.Zdivide_Zdiv_eq; crush.
  assert (b = m*(b/m)).  apply Znumtheory.Zdivide_Zdiv_eq; crush.
  rewrite H3 in *.  rewrite H4 in *.
  clear H3.  clear H4.
  clear H0.  clear H1.
  rewrite <- Z.mul_sub_distr_l.
  rewrite <- Z.mul_1_r at 1.
  apply Zmult_le_compat_l; [ idtac | crush ].
  apply Z.lt_pred_le.
  apply Z.lt_0_sub.
  apply Z.mul_lt_mono_pos_l with (p:=m); crush.
Qed.

Lemma list_eq:
  forall A:Type,
  forall l l' (x x':A),
  l = l' -> x = x' ->
  x :: l = x' :: l'.
Proof.
  crush.
Qed.

Lemma byte_div_zero:
  forall b,
  Byte.unsigned b / 256 = 0.
Proof.
  intros.
  rewrite Zdiv_small; auto; apply Byte.unsigned_range.
Qed.

Lemma le_pow_pos:
  forall a b x y,
  (x < y)%positive ->
  0 <= a -> 0 <= b ->
  a < Z.pow_pos 2 x ->
  b < Z.pow_pos 2 (y-x) ->
  a + b * (Z.pow_pos 2 x) < Z.pow_pos 2 y.
Proof.
  admit.
Qed.

Lemma wtf_32_8:
  (32 - 8 - 8 - 8 = 8)%positive.
Proof.
  crush.
Qed.

Lemma quad_byte_range:
  forall b0 b1 b2 b3,
  0 <= Byte.unsigned b0 +
      (Byte.unsigned b1 +
      (Byte.unsigned b2 +
      (Byte.unsigned b3 + 0) * 256) * 256) * 256 < Int.modulus.
Proof.
  intros.
  destruct (Byte.unsigned_range b0).
  destruct (Byte.unsigned_range b1).
  destruct (Byte.unsigned_range b2).
  destruct (Byte.unsigned_range b3).

  split; [ crush | idtac ].
  assert (256 = Byte.modulus); [ crush | idtac ].
  unfold Byte.modulus in *; unfold Byte.wordsize in *; unfold Wordsize_8.wordsize in *.
  rewrite two_power_nat_equiv in *; simpl in *.
  rewrite H7.

  unfold Int.modulus; unfold Int.wordsize; unfold Wordsize_32.wordsize.
  rewrite two_power_nat_equiv; simpl.
  repeat apply le_pow_pos; zify; try rewrite wtf_32_8; try omega;
    try apply Z.add_nonneg_nonneg; try rewrite H7; crush.
Qed.

Lemma decode_encode_int_4:
  forall l,
  (length l = 4)%nat ->
  encode_int 4 (Int.unsigned (Int.repr (decode_int l))) = l.
Proof.
  destruct l; [ crush | idtac ].
  destruct l; [ crush | idtac ].
  destruct l; [ crush | idtac ].
  destruct l; [ crush | idtac ].
  destruct l; [ idtac | crush ].
  intros Hxx; clear Hxx.
  assert (Byte.modulus = 256); crush.
  unfold decode_int; unfold encode_int.
  unfold rev_if_be.
  destruct Archi.big_endian.
  - simpl.  rewrite Int.unsigned_repr_eq.  rewrite Zmod_small; [ idtac | apply quad_byte_range ].
    repeat apply list_eq; auto; apply Byte.eqm_repr_eq;
      unfold Byte.eqm; unfold Byte.eqmod; rewrite H;
      repeat ( rewrite Z_div_plus_full; [ rewrite byte_div_zero; simpl | discriminate ] );
      rewrite Z.add_comm;
      [ exists (Byte.unsigned i1 + (Byte.unsigned i0 + (Byte.unsigned i + 0) * 256) * 256)
      | exists (Byte.unsigned i0 + (Byte.unsigned i + 0) * 256)
      | exists (Byte.unsigned i + 0)
      | exists 0 ];
      crush.
  - simpl.  rewrite Int.unsigned_repr_eq.  rewrite Zmod_small; [ idtac | apply quad_byte_range ].
    repeat apply list_eq; auto; apply Byte.eqm_repr_eq;
      unfold Byte.eqm; unfold Byte.eqmod; rewrite H;
      repeat ( rewrite Z_div_plus_full; [ rewrite byte_div_zero; simpl | discriminate ] );
      rewrite Z.add_comm;
      [ exists 0
      | exists (Byte.unsigned i2 + 0)
      | exists (Byte.unsigned i1 + (Byte.unsigned i2 + 0) * 256)
      | exists (Byte.unsigned i0 + (Byte.unsigned i1 + (Byte.unsigned i2 + 0) * 256) * 256) ];
      crush.
Qed.

Definition mem_inj := Mem.mem_inj inject_id.

Lemma inj_refl:
  forall m, mem_inj m m.
Proof.
  intros.
  constructor; intros; unfold inject_id in H; inv H.

  replace (ofs + 0) with ofs by omega.
  auto.

  apply Z.divide_0_r.

  replace (ofs + 0) with ofs by omega.
  apply memval_lessdef_refl.
Qed.

Lemma inj_trans:
  forall m1 m2 m3,
  mem_inj m1 m2 -> mem_inj m2 m3 -> mem_inj m1 m3.
Proof.
  unfold mem_inj.
  apply Mem.mem_inj_compose.
Qed.

Lemma free_alloc_inj:
  forall m1 m2 b lo hi m2',
  Mem.alloc m1 lo hi = (m2, b) ->
  Mem.free m2 b lo hi = Some m2' ->
  mem_inj m1 m2'.
Proof.
  intros.
  apply (Mem.free_right_inj inject_id m1 m2 b lo hi m2').
  apply (Mem.alloc_right_inj inject_id m1 m1 lo hi b m2).
  exact (inj_refl m1). auto. auto.

  intros.
  apply (Mem.fresh_block_alloc m1 lo hi m2 b).
  auto.
  apply (Mem.perm_valid_block m1 b') in H2.
  unfold inject_id in H1.
  inv H1.
  auto.
Qed.
