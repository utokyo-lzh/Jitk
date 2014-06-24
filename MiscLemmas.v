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

Lemma iwordsize_zwordsize:
  Int.unsigned Int.iwordsize = Int.zwordsize.
Proof.
  unfold Int.iwordsize.
  rewrite Int.unsigned_repr. reflexivity.
  split; compute; discriminate.
Qed.

Ltac break_if :=
  match goal with
    | [ H : context [ if ?X then _ else _ ] |- _ ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
    | [ |- context [ if ?X then _ else _ ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Lemma oversize_shl_zero:
  forall a i,
  Int.ltu i Int.iwordsize = false ->
  Int.shl a i = Int.zero.
Proof.
  intros.
  apply Int.same_bits_eq.
  intros.
  rewrite Int.bits_zero.
  rewrite Int.bits_shl by auto.
  break_if.
  - reflexivity.
  - (* i0 >= i, i0 < Int.zwordsize, i < iwordsize, thus contra *)
    unfold Int.ltu in *.
    break_if.
    + discriminate.
    + rewrite iwordsize_zwordsize in *.
      omega.
Qed.


Lemma oversize_shru_zero:
  forall a i,
  Int.ltu i Int.iwordsize = false ->
  Int.shru a i = Int.zero.
Proof.
  intros.
  apply Int.same_bits_eq.
  intros.
  rewrite Int.bits_zero.
  rewrite Int.bits_shru by auto.
  break_if.
  - unfold Int.ltu in *.
    break_if.
    + discriminate.
    + rewrite iwordsize_zwordsize in *.
      omega.
  - reflexivity.
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
  intros.
  assert (Z.pow_pos 2 y = (Z.pow_pos 2 x) + (Z.pow_pos 2 y - Z.pow_pos 2 x)); [ crush | idtac ].
  rewrite H4.
  apply Z.add_lt_le_mono; [ auto | idtac ].
  assert (Z.pow_pos 2 y = (Z.pow_pos 2 (y - x)) * (Z.pow_pos 2 x)).
  rewrite <- Zpower_pos_is_exp.
  rewrite Pos.sub_add; crush.
  rewrite H5.
  rewrite <- (Z.mul_1_l (Z.pow_pos 2 x)) at 3.
  rewrite <- Z.mul_sub_distr_r.
  apply Zmult_lt_0_le_compat_r.
  crush.
  crush.
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

Lemma list_length_z_strict_pos:
  forall (A: Type) (hd: A) (tl: list A),
  0 < list_length_z (hd :: tl).
Proof.
  intros.
  rewrite list_length_nat_z.
  crush.
Qed.

Lemma is_tail_exists_prefix:
  forall A:Type,
  forall a b:list A,
  is_tail a b ->
  exists p,
  b = p ++ a.
Proof.
  induction 1.
  - exists nil; auto.
  - inv IHis_tail. exists (i :: x). auto.
Qed.

Lemma is_tail_strict_prefix:
  forall A:Type,
  forall b' b:list A,
  is_tail b' b ->
  list_length_z b' < list_length_z b ->
  exists x:A,
  exists prefix:list A,
  b = prefix ++ (x :: b').
Proof.
  intros.
  destruct (is_tail_exists_prefix A b' b); auto.
  destruct x; crush.
  assert (a::x <> nil); crush.
  destruct (exists_last H1); destruct s.
  exists x1; exists x0.
  rewrite app_comm_cons; rewrite e; crush.
Qed.

Lemma is_tail_skipn:
  forall A:Type,
  forall n,
  forall l:list A,
  is_tail (skipn n l) l.
Proof.
  induction n; [ crush | destruct l; crush ].
Qed.

Lemma list_length_z_skipn:
  forall A:Type,
  forall x,
  forall l:list A,
  list_length_z (skipn x l) <= list_length_z l.
Proof.
  induction x.
  - crush.
  - induction l.
    + crush.
    + rewrite list_length_z_cons.
      crush.
Qed.

Lemma list_length_z_istail':
  forall A:Type,
  forall b l:list A,
  is_tail b l ->
  b <> nil ->
  list_length_z (skipn 1 b) < list_length_z l.
Proof.
  intros A b l H.
  induction H.
  - destruct c; [ crush | rewrite list_length_z_cons; crush ].
  - rewrite list_length_z_cons; crush.
Qed.

Lemma list_length_z_istail:
  forall A:Type,
  forall v:A,
  forall b l:list A,
  is_tail (v :: b) l ->
  list_length_z b < list_length_z l.
Proof.
  intros.
  remember (v::b) as b'.
  cut (b = skipn 1 b').
  - intros; rewrite H0; apply list_length_z_istail'; crush.
  - crush.
Qed.

Lemma psucc_ne:
  forall a b,
  a <> b -> P_of_succ_nat a <> P_of_succ_nat b.
Proof.
  unfold not.
  intros.
  apply H.
  apply SuccNat2Pos.inj.
  auto.
Qed.
