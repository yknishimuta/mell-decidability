From Coq Require Import Lia List QArith Qround Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Corollary67Finitary FaceStrippingBases Faces
  MathCompBridge.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Check @ThresholdFace.
Check @RationalThresholdSlice.
Check @integer_ge_rational_iff_ceiling.
Check @integer_eq_rational_iff_two_ceilings.
Check @rational_slice_affine_group_iff.
Check @homogeneous_group_face_period_iff.
Check @corollary_6_7_finitary.

Definition b4_zv1 (value : Z) : ZVec 1 := Vector.of_list [value].
Definition b4_zv2 (left right : Z) : ZVec 2 :=
  Vector.of_list [left; right].
Definition b4_e1 : ZVec 1 := b4_zv1 1.
Definition b4_e21 : ZVec 2 := b4_zv2 1 0.
Definition b4_e22 : ZVec 2 := b4_zv2 0 1.

Lemma b4_zinner_e1 : forall z, zinner b4_e1 (b4_zv1 z) = z.
Proof. intro z. unfold b4_e1, b4_zv1, zinner. destruct z; reflexivity. Qed.

Lemma b4_zinner_e21 : forall x y, zinner b4_e21 (b4_zv2 x y) = x.
Proof. intros x y. unfold b4_e21, b4_zv2, zinner. destruct x; reflexivity. Qed.

Lemma b4_zinner_e22 : forall x y, zinner b4_e22 (b4_zv2 x y) = y.
Proof. intros x y. unfold b4_e22, b4_zv2, zinner. destruct y; reflexivity. Qed.

Example ceiling_half : Qceiling (1 # 2) = 1%Z.
Proof. reflexivity. Qed.

Example ceiling_negative_three_halves : Qceiling (- (3 # 2)) = (-1)%Z.
Proof. reflexivity. Qed.

Example noninteger_threshold_equality_is_empty : forall n : Z,
    ~ inject_Z n == (3 # 2).
Proof.
  intros n Heq.
  apply (proj1 (integer_eq_rational_iff_two_ceilings n (3 # 2))) in Heq.
  cbn in Heq. lia.
Qed.

Definition b4_negative_threshold (_ : ZVec 1) : Q := (-2)%Q.

Example negative_threshold_without_cone_guard_accepts_minus_one :
    AffineSolutions [(b4_e1, (-2)%Z)] (b4_zv1 (-1)).
Proof.
  intros constraint [Heq | Hin]; [subst constraint|inversion Hin].
  unfold b4_e1, b4_zv1, zinner. cbn. lia.
Qed.

Example negative_threshold_cone_guard_rejects_minus_one :
    ~ AffineSolutions
      (rational_threshold_constraints [b4_e1] [] b4_negative_threshold)
      (b4_zv1 (-1)).
Proof.
  intro H. apply (proj1 (affine_rational_threshold_constraints_iff
    1 [b4_e1] [] b4_negative_threshold (b4_zv1 (-1)))) in H.
  destruct H as [Hzero _].
  specialize (Hzero b4_e1 ltac:(now left)).
  unfold b4_e1, b4_zv1, zinner in Hzero. cbn in Hzero. lia.
Qed.

Definition b4_two_nat : ZSet 1 :=
  fun value => exists n : Z, (0 <= n)%Z /\ value = b4_zv1 ((2 * n)%Z).
Definition b4_one_threshold (_ : ZVec 1) : Q := 1.

Example example_A_two_nat_slice : forall z : Z,
    RationalThresholdSlice b4_two_nat [b4_e1] [] b4_one_threshold
      (b4_zv1 z) <->
    exists n : Z, (0 <= n)%Z /\ z = (2 + 2 * n)%Z.
Proof.
  intro z. split.
  - intros [[n [Hn Heq]] [Hlower _]].
    assert (Hz : z = (2 * n)%Z).
    { pose proof (f_equal (fun value => Vector.nth value Fin.F1) Heq) as Hnth.
      unfold b4_zv1 in Hnth. cbn in Hnth. exact Hnth. }
    specialize (Hlower b4_e1 ltac:(now left)).
    apply (proj1 (integer_qinner_ge_rational_iff_ceiling
      1 b4_e1 (b4_zv1 z) 1)) in Hlower.
    unfold b4_e1, b4_zv1, zinner in Hlower. cbn in Hlower.
    ring_simplify in Hlower.
    replace (match z with
      | 0%Z => 0%Z | Z.pos p => Z.pos p | Z.neg p => Z.neg p
      end) with z in Hlower by (destruct z; reflexivity).
    exists (n - 1)%Z. split; lia.
  - intros [n [Hn ->]]. repeat split.
    + exists (n + 1)%Z. split; [lia|].
      replace (2 + 2 * n)%Z with (2 * (n + 1))%Z by ring.
      reflexivity.
    + intros normal [Heq | Hin]; [subst normal|inversion Hin].
      apply (proj2 (integer_qinner_ge_rational_iff_ceiling
        1 b4_e1 (b4_zv1 ((2 + 2 * n)%Z)) 1)).
      rewrite b4_zinner_e1. change (1 <= 2 + 2 * n)%Z. lia.
    + intros normal Hin. inversion Hin.
Qed.

Definition b4_nonnegative2 : ZSet 2 :=
  fun value =>
    (0 <= Vector.hd value)%Z /\ (0 <= Vector.hd (Vector.tl value))%Z.

Definition b4_threshold2 (normal : ZVec 2) : Q :=
  if Z.eqb (Vector.hd normal) 1 then 2 else (1 # 2).

Example example_B_quadrant_slice : forall x y : Z,
    RationalThresholdSlice b4_nonnegative2 [b4_e21; b4_e22] [b4_e21]
      b4_threshold2 (b4_zv2 x y) <-> x = 2%Z /\ (1 <= y)%Z.
Proof.
  intros x y. split.
  - intros [Hperiod [Hlower Hequal]].
    specialize (Hequal b4_e21 ltac:(now left)).
    apply (proj1 (integer_qinner_eq_rational_iff_two_ceilings
      2 b4_e21 (b4_zv2 x y) (b4_threshold2 b4_e21))) in Hequal.
    specialize (Hlower b4_e22 ltac:(now right; left)).
    apply (proj1 (integer_qinner_ge_rational_iff_ceiling
      2 b4_e22 (b4_zv2 x y) (b4_threshold2 b4_e22))) in Hlower.
    rewrite b4_zinner_e21 in Hequal.
    rewrite b4_zinner_e22 in Hlower.
    unfold b4_threshold2, b4_e21, b4_e22, b4_zv2 in Hequal, Hlower.
    cbn in Hequal, Hlower. lia.
  - intros [-> Hy]. split.
    + unfold b4_nonnegative2, b4_zv2. cbn. lia.
    + split.
      * intros normal Hin. destruct Hin as [Heq | [Heq | Hin]].
        -- subst normal. apply (proj2 (integer_qinner_ge_rational_iff_ceiling
            2 b4_e21 (b4_zv2 2 y) (b4_threshold2 b4_e21))).
           rewrite b4_zinner_e21.
           unfold b4_threshold2, b4_e21, b4_zv2. cbn. lia.
        -- subst normal. apply (proj2 (integer_qinner_ge_rational_iff_ceiling
            2 b4_e22 (b4_zv2 2 y) (b4_threshold2 b4_e22))).
           rewrite b4_zinner_e22.
           unfold b4_threshold2, b4_e22, b4_zv2. cbn. lia.
        -- inversion Hin.
      * intros normal [Heq | Hin]; [subst normal|inversion Hin].
        apply (proj2 (integer_qinner_eq_rational_iff_two_ceilings
          2 b4_e21 (b4_zv2 2 y) (b4_threshold2 b4_e21))).
        rewrite b4_zinner_e21.
        unfold b4_threshold2, b4_e21, b4_zv2. cbn. lia.
Qed.

Definition b4_three_halves (_ : ZVec 1) : Q := (3 # 2).

Example example_C_noninteger_tight_slice_empty : forall value : ZVec 1,
    ~ RationalThresholdSlice (fun _ => True) [b4_e1] [b4_e1]
      b4_three_halves value.
Proof.
  intros value [_ [_ Hequal]].
  specialize (Hequal b4_e1 ltac:(now left)).
  pose proof (qinner_zvec_to_qvec 1 b4_e1 value) as Hinner.
  assert (Hinteger : inject_Z (zinner b4_e1 value) == (3 # 2)).
  { transitivity (qinner (zvec_to_qvec b4_e1) (zvec_to_qvec value));
      [symmetry; exact Hinner|exact Hequal]. }
  now apply (noninteger_threshold_equality_is_empty (zinner b4_e1 value)).
Qed.

Example dimension_zero_empty_normals : forall value : ZVec 0,
    RationalThresholdSlice (fun _ => True) [] [] (fun _ => 0) value.
Proof.
  intros value. repeat split; intros normal Hin; inversion Hin.
Qed.

Example empty_tight_keeps_the_full_homogeneous_system : forall value : ZVec 1,
    HomogeneousSolutions
      (rational_threshold_constraints [b4_e1] [] b4_negative_threshold)
      value -> (0 <= zinner b4_e1 value)%Z.
Proof.
  intro value. rewrite homogeneous_rational_threshold_constraints_iff.
  intros [H _]. now apply H; left.
Qed.

Example duplicate_normals_are_preserved :
    length (rational_threshold_constraints [b4_e1; b4_e1]
      [b4_e1; b4_e1] b4_one_threshold) = 6%nat.
Proof. reflexivity. Qed.

Print Assumptions integer_ge_rational_iff_ceiling.
Print Assumptions integer_eq_rational_iff_two_ceilings.
Print Assumptions rational_slice_affine_group_iff.
Print Assumptions homogeneous_group_face_period_iff.
Print Assumptions corollary_6_7_finitary.
