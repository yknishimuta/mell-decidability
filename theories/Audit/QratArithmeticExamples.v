From Coq Require Import QArith ZArith Lia.
From mathcomp Require Import all_ssreflect all_algebra.
From Mell.Geometry Require Import QratAdapter.

Import GRing.Theory Num.Theory.

Set Printing Implicit.

Check @z_to_int_zero.
Check @z_to_int_one.
Check @z_to_int_add.
Check @z_to_int_sub.
Check @z_to_int_mul.
Check @z_to_int_le_iff.
Check @z_to_int_lt_iff.
Check @z_to_int_nonnegative_iff.
Check @z_to_int_positive_iff.

Example large_integer_addition_preserved :
    z_to_int (Z.add (Zpos 123456789) (Zneg 987654321)) =
      (z_to_int (Zpos 123456789) + z_to_int (Zneg 987654321))%R.
Proof. apply z_to_int_add. Qed.

Example large_integer_order_preserved :
    is_true ((z_to_int (Zneg 987654321) <
      z_to_int (Zpos 123456789))%R).
Proof.
  apply (proj1 (z_to_int_lt_iff _ _)). lia.
Qed.

Check @q_to_rat_zero.
Check @q_to_rat_one.
Check @q_to_rat_add.
Check @q_to_rat_opp.
Check @q_to_rat_sub.
Check @q_to_rat_mul.
Check @q_to_rat_inv.
Check @q_to_rat_div.
Check @q_to_rat_inject_Z.

Definition a1_zero_over_seven : Q := Qmake Z0 7%positive.
Definition a1_one_half : Q := Qmake (Zpos 1) 2%positive.
Definition a1_two_fourths : Q := Qmake (Zpos 2) 4%positive.
Definition a1_three_fourths : Q := Qmake (Zpos 3) 4%positive.
Definition a1_minus_three_sixths : Q := Qmake (Zneg 3) 6%positive.
Definition a1_minus_three_halves : Q := Qmake (Zneg 3) 2%positive.
Definition a1_minus_one : Q := Qmake (Zneg 1) 1%positive.

Example nonnormalized_addition_preserved :
    q_to_rat (Qplus a1_one_half a1_two_fourths) =
      (q_to_rat a1_one_half + q_to_rat a1_two_fourths)%R.
Proof. apply q_to_rat_add. Qed.

Example nonnormalized_zero_division_preserved :
    q_to_rat (Qdiv a1_zero_over_seven a1_two_fourths) =
      (q_to_rat a1_zero_over_seven / q_to_rat a1_two_fourths)%R.
Proof. apply q_to_rat_div. Qed.

Example zero_addition_preserved :
    q_to_rat (Qplus a1_zero_over_seven a1_one_half) =
      (q_to_rat a1_zero_over_seven + q_to_rat a1_one_half)%R.
Proof. apply q_to_rat_add. Qed.

Example zero_subtraction_preserved :
    q_to_rat (Qminus a1_zero_over_seven a1_one_half) =
      (q_to_rat a1_zero_over_seven - q_to_rat a1_one_half)%R.
Proof. apply q_to_rat_sub. Qed.

Example zero_multiplication_preserved :
    q_to_rat (Qmult a1_zero_over_seven a1_minus_three_sixths) =
      (q_to_rat a1_zero_over_seven *
        q_to_rat a1_minus_three_sixths)%R.
Proof. apply q_to_rat_mul. Qed.

Example division_by_zero_preserved :
    q_to_rat (Qdiv a1_three_fourths a1_zero_over_seven) =
      (q_to_rat a1_three_fourths / q_to_rat a1_zero_over_seven)%R.
Proof. apply q_to_rat_div. Qed.

Example inverse_zero_preserved :
    q_to_rat (Qinv (Qmake Z0 3%positive)) =
      (q_to_rat (Qmake Z0 3%positive))^-1%R.
Proof. apply q_to_rat_inv. Qed.

Example negative_inverse_preserved :
    q_to_rat (Qinv a1_minus_three_sixths) =
      (q_to_rat a1_minus_three_sixths)^-1%R.
Proof. apply q_to_rat_inv. Qed.

Example zero_one_minus_one_preserved :
    q_to_rat (Qopp 1) = (- (1 : rat))%R.
Proof. rewrite q_to_rat_opp q_to_rat_one. reflexivity. Qed.

Example signed_addition_preserved :
    q_to_rat (Qplus a1_minus_three_sixths a1_three_fourths) =
      (q_to_rat a1_minus_three_sixths + q_to_rat a1_three_fourths)%R.
Proof. apply q_to_rat_add. Qed.

Example signed_subtraction_preserved :
    q_to_rat (Qminus a1_minus_three_sixths a1_three_fourths) =
      (q_to_rat a1_minus_three_sixths - q_to_rat a1_three_fourths)%R.
Proof. apply q_to_rat_sub. Qed.

Example signed_multiplication_preserved :
    q_to_rat (Qmult a1_minus_three_sixths a1_three_fourths) =
      (q_to_rat a1_minus_three_sixths * q_to_rat a1_three_fourths)%R.
Proof. apply q_to_rat_mul. Qed.

Example signed_division_preserved :
    q_to_rat (Qdiv a1_minus_three_sixths a1_three_fourths) =
      (q_to_rat a1_minus_three_sixths / q_to_rat a1_three_fourths)%R.
Proof. apply q_to_rat_div. Qed.

Example large_integer_multiplication_preserved :
    q_to_rat (Qmult (inject_Z (Zpos 123456789))
      (inject_Z (Zneg 987654321))) =
    (q_to_rat (inject_Z (Zpos 123456789)) *
      q_to_rat (inject_Z (Zneg 987654321)))%R.
Proof. apply q_to_rat_mul. Qed.

Check @q_to_rat_le_iff.
Check @q_to_rat_lt_iff.
Check @q_to_rat_nonnegative_iff.
Check @q_to_rat_positive_iff.
Check @q_to_rat_nonpositive_iff.
Check @q_to_rat_negative_iff.
Check @q_to_rat_inject_Z_le_iff.
Check @q_to_rat_inject_Z_lt_iff.
Check @q_to_rat_mul_positive_le_iff.
Check @q_to_rat_mul_positive_lt_iff.
Check @rat_to_q_nonnegative.
Check @rat_to_q_positive.

Print Assumptions z_to_int_zero.
Print Assumptions z_to_int_one.
Print Assumptions z_to_int_add.
Print Assumptions z_to_int_sub.
Print Assumptions z_to_int_mul.
Print Assumptions z_to_int_le_iff.
Print Assumptions z_to_int_lt_iff.
Print Assumptions z_to_int_nonnegative_iff.
Print Assumptions z_to_int_positive_iff.
Print Assumptions q_to_rat_zero.
Print Assumptions q_to_rat_one.
Print Assumptions q_to_rat_add.
Print Assumptions q_to_rat_opp.
Print Assumptions q_to_rat_sub.
Print Assumptions q_to_rat_mul.
Print Assumptions q_to_rat_inv.
Print Assumptions q_to_rat_div.
Print Assumptions q_to_rat_inject_Z.
Print Assumptions q_to_rat_le_iff.
Print Assumptions q_to_rat_lt_iff.
Print Assumptions q_to_rat_nonnegative_iff.
Print Assumptions q_to_rat_positive_iff.
Print Assumptions q_to_rat_nonpositive_iff.
Print Assumptions q_to_rat_negative_iff.
Print Assumptions q_to_rat_inject_Z_le_iff.
Print Assumptions q_to_rat_inject_Z_lt_iff.
Print Assumptions q_to_rat_mul_positive_le_iff.
Print Assumptions q_to_rat_mul_positive_lt_iff.
Print Assumptions rat_to_q_nonnegative.
Print Assumptions rat_to_q_positive.

Example nonnormalized_equal_le_left_to_right :
    is_true ((q_to_rat a1_one_half <= q_to_rat a1_two_fourths)%R).
Proof.
  apply (proj1 (q_to_rat_le_iff _ _)).
  unfold a1_one_half, a1_two_fourths, Qle. cbn. lia.
Qed.

Example nonnormalized_equal_le_right_to_left :
    is_true ((q_to_rat a1_two_fourths <= q_to_rat a1_one_half)%R).
Proof.
  apply (proj1 (q_to_rat_le_iff _ _)).
  unfold a1_one_half, a1_two_fourths, Qle. cbn. lia.
Qed.

Example one_half_less_three_fourths :
    is_true ((q_to_rat a1_one_half < q_to_rat a1_three_fourths)%R).
Proof.
  apply (proj1 (q_to_rat_lt_iff _ _)).
  unfold a1_one_half, a1_three_fourths, Qlt. cbn. lia.
Qed.

Example minus_three_halves_less_minus_one :
    is_true ((q_to_rat a1_minus_three_halves <
      q_to_rat a1_minus_one)%R).
Proof.
  apply (proj1 (q_to_rat_lt_iff _ _)).
  unfold a1_minus_three_halves, a1_minus_one, Qlt. cbn. lia.
Qed.

Example different_denominators_compared :
    is_true ((q_to_rat (Qmake (Zpos 5) 7%positive) <
      q_to_rat (Qmake (Zpos 8) 9%positive))%R).
Proof.
  apply (proj1 (q_to_rat_lt_iff _ _)). unfold Qlt. cbn. lia.
Qed.

Example positive_factor_preserves_order :
    is_true (((q_to_rat a1_one_half * q_to_rat a1_three_fourths) <=
      (q_to_rat a1_two_fourths * q_to_rat a1_three_fourths))%R).
Proof.
  have Hfactor : Qlt 0 a1_three_fourths.
    unfold a1_three_fourths, Qlt. cbn. lia.
  apply (proj1 (@q_to_rat_mul_positive_le_iff
    a1_one_half a1_two_fourths a1_three_fourths Hfactor)).
  unfold a1_one_half, a1_two_fourths, Qle. cbn. lia.
Qed.

Example positive_factor_preserves_strict_order :
    is_true (((q_to_rat a1_one_half * q_to_rat a1_three_fourths) <
      (q_to_rat a1_three_fourths * q_to_rat a1_three_fourths))%R).
Proof.
  have Hfactor : Qlt 0 a1_three_fourths.
    unfold a1_three_fourths, Qlt. cbn. lia.
  apply (proj1 (@q_to_rat_mul_positive_lt_iff
    a1_one_half a1_three_fourths a1_three_fourths Hfactor)).
  unfold a1_one_half, a1_three_fourths, Qlt. cbn. lia.
Qed.

Example rat_roundtrip_nonnegative : forall value : rat,
    is_true (((0 : rat) <= value)%R) -> Qle 0 (rat_to_q value).
Proof. exact rat_to_q_nonnegative. Qed.

Example rat_roundtrip_positive : forall value : rat,
    is_true (((0 : rat) < value)%R) -> Qlt 0 (rat_to_q value).
Proof. exact rat_to_q_positive. Qed.

Example rat_roundtrip_order : forall left right : rat,
    is_true ((left <= right)%R) -> Qle (rat_to_q left) (rat_to_q right).
Proof.
  intros left right Horder.
  apply (proj2 (q_to_rat_le_iff _ _)).
  now rewrite !rat_to_q_to_rat.
Qed.
