From Coq Require Import QArith ZArith.
From mathcomp Require Import all_ssreflect all_algebra.
From Mell.Geometry Require Import QratAdapter.

Set Printing Implicit.

Check @z_to_int.
Check @int_to_z.
Check @int_to_z_to_int.
Check @z_to_int_to_z.
Check @z_to_int_opp.
Check @q_to_rat.
Check @rat_to_q.
Check @q_to_rat_eq_iff.
Check @rat_to_q_to_rat.
Check @q_to_rat_to_q.

Print Assumptions q_to_rat_eq_iff.
Print Assumptions rat_to_q_to_rat.
Print Assumptions q_to_rat_to_q.

Definition q_zero : Q :=
  Qmake BinNums.Z0 1%positive.

Definition q_zero_over_two : Q :=
  Qmake BinNums.Z0 2%positive.

Definition q_zero_over_seven : Q :=
  Qmake BinNums.Z0 7%positive.

Definition q_one_half : Q :=
  Qmake (BinNums.Zpos 1) 2%positive.

Definition q_two_fourths : Q :=
  Qmake (BinNums.Zpos 2) 4%positive.

Definition q_minus_three_sixths : Q :=
  Qmake (BinNums.Zneg 3) 6%positive.

Example integer_roundtrips_zero :
    int_to_z (z_to_int BinNums.Z0) = BinNums.Z0.
Proof. apply int_to_z_to_int. Qed.

Example integer_roundtrips_positive :
    int_to_z (z_to_int (BinNums.Zpos 123456789)) =
      BinNums.Zpos 123456789.
Proof. apply int_to_z_to_int. Qed.

Example integer_roundtrips_negative :
    int_to_z (z_to_int (BinNums.Zneg 987654321)) =
      BinNums.Zneg 987654321.
Proof. apply int_to_z_to_int. Qed.

Example zero_denominators_are_numerically_equal :
    Qeq q_zero_over_two q_zero_over_seven.
Proof. reflexivity. Qed.

Example q_to_rat_identifies_zero_denominators :
    q_to_rat q_zero_over_two = q_to_rat q_zero_over_seven.
Proof.
  apply (proj2 (q_to_rat_eq_iff _ _)). reflexivity.
Qed.

Example nonnormalized_halves_are_numerically_equal :
    Qeq q_one_half q_two_fourths.
Proof. reflexivity. Qed.

Example nonnormalized_halves_are_not_leibniz_equal :
    q_one_half <> q_two_fourths.
Proof. discriminate. Qed.

Example q_to_rat_identifies_nonnormalized_halves :
    q_to_rat q_one_half = q_to_rat q_two_fourths.
Proof.
  apply (proj2 (q_to_rat_eq_iff _ _)). reflexivity.
Qed.

Example negative_half_is_preserved :
    q_to_rat q_minus_three_sixths = q_to_rat (Qmake (BinNums.Zneg 1) 2%positive).
Proof.
  apply (proj2 (q_to_rat_eq_iff _ _)). reflexivity.
Qed.

Example q_roundtrip_zero : Qeq (rat_to_q (q_to_rat q_zero)) q_zero.
Proof. apply q_to_rat_to_q. Qed.

Example q_roundtrip_zero_over_seven :
    Qeq (rat_to_q (q_to_rat q_zero_over_seven)) q_zero_over_seven.
Proof. apply q_to_rat_to_q. Qed.

Example q_roundtrip_one :
    Qeq (rat_to_q (q_to_rat (Qmake (BinNums.Zpos 1) 1%positive)))
      (Qmake (BinNums.Zpos 1) 1%positive).
Proof. apply q_to_rat_to_q. Qed.

Example q_roundtrip_minus_one :
    Qeq (rat_to_q (q_to_rat (Qmake (BinNums.Zneg 1) 1%positive)))
      (Qmake (BinNums.Zneg 1) 1%positive).
Proof. apply q_to_rat_to_q. Qed.

Example rat_roundtrip_example : forall value : rat,
    q_to_rat (rat_to_q value) = value.
Proof. apply rat_to_q_to_rat. Qed.
