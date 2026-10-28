From Coq Require Import Fin Lia Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Center ClosedLinearization Periodic.
From Mell.Order Require Import PeriodicOrder.

Open Scope Z_scope.
Set Printing Implicit.

Check @Center.
Check @center_in_difference.
Check @center_add.

Definition center_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition center_zero_set {d} : ZSet d :=
  fun value => value = zvec_zero d.

Lemma center_zero_set_periodic : forall d, Periodic (@center_zero_set d).
Proof.
  intro d. split.
  - reflexivity.
  - intros left right -> ->. apply zvec_add_zero_right.
Qed.

Example center_dimension_zero :
    Center (@center_zero_set 0) (zvec_zero 0).
Proof.
  intros g [left [right [-> [-> ->]]]].
  exists 0%nat. intro n.
  apply Vector.eq_nth_iff. intros index index' Heq. subst index'.
  exact (Fin.case0 (fun i =>
    Vector.nth
      (zvec_add (zvec_sub (zvec_zero 0) (zvec_zero 0))
        (zvec_nsmul (0 + n) (zvec_zero 0))) i =
      Vector.nth (zvec_zero 0) i) index).
Qed.

Example center_zero_monoid_contains_zero :
    Center (@center_zero_set 1) (zvec_zero 1).
Proof.
  intros g [left [right [Hleft [Hright ->]]]].
  unfold center_zero_set in Hleft, Hright. subst left right.
  exists 0%nat. intro n.
  unfold center_zero_set.
  rewrite zvec_sub_self, zvec_add_zero_left.
  apply zvec_ext. intro index.
  rewrite nth_zvec_nsmul. unfold zvec_zero.
  rewrite const_nth. ring.
Qed.

Definition center_twoN (value : ZVec 1) : Prop :=
  exists coefficient : nat,
    Vector.nth value Fin.F1 = 2 * Z.of_nat coefficient.

Lemma center_twoN_periodic : Periodic center_twoN.
Proof.
  split.
  - exists 0%nat. reflexivity.
  - intros left right [a Ha] [b Hb]. exists (a + b)%nat.
    unfold zvec_add.
    rewrite (nth_map2 Z.add left right Fin.F1 Fin.F1 Fin.F1
      eq_refl eq_refl), Ha, Hb, Nat2Z.inj_add. ring.
Qed.

Lemma center_twoN_minus_two_in_difference :
    Difference center_twoN (center_z1 (-2)).
Proof.
  exists (center_z1 0), (center_z1 2). repeat split.
  - exists 0%nat. reflexivity.
  - exists 1%nat. reflexivity.
Qed.

Example center_twoN_does_not_contain_zero :
    ~ Center center_twoN (zvec_zero 1).
Proof.
  intros Hcenter.
  destruct (Hcenter (center_z1 (-2)) center_twoN_minus_two_in_difference)
    as [radius Htail].
  destruct (Htail 0%nat) as [coefficient Hcoefficient].
  unfold center_z1, zvec_add in Hcoefficient.
  rewrite (nth_map2 Z.add _ _ Fin.F1 Fin.F1 Fin.F1
    eq_refl eq_refl), nth_zvec_nsmul in Hcoefficient.
  unfold zvec_zero in Hcoefficient. rewrite const_nth in Hcoefficient.
  rewrite Z.mul_0_r in Hcoefficient.
  change (-2 = 2 * Z.of_nat coefficient)%Z in Hcoefficient.
  pose proof (Zle_0_nat coefficient).
  lia.
Qed.

Example center_twoN_center_is_in_difference : forall value,
    Center center_twoN value -> Difference center_twoN value.
Proof.
  intros value Hvalue.
  eapply center_in_difference; [exact center_twoN_periodic|exact Hvalue].
Qed.

Definition center_gap (value : ZVec 1) : Prop :=
  Vector.nth value Fin.F1 = 0 \/
  2 <= Vector.nth value Fin.F1.

Lemma center_gap_periodic : Periodic center_gap.
Proof.
  split.
  - left. reflexivity.
  - intros left right Hleft Hright. unfold center_gap in *.
    unfold zvec_add.
    rewrite (nth_map2 Z.add left right Fin.F1 Fin.F1 Fin.F1
      eq_refl eq_refl).
    destruct Hleft, Hright; [left|right|right|right]; lia.
Qed.

Example center_gap_one_not_member : ~ center_gap (center_z1 1).
Proof. unfold center_gap, center_z1; cbn; lia. Qed.

Example center_gap_one_is_central : Center center_gap (center_z1 1).
Proof.
  intros offset _.
  set (coordinate := Vector.nth offset Fin.F1).
  exists (Z.to_nat (Z.abs coordinate + 2)). intro n. right.
  unfold zvec_add.
  rewrite (nth_map2 Z.add _ _ Fin.F1 Fin.F1 Fin.F1
    eq_refl eq_refl), nth_zvec_nsmul.
  unfold center_z1; cbn.
  rewrite Nat2Z.inj_add, Z2Nat.id by
    (pose proof (Z.abs_nonneg coordinate); lia).
  assert (Habs : coordinate <= Z.abs coordinate).
  { destruct coordinate; cbn; lia. }
  unfold coordinate in *. lia.
Qed.

Print Assumptions center_in_difference.
Print Assumptions center_add.
