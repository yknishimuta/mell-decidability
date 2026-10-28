From Coq Require Import List Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Cone Faces FaceStrippingExtract
  FaceStrippingLemma610FiniteBasis LatticeGordanV MathCompBridge Periodic
  QConeCore RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.

Check zvec_generated_dec_explicit.
Check finitary_presentation_dec_explicit.
Check extract_face_cylindric_characterization.
Check extract_face_dec_explicit.
Check face_periodic_le_dec_explicit.
Check monotone_subsequence_implies_finitary.
Check lemma_6_10_maximal_extract_finitary.

Definition finite_basis_z1 (value : Z) : ZVec 1 :=
  Vector.of_list [value].

Definition finite_basis_z2 (left right : Z) : ZVec 2 :=
  Vector.of_list [left; right].

Definition generated_decision {d} (generators : list (ZVec d)) value : bool :=
  if zvec_generated_dec_explicit generators value then true else false.

Definition presented_decision {d} (generators bases : list (ZVec d)) value
    : bool :=
  if finitary_presentation_dec_explicit generators bases value
  then true else false.

Example generated_dimension_zero_decides :
    generated_decision [] (zvec_zero 0) = true.
Proof. vm_compute. reflexivity. Qed.

Example generated_two_nat_accepts_even :
    generated_decision [finite_basis_z1 2] (finite_basis_z1 8) = true.
Proof. vm_compute. reflexivity. Qed.

Example generated_two_nat_rejects_odd :
    generated_decision [finite_basis_z1 2] (finite_basis_z1 7) = false.
Proof. vm_compute. reflexivity. Qed.

Example translated_two_nat_accepts_outside_period :
    presented_decision [finite_basis_z1 2] [finite_basis_z1 1]
      (finite_basis_z1 7) = true.
Proof. vm_compute. reflexivity. Qed.

Example translated_two_nat_rejects_even :
    presented_decision [finite_basis_z1 2] [finite_basis_z1 1]
      (finite_basis_z1 8) = false.
Proof. vm_compute. reflexivity. Qed.

Example quadrant_two_nat_accepts :
    generated_decision
      [finite_basis_z2 2 0; finite_basis_z2 0 2]
      (finite_basis_z2 4 6) = true.
Proof. vm_compute. reflexivity. Qed.

Example quadrant_two_nat_rejects_odd_translate :
    generated_decision
      [finite_basis_z2 2 0; finite_basis_z2 0 2]
      (finite_basis_z2 1 1) = false.
Proof. vm_compute. reflexivity. Qed.

Example proper_face_two_nat_accepts_axis_difference :
    generated_decision [finite_basis_z2 2 0] (finite_basis_z2 6 0) = true.
Proof. vm_compute. reflexivity. Qed.

Example proper_face_two_nat_rejects_off_axis_difference :
    generated_decision [finite_basis_z2 2 0] (finite_basis_z2 6 2) = false.
Proof. vm_compute. reflexivity. Qed.

Example proper_face_odd_translate_is_presented :
    presented_decision
      [finite_basis_z2 2 0; finite_basis_z2 0 2]
      [finite_basis_z2 1 1] (finite_basis_z2 5 7) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma finitely_presented_is_cylindric : forall d
    (generators bases : list (ZVec d)),
    QCylindric (zvec_generated generators)
      (FinitelyPresented generators bases).
Proof.
  intros d generators bases base increment Hbase Hincrement.
  apply finitely_presented_spec in Hbase.
  destruct Hbase as [origin [part [Horigin [Hpart ->]]]].
  apply finitely_presented_spec.
  exists origin, (zvec_add part increment). repeat split; try assumption.
  - now apply generated_add.
  - apply zvec_add_assoc.
Qed.

Definition even_nat_period : ZSet 1 :=
  zvec_generated [finite_basis_z1 2].

Definition odd_even_translate : ZSet 1 :=
  FinitelyPresented [finite_basis_z1 2] [finite_basis_z1 1].

Lemma even_nat_face_periodic :
    Periodic (FacePeriod even_nat_period (Cone even_nat_period)).
Proof. apply face_periodic; [apply generated_periodic|apply face_self]. Qed.

Lemma even_nat_face_generated : forall value,
    FacePeriod even_nat_period (Cone even_nat_period) value <->
    zvec_generated [finite_basis_z1 2] value.
Proof.
  intro value. apply face_period_self, generated_periodic.
Qed.

Lemma empty_even_presentation : forall value,
    (fun _ : ZVec 1 => False) value <->
    FinitelyPresented [finite_basis_z1 2] [] value.
Proof.
  intro value. split; [contradiction|].
  intros [base [Hin _]]. contradiction.
Qed.

Definition even_odd_extract_decision (value : ZVec 1) : bool :=
  if extract_face_dec_explicit even_nat_period
      (fun _ : ZVec 1 => False) odd_even_translate
      (Cone even_nat_period)
      [finite_basis_z1 2] [finite_basis_z1 2]
      [] [finite_basis_z1 1]
      even_nat_face_periodic
      (finitely_presented_is_cylindric 1
        [finite_basis_z1 2] [finite_basis_z1 1])
      (fun value => iff_refl (even_nat_period value))
      even_nat_face_generated
      empty_even_presentation
      (fun value => iff_refl (odd_even_translate value))
      value
  then true else false.

Example outside_period_extract_membership_is_decidable :
    even_odd_extract_decision (finite_basis_z1 1) = true.
Proof. vm_compute. reflexivity. Qed.

Example later_outside_period_extract_membership_is_decidable :
    even_odd_extract_decision (finite_basis_z1 9) = true.
Proof. vm_compute. reflexivity. Qed.

Definition even_quadrant_period : ZSet 2 :=
  zvec_generated [finite_basis_z2 2 0; finite_basis_z2 0 2].

Definition even_first_axis_period : ZSet 2 :=
  zvec_generated [finite_basis_z2 2 0].

Definition even_first_axis_face : QSet 2 :=
  fun point => exists value,
    even_first_axis_period value /\
    QVecEq point (zvec_to_qvec value).

Lemma even_first_axis_face_period_spec : forall value,
    FacePeriod even_quadrant_period even_first_axis_face value <->
    even_first_axis_period value.
Proof.
  intro value. split.
  - intros [_ [axis [Haxis Heq]]].
    apply zvec_to_qvec_injective in Heq. now subst axis.
  - intro Haxis. split.
    + change (zvec_generated
        ([finite_basis_z2 2 0] ++ [finite_basis_z2 0 2]) value).
      now apply generated_append_left.
    + exists value. split; [exact Haxis|apply qvec_eq_refl].
Qed.

Lemma even_first_axis_face_periodic :
    Periodic (FacePeriod even_quadrant_period even_first_axis_face).
Proof.
  split.
  - apply (proj2 (even_first_axis_face_period_spec (zvec_zero 2))).
    apply generated_zero.
  - intros left right Hleft Hright.
    apply (proj2 (even_first_axis_face_period_spec (zvec_add left right))).
    apply generated_add;
      apply (proj1 (even_first_axis_face_period_spec _)); assumption.
Qed.

Definition proper_face_extract_decision (value : ZVec 2) : bool :=
  if extract_face_dec_explicit even_quadrant_period
      (FinitelyPresented
        [finite_basis_z2 2 0; finite_basis_z2 0 2]
        [finite_basis_z2 1 3])
      (FinitelyPresented
        [finite_basis_z2 2 0; finite_basis_z2 0 2]
        [finite_basis_z2 1 1])
      even_first_axis_face
      [finite_basis_z2 2 0; finite_basis_z2 0 2]
      [finite_basis_z2 2 0]
      [finite_basis_z2 1 3] [finite_basis_z2 1 1]
      even_first_axis_face_periodic
      (finitely_presented_is_cylindric 2
        [finite_basis_z2 2 0; finite_basis_z2 0 2]
        [finite_basis_z2 1 1])
      (fun value => iff_refl (even_quadrant_period value))
      even_first_axis_face_period_spec
      (fun value => iff_refl
        (FinitelyPresented
          [finite_basis_z2 2 0; finite_basis_z2 0 2]
          [finite_basis_z2 1 3] value))
      (fun value => iff_refl
        (FinitelyPresented
          [finite_basis_z2 2 0; finite_basis_z2 0 2]
          [finite_basis_z2 1 1] value))
      value
  then true else false.

Example proper_face_two_nat_extract_start :
    proper_face_extract_decision (finite_basis_z2 1 1) = true.
Proof. vm_compute. reflexivity. Qed.

Example proper_face_two_nat_excluded_point :
    proper_face_extract_decision (finite_basis_z2 1 3) = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions zvec_generated_dec_explicit.
Print Assumptions extract_face_dec_explicit.
Print Assumptions face_periodic_le_dec_explicit.
Print Assumptions monotone_subsequence_implies_finitary.
Print Assumptions lemma_6_10_maximal_extract_finitary.
