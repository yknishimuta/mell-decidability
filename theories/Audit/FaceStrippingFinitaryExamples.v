From Coq Require Import List Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Cone Faces FaceStrippingExtract
  FaceStrippingFinitary Periodic RationalDefinability.
From Mell.Order Require Import PeriodicOrder.
From Mell.Audit Require Import FaceStrippingExtractExamples.

Import ListNotations.

Set Printing Implicit.

Check @CylindricSlice.
Check @finitary_qcylindric_implies_cylindric.
Check @slice_subset_period.
Check @slice_upward_closed.
Check @slice_finite_cover.
Check @finite_base_translation.
Check @finite_base_union.
Check @finitary_qcylindric_sub.
Check @extract_remainder_finitary.

Print Assumptions slice_finite_cover.
Print Assumptions finitary_qcylindric_sub.
Print Assumptions extract_remainder_finitary.

Example empty_set_has_empty_finitary_basis : forall d (period : ZSet d),
    FinitaryQCylindric period (fun _ => False).
Proof. apply empty_finitary_qcylindric. Qed.

Example finitary_sub_identity : forall d (period set : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    QCylindric period set ->
    FinitaryQCylindric period set ->
    FinitaryQCylindric period set.
Proof.
  intros d period set Hperiodic Hfinite Hcylindric Hfinitary.
  eapply finitary_qcylindric_sub; eauto.
Qed.

Example empty_sub_empty_finitary : forall d (period : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FinitaryQCylindric period (fun _ => False).
Proof.
  intros d period Hperiodic Hfinite.
  eapply finitary_qcylindric_sub with
    (B := fun _ : ZVec d => False).
  - exact Hperiodic.
  - exact Hfinite.
  - firstorder.
  - apply empty_finitary_qcylindric.
  - firstorder.
Qed.

Example dimension_zero_period_finitary :
    FinitaryQCylindric (@zvec_generated 0 []) (@zvec_generated 0 []).
Proof. apply period_finitary_self, generated_periodic. Qed.

Example zero_period_finitary : forall d,
    FinitaryQCylindric (@zvec_generated d []) (@zvec_generated d []).
Proof. intro d. apply period_finitary_self, generated_periodic. Qed.

Example nat_period_finitary :
    FinitaryQCylindric extract_nat_period extract_nat_period.
Proof. apply period_finitary_self, generated_periodic. Qed.

Example quadrant_period_finitary :
    FinitaryQCylindric extract_quadrant_period extract_quadrant_period.
Proof. apply period_finitary_self, generated_periodic. Qed.

Example signed_lineality_period_finitary :
    FinitaryQCylindric extract_lineality_period extract_lineality_period.
Proof. apply period_finitary_self, generated_periodic. Qed.

Definition low_rank_signed_period : ZSet 2 :=
  zvec_generated [extract_z2 1 0; extract_z2 (-1) 0].

Example low_rank_signed_period_finitary :
    FinitaryQCylindric low_rank_signed_period low_rank_signed_period.
Proof. apply period_finitary_self, generated_periodic. Qed.

Definition two_translate_nat : ZSet 1 :=
  fun value => exists base increment,
    List.In base [extract_z1 0; extract_z1 1] /\
    extract_nat_period increment /\
    value = zvec_add base increment.

Example multiple_translate_finitary :
    FinitaryQCylindric extract_nat_period two_translate_nat.
Proof.
  exists [extract_z1 0; extract_z1 1]. intro value. reflexivity.
Qed.

Example maximal_face_empty_excluded_remainder_finitary :
    FinitaryQCylindric extract_nat_period
      (fun value =>
        extract_nat_period value /\
        ~ ExtractFace extract_nat_period (Cone extract_nat_period)
            (fun _ => False) extract_nat_period value).
Proof.
  apply extract_remainder_finitary.
  - apply generated_periodic.
  - apply generated_period_finitely_generated.
  - apply face_self.
  - firstorder.
  - apply period_finitary_self, generated_periodic.
  - firstorder.
Qed.

Example maximal_face_equal_excluded_remainder_finitary :
    FinitaryQCylindric extract_nat_period
      (fun value =>
        extract_nat_period value /\
        ~ ExtractFace extract_nat_period (Cone extract_nat_period)
            extract_nat_period extract_nat_period value).
Proof.
  apply extract_remainder_finitary.
  - apply generated_periodic.
  - apply generated_period_finitely_generated.
  - apply face_self.
  - intros base increment Hbase Hincrement.
    now apply (proj2 (generated_periodic 1 [extract_z1 1])).
  - apply period_finitary_self, generated_periodic.
  - firstorder.
Qed.

Example proper_face_empty_excluded_remainder_finitary :
    FinitaryQCylindric extract_nat_period
      (fun value =>
        extract_nat_period value /\
        ~ ExtractFace extract_nat_period extract_nat_zero_face
            (fun _ => False) extract_nat_period value).
Proof.
  apply extract_remainder_finitary.
  - apply generated_periodic.
  - apply generated_period_finitely_generated.
  - apply extract_nat_zero_face_is_face.
  - firstorder.
  - apply period_finitary_self, generated_periodic.
  - firstorder.
Qed.

Example excluded_is_contained_in_finitary_remainder : forall value,
    extract_nat_period value ->
    extract_nat_period value /\
    ~ ExtractFace extract_nat_period (Cone extract_nat_period)
        extract_nat_period extract_nat_period value.
Proof.
  apply excluded_subset_extract_remainder.
  - apply generated_periodic.
  - apply face_self.
  - firstorder.
Qed.
