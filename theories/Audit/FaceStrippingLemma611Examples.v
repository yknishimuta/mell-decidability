From Coq Require Import Lia List Vector.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Cone FaceStrippingExtract
  FaceStrippingFinitary FaceStrippingLemma610 FaceStrippingLemma611
  FaceStrippingMinimalFace FaceStrippingRecursion FaceOrder Faces FiniteFaces
  LatticeGordanInterface Periodic QConeCore RationalDefinability.
From Mell.Order Require Import PeriodicOrder.
From Mell.Audit Require Import FaceOrderExamples FiniteFacesExamples
  FaceStrippingExtractExamples FaceStrippingMinimalFaceExamples
  FaceStrippingRecursionExamples.

Import ListNotations.

Check @OrderedStrippingFaces.
Check @ordered_stripping_faces_exists.
Check @extract_face_remaining_monotone.
Check @stripping_candidate_monotone.
Check @stripping_current_face_eliminated.
Check @stripping_current_face_same_set_eliminated.
Check @stripping_remainders_cylindric.
Check @stripping_candidates_represented_later.
Check @lemma_6_11_stripping_invariants.
Check @stripping_remainder_finitary.
Check @stripping_nonempty_slice_maximal_face.
Check @stripping_slice_finitary.
Check @stripping_no_candidate_at_end.

Example d2_dimension_zero_ordered_faces :
    exists faces : list (QSet 0),
      OrderedStrippingFaces (@zvec_generated 0 []) faces.
Proof.
  destruct (ordered_stripping_faces_exists 0 (@zvec_generated 0 [])
    (fun _ => False) (@zvec_generated 0 [])
    (generated_periodic 0 [])
    (generated_period_finitely_generated 0 [])) as [faces [Hfaces _]].
  now exists faces.
Qed.

Example d2_nat_stripping_invariants :
    exists faces,
      OrderedStrippingFaces d0_nat_period faces /\
      (forall stage,
        stage <= length faces ->
        QCylindric d0_nat_period
          (StrippingRemainder d0_nat_period d0_nat_excluded
            d0_nat_period faces stage)) /\
      (forall stage,
        stage <= length faces ->
        forall face,
          StageCandidateFace d0_nat_period d0_nat_excluded
            d0_nat_period faces stage face ->
          exists index representative,
            stage <= index /\
            index < length faces /\
            nth_error faces index = Some representative /\
            SameSet face representative).
Proof.
  destruct (ordered_stripping_faces_exists 1 d0_nat_period
    d0_nat_excluded d0_nat_period d0_nat_periodic
    d0_nat_finitely_generated) as [faces [Hfaces _]].
  exists faces. split; [exact Hfaces|].
  apply lemma_6_11_stripping_invariants.
  - exact d0_nat_periodic.
  - exact d0_nat_excluded_cylindric.
  - exact d0_nat_remaining_cylindric.
  - intros value Hexcluded.
    unfold d0_nat_excluded, d0_nat_period in *. lia.
  - exact Hfaces.
Qed.

Example d2_nat_finitary_remainders_and_slices :
    exists faces,
      OrderedStrippingFaces d0_nat_period faces /\
      (forall stage,
        stage <= length faces ->
        FinitaryQCylindric d0_nat_period
          (StrippingRemainder d0_nat_period (fun _ => False)
            d0_nat_period faces stage)) /\
      (forall stage face,
        stage < length faces ->
        nth_error faces stage = Some face ->
        FinitaryQCylindric (FacePeriod d0_nat_period face)
          (StrippingSlice d0_nat_period (fun _ => False)
            d0_nat_period faces stage)).
Proof.
  destruct (ordered_stripping_faces_exists 1 d0_nat_period
    (fun _ => False) d0_nat_period d0_nat_periodic
    d0_nat_finitely_generated) as [faces [Hfaces _]].
  exists faces. split; [exact Hfaces|]. split.
  - intros stage Hstage.
    apply (stripping_remainder_finitary 1 d0_nat_period
      (fun _ => False) d0_nat_period faces d0_nat_periodic
      d0_nat_finitely_generated).
    + firstorder.
    + apply period_finitary_self. exact d0_nat_periodic.
    + firstorder.
    + exact Hfaces.
    + exact Hstage.
  - intros stage face Hstage Hface.
    apply (stripping_slice_finitary 1 d0_nat_period
      (fun _ => False) d0_nat_period faces d0_nat_periodic
      d0_nat_finitely_generated d0_nat_full).
    + apply empty_finitary_qcylindric.
    + apply period_finitary_self. exact d0_nat_periodic.
    + firstorder.
    + exact Hfaces.
    + exact Hstage.
    + exact Hface.
Qed.

Example d2_nat_maximal_face_not_candidate_at_stage_zero :
    ~ StageCandidateFace d0_nat_period d0_nat_excluded d0_nat_period
        d1_nat_faces 0 (Cone d0_nat_period).
Proof.
  intros [_ [value Hextract]].
  apply (d1_nat_slice_zero_empty value).
  exact Hextract.
Qed.

Example d2_nat_minimal_face_candidate_at_stage_one :
    StageCandidateFace d0_nat_period d0_nat_excluded d0_nat_period
      d1_nat_faces 1 (ConeLineality (Cone d0_nat_period)).
Proof.
  split.
  - apply (proj1 (polyhedral_lineality_minimal_face 1
      (Cone d0_nat_period) ltac:(
        apply finitely_generated_period_cone_polyhedral;
          [exact d0_nat_periodic|exact d0_nat_finitely_generated]))).
  - exists (d0_z1 BinNums.Z0).
    exact (proj2 (d1_nat_slice_one (d0_z1 BinNums.Z0))
      (or_introl eq_refl)).
Qed.

Example d2_nat_no_candidate_after_both_faces : forall face,
    ~ StageCandidateFace d0_nat_period d0_nat_excluded d0_nat_period
        d1_nat_faces 2 face.
Proof.
  intros face [Hface [value Hextract]].
  assert (Hface_periodic : Periodic (FacePeriod d0_nat_period face)).
  { apply face_periodic; [exact d0_nat_periodic|exact Hface]. }
  destruct (extract_face_subset_difference 1 d0_nat_period d0_nat_excluded
    (StrippingRemainder d0_nat_period d0_nat_excluded d0_nat_period
      d1_nat_faces 2) face Hface_periodic value Hextract) as
    [Hremainder Hnot_excluded].
  apply Hnot_excluded.
  now apply (proj1 (d1_nat_remainder_two value)).
Qed.

Example d2_quadrant_four_faces_ordered :
    exists faces : list (QSet 2),
      (exists tail, faces = finite_faces_quadrant :: tail) /\
      (forall face,
        List.In face faces -> FaceOf finite_faces_quadrant face) /\
      (forall face,
        FaceOf finite_faces_quadrant face ->
        exists representative,
          List.In representative faces /\
          SameSet face representative) /\
      (forall i j face_i face_j,
        nth_error faces i = Some face_i ->
        nth_error faces j = Some face_j ->
        FaceSubset face_j face_i -> i <= j) /\
      (forall face,
        FaceOf finite_faces_quadrant face ->
        SameSet face finite_faces_quadrant \/
        SameSet face finite_faces_axis1 \/
        SameSet face finite_faces_axis2 \/
        SameSet face finite_faces_zero).
Proof.
  destruct quadrant_faces_linearized as
    [faces [Hhead [Hsound [Hcomplete [Hdistinct Horder]]]]].
  exists faces. repeat split; try assumption.
  apply quadrant_faces_are_exactly_standard.
Qed.

Example d2_quadrant_candidates_represented_later :
    exists faces : list (QSet 2),
      OrderedStrippingFaces extract_quadrant_period faces /\
      (forall stage,
        stage <= length faces ->
        forall face,
          StageCandidateFace extract_quadrant_period (fun _ => False)
            extract_quadrant_period faces stage face ->
          exists index representative,
            stage <= index /\
            index < length faces /\
            nth_error faces index = Some representative /\
            SameSet face representative).
Proof.
  destruct (ordered_stripping_faces_exists 2 extract_quadrant_period
    (fun _ => False) extract_quadrant_period (generated_periodic 2 _)
    (generated_period_finitely_generated 2 _)) as [faces [Hfaces _]].
  exists faces. split; [exact Hfaces|].
  intros stage Hstage face Hcandidate.
  eapply (stripping_candidates_represented_later 2 extract_quadrant_period
    (fun _ => False) extract_quadrant_period faces).
  - apply generated_periodic.
  - exact Hfaces.
  - exact Hstage.
  - exact Hcandidate.
Qed.

Check d0_two_nat_periodic.
Check d0_nat_square_periodic.
Check d0_integer_periodic.
Check d0_nat_times_integer_periodic.
Check d1_two_nat_remainder_one_empty.
Check d1_nat_times_integer_minimal_face_nonzero.

Print Assumptions extract_face_remaining_monotone.
Print Assumptions stripping_candidate_monotone.
Print Assumptions stripping_current_face_eliminated.
Print Assumptions stripping_current_face_same_set_eliminated.
Print Assumptions lemma_6_11_stripping_invariants.
Print Assumptions stripping_remainder_finitary.
Print Assumptions stripping_nonempty_slice_maximal_face.
Print Assumptions stripping_slice_finitary.
Print Assumptions stripping_no_candidate_at_end.
