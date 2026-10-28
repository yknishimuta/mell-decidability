From Coq Require Import Lia List.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone Corollary67Finitary
  FaceDimension FaceOrder Faces FaceStrippingExtract
  FaceStrippingLemma610 FaceStrippingLemma611 MathCompBridge QConeCore
  RationalDefinability Periodic.
From Mell.Order Require Import PeriodicOrder.

Theorem face_period_full : forall d (period : ZSet d) (face : QSet d),
    Periodic period ->
    FullPeriodic period ->
    FaceOf (Cone period) face ->
    FullPeriodic (FacePeriod period face).
Proof.
  intros d period face Hperiodic Hfull Hface. split.
  - now apply face_periodic.
  - exists (Difference period), face. split.
    + now apply difference_is_integer_additive_group.
    + split.
      * constructor.
        -- exact (face_is_cone d (Cone period) face
             (cone_is_cone d period) Hface).
        -- intros left right Heq.
           apply (face_qvec_ext d (Cone period) face Hface).
           ++ now apply cone_qvec_extensional.
           ++ exact Heq.
      * intro value. split.
        -- intros [Hvalue Hvalue_face]. split.
           ++ exact (proj1 (proj1
                (full_periodic_member_iff_difference_cone d period
                  Hperiodic Hfull value) Hvalue)).
           ++ exact Hvalue_face.
        -- intros [Hvalue_difference Hvalue_face]. split.
           ++ apply (proj2
                (full_periodic_member_iff_difference_cone d period
                  Hperiodic Hfull value)). split.
              ** exact Hvalue_difference.
              ** now apply (face_subset d (Cone period) face Hface).
           ++ exact Hvalue_face.
Qed.

Lemma ordered_stripping_noninitial_face_proper : forall d
    (period : ZSet d) (faces : list (QSet d)) index face,
    OrderedStrippingFaces period faces ->
    0 < index ->
    nth_error faces index = Some face ->
    ProperFaceSubset face (Cone period).
Proof.
  intros d period faces index face Hordered Hpositive Hface.
  destruct Hordered as
    [_ [Hhead [Hsound [_ [Hdistinct _]]]]]. split.
  - unfold FaceSubset. apply (face_subset d (Cone period) face).
    apply Hsound, nth_error_In with (n := index). exact Hface.
  - apply (Hdistinct index 0 face (Cone period)); try assumption.
    lia.
Qed.

Theorem ordered_stripping_noninitial_face_dimension_lt : forall d
    (period : ZSet d) (faces : list (QSet d)) index face
    face_dimension cone_dimension,
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    OrderedStrippingFaces period faces ->
    0 < index ->
    nth_error faces index = Some face ->
    SpanDimension face face_dimension ->
    SpanDimension (Cone period) cone_dimension ->
    face_dimension < cone_dimension.
Proof.
  intros d period faces index face face_dimension cone_dimension
    Hperiodic Hfinite Hordered Hpositive Hface
    Hface_dimension Hcone_dimension.
  apply (proper_face_of_cone_dimension_lt d (Cone period) face
    face_dimension cone_dimension).
  - now apply finitely_generated_period_cone_polyhedral.
  - apply (proj1 (proj2 (proj2 Hordered))), nth_error_In with (n := index).
    exact Hface.
  - exact (proj2 (ordered_stripping_noninitial_face_proper d period faces
      index face Hordered Hpositive Hface)).
  - exact Hface_dimension.
  - exact Hcone_dimension.
Qed.
