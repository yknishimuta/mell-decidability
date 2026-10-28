From Coq Require Import Arith.PeanoNat Classical_Prop Lia List.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone FaceOrder Faces FaceStrippingExtract
  FaceStrippingFinitary FaceStrippingLemma610 FaceStrippingLemma611
  FaceStrippingMinimalFace FaceStrippingOrderFoundation
  FaceStrippingRecursion LatticeGordanInterface MathCompBridge Periodic QConeCore
  RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Definition BackwardPeriodCover {d}
    (period excluded remaining : ZSet d) : Prop :=
  forall value,
    remaining value ->
    exists increment,
      period increment /\
      excluded (zvec_add value increment).

Theorem stripping_final_remainder_eq_excluded : forall d
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces ->
    SameSet
      (StrippingRemainder period excluded initial_remaining
        faces (length faces))
      excluded.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfinite Hfull
    Hexcluded_finite Hinitial_finite Hsubset Hordered.
  assert (Hexcluded_cyl : QCylindric period excluded).
  { now apply finitary_qcylindric_implies_cylindric. }
  assert (Hinitial_cyl : QCylindric period initial_remaining).
  { now apply finitary_qcylindric_implies_cylindric. }
  assert (Hsound : forall face,
      List.In face faces -> FaceOf (Cone period) face).
  { exact (proj1 (proj2 (proj2 Hordered))). }
  assert (Hexcluded_final : forall value,
      excluded value ->
      StrippingRemainder period excluded initial_remaining
        faces (length faces) value).
  { eapply stripping_excluded_subset_remainder; eauto. }
  assert (Hfinal_cyl : QCylindric period
      (StrippingRemainder period excluded initial_remaining
        faces (length faces))).
  { destruct (lemma_6_11_stripping_invariants d period excluded
      initial_remaining faces Hperiodic Hexcluded_cyl Hinitial_cyl Hsubset
      Hordered) as [Hremainders _].
    now apply Hremainders. }
  assert (Hlineality_face :
      FaceOf (Cone period) (ConeLineality (Cone period))).
  { assert (Hpolyhedral : RationalPolyhedralCone (Cone period)).
    { now apply finitely_generated_period_cone_polyhedral. }
    exact (proj1 (polyhedral_lineality_minimal_face d (Cone period)
      Hpolyhedral)). }
  pose proof (lemma_6_9_minimal_extract d period excluded
    (StrippingRemainder period excluded initial_remaining
      faces (length faces)) Hperiodic Hfinite Hfull Hexcluded_cyl
    Hfinal_cyl Hexcluded_final) as Hminimal_extract.
  intro value. split.
  - intro Hfinal.
    destruct (classic (excluded value)) as [Hexcluded|Hnot_excluded];
      [exact Hexcluded|].
    exfalso.
    apply (stripping_no_candidate_at_end d period excluded initial_remaining
      faces Hperiodic Hordered (ConeLineality (Cone period))).
    split; [exact Hlineality_face|].
    exists value.
    apply (proj2 (Hminimal_extract value)). now split.
  - exact (Hexcluded_final value).
Qed.

Theorem stripping_complete_partition : forall d
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces ->
    forall value,
      (initial_remaining value /\ ~ excluded value) <->
      exists stage,
        stage < length faces /\
        StrippingSlice period excluded initial_remaining faces stage value.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfinite Hfull
    Hexcluded_finite Hinitial_finite Hsubset Hordered value.
  assert (Hsound : forall face,
      List.In face faces -> FaceOf (Cone period) face).
  { exact (proj1 (proj2 (proj2 Hordered))). }
  pose proof (stripping_final_remainder_eq_excluded d period excluded
    initial_remaining faces Hperiodic Hfinite Hfull Hexcluded_finite
    Hinitial_finite Hsubset Hordered) as Hfinal.
  split.
  - intros [Hinitial Hnot_excluded].
    apply (proj1 (stripping_initial_partition d period excluded
      initial_remaining faces Hperiodic Hsound (length faces)
      (Nat.le_refl _) value)) in Hinitial.
    destruct Hinitial as [Hremainder|Hprocessed].
    + exfalso. apply Hnot_excluded. now apply (proj1 (Hfinal value)).
    + exact Hprocessed.
  - intros [stage [Hstage Hslice]].
    eapply stripping_slice_subset_initial_difference; eassumption.
Qed.

Theorem stripping_partition_slices_disjoint : forall d
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
    Periodic period ->
    OrderedStrippingFaces period faces ->
    forall earlier later,
      earlier < later ->
      later < length faces ->
      forall value,
        ~ (StrippingSlice period excluded initial_remaining faces earlier value /\
           StrippingSlice period excluded initial_remaining faces later value).
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hordered.
  eapply stripping_slices_disjoint; eauto.
  exact (proj1 (proj2 (proj2 Hordered))).
Qed.

Theorem stripping_finitary_stage_package : forall d
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces ->
    (forall stage,
      stage <= length faces ->
      FinitaryQCylindric period
        (StrippingRemainder period excluded initial_remaining faces stage) /\
      forall value,
        excluded value ->
        StrippingRemainder period excluded initial_remaining faces stage value) /\
    (forall stage face,
      stage < length faces ->
      nth_error faces stage = Some face ->
      FinitaryQCylindric (FacePeriod period face)
        (StrippingSlice period excluded initial_remaining faces stage)).
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfinite Hfull
    Hexcluded_finite Hinitial_finite Hsubset Hordered.
  assert (Hexcluded_cyl : QCylindric period excluded).
  { now apply finitary_qcylindric_implies_cylindric. }
  split.
  - intros stage Hstage. split.
    + eapply stripping_remainder_finitary; eauto.
    + apply (stripping_excluded_subset_remainder d period excluded
        initial_remaining faces Hperiodic
        (proj1 (proj2 (proj2 Hordered))) Hsubset stage Hstage).
  - intros stage face Hstage Hface.
    eapply stripping_slice_finitary; eauto.
Qed.

Theorem stripping_first_slice_empty : forall d
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
    Periodic period ->
    OrderedStrippingFaces period faces ->
    BackwardPeriodCover period excluded initial_remaining ->
    forall value,
      ~ StrippingSlice period excluded initial_remaining faces 0 value.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hordered
    Hcover value Hslice.
  destruct Hordered as
    [Hnonempty [Hhead [Hsound [Hcomplete [Hdistinct Horder]]]]].
  assert (Hlength : 0 < length faces).
  { destruct faces; [contradiction|cbn; lia]. }
  assert (Hinitial : initial_remaining value).
  { exact (proj1 (stripping_slice_subset_initial_difference d period excluded
      initial_remaining faces Hperiodic Hsound 0 Hlength value Hslice)). }
  destruct (Hcover value Hinitial) as [increment [Hincrement Hexcluded]].
  assert (Hextract : ExtractFace period (Cone period) excluded
      (StrippingRemainder period excluded initial_remaining faces 0) value).
  { apply (proj1 (stripping_slice_spec d period excluded initial_remaining
      faces 0 (Cone period) Hlength Hhead value)). exact Hslice. }
  destruct (Hextract increment) as [_ Hnot_excluded].
  - split; [exact Hincrement|]. now apply cone_contains_source.
  - contradiction.
Qed.

Theorem face_stripping_theorem : forall d
    (period excluded initial_remaining : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    exists faces : list (QSet d),
      OrderedStrippingFaces period faces /\
      nth_error faces 0 = Some (Cone period) /\
      SameSet
        (StrippingRemainder period excluded initial_remaining faces 0)
        initial_remaining /\
      SameSet
        (StrippingRemainder period excluded initial_remaining
          faces (length faces))
        excluded /\
      (forall stage,
        stage <= length faces ->
        FinitaryQCylindric period
          (StrippingRemainder period excluded initial_remaining faces stage) /\
        forall value,
          excluded value ->
          StrippingRemainder period excluded initial_remaining faces
            stage value) /\
      (forall stage face,
        stage < length faces ->
        nth_error faces stage = Some face ->
        FinitaryQCylindric (FacePeriod period face)
          (StrippingSlice period excluded initial_remaining faces stage) /\
        forall value,
          StrippingSlice period excluded initial_remaining faces stage value ->
          initial_remaining value /\ ~ excluded value) /\
      (forall earlier later,
        earlier < later ->
        later < length faces ->
        forall value,
          ~ (StrippingSlice period excluded initial_remaining faces earlier value /\
             StrippingSlice period excluded initial_remaining faces later value)) /\
      (forall value,
        (initial_remaining value /\ ~ excluded value) <->
        exists stage,
          stage < length faces /\
          StrippingSlice period excluded initial_remaining faces stage value) /\
      (BackwardPeriodCover period excluded initial_remaining ->
        forall value,
          ~ StrippingSlice period excluded initial_remaining faces 0 value).
Proof.
  intros d period excluded initial_remaining Hperiodic Hfinite Hfull
    Hexcluded_finite Hinitial_finite Hsubset.
  destruct (ordered_stripping_faces_exists d period excluded
    initial_remaining Hperiodic Hfinite) as [faces [Hordered Hzero]].
  exists faces. split; [exact Hordered|].
  split; [exact (proj1 (proj2 Hordered))|].
  split; [exact Hzero|].
  split.
  - eapply stripping_final_remainder_eq_excluded; eauto.
  - split.
    + intros stage Hstage.
      exact (proj1 (stripping_finitary_stage_package d period excluded
        initial_remaining faces Hperiodic Hfinite Hfull Hexcluded_finite
        Hinitial_finite Hsubset Hordered) stage Hstage).
    + split.
      * intros stage face Hstage Hface. split.
        -- exact (proj2 (stripping_finitary_stage_package d period excluded
            initial_remaining faces Hperiodic Hfinite Hfull Hexcluded_finite
            Hinitial_finite Hsubset Hordered) stage face Hstage Hface).
        -- intros value Hslice.
           eapply stripping_slice_subset_initial_difference; eauto.
           exact (proj1 (proj2 (proj2 Hordered))).
      * split.
        -- now apply stripping_partition_slices_disjoint.
        -- split.
           ++ now apply stripping_complete_partition.
           ++ now apply stripping_first_slice_empty.
Qed.
