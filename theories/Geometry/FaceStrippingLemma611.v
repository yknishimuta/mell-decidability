From Coq Require Import Arith.PeanoNat Classical_Prop Lia List.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone Corollary67Finitary FaceOrder Faces
  FaceStrippingExtract FaceStrippingFinitary FaceStrippingLemma610FiniteBasis
  FaceStrippingOrderFoundation FaceStrippingRecursion Periodic QConeCore
  RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.

Definition OrderedStrippingFaces {d}
    (period : ZSet d) (faces : list (QSet d)) : Prop :=
  faces <> [] /\
  nth_error faces 0 = Some (Cone period) /\
  (forall face,
    List.In face faces -> FaceOf (Cone period) face) /\
  (forall face,
    FaceOf (Cone period) face ->
    exists representative,
      List.In representative faces /\
      SameSet face representative) /\
  (forall i j face_i face_j,
    nth_error faces i = Some face_i ->
    nth_error faces j = Some face_j ->
    i <> j -> ~ SameSet face_i face_j) /\
  (forall i j face_i face_j,
    nth_error faces i = Some face_i ->
    nth_error faces j = Some face_j ->
    FaceSubset face_j face_i -> i <= j).

Theorem ordered_stripping_faces_exists : forall d
    (period excluded initial_remaining : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    exists faces,
      OrderedStrippingFaces period faces /\
      SameSet
        (StrippingRemainder period excluded initial_remaining faces 0)
        initial_remaining.
Proof.
  intros d period excluded initial_remaining Hperiodic Hfinite.
  destruct (face_stripping_ordered_recursion d period excluded
    initial_remaining Hperiodic Hfinite) as
    [faces [Hnonempty [Hhead [Hsound [Hcomplete
      [Hdistinct [Hordered Hzero]]]]]]].
  exists faces. split; [|exact Hzero].
  unfold OrderedStrippingFaces. repeat split; assumption.
Qed.

Lemma extract_face_remaining_monotone : forall d
    (period excluded smaller larger : ZSet d) (face : QSet d),
    (forall value, smaller value -> larger value) ->
    forall value,
      ExtractFace period face excluded smaller value ->
      ExtractFace period face excluded larger value.
Proof.
  intros d period excluded smaller larger face Hsubset value Hextract
    increment Hincrement.
  destruct (Hextract increment Hincrement) as [Hsmall Hnot].
  split; [now apply Hsubset|exact Hnot].
Qed.

Lemma stripping_candidate_monotone : forall d
    (period excluded initial_remaining : ZSet d) faces stage face,
    StageCandidateFace period excluded initial_remaining faces (S stage) face ->
    StageCandidateFace period excluded initial_remaining faces stage face.
Proof.
  intros d period excluded initial_remaining faces stage face
    [Hface [value Hextract]]. split; [exact Hface|]. exists value.
  eapply extract_face_remaining_monotone; [|exact Hextract].
  intros candidate Hcandidate.
  now apply stripping_remainder_step_subset in Hcandidate.
Qed.

Lemma stripping_current_face_eliminated : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    (forall face, List.In face faces -> FaceOf (Cone period) face) ->
    forall stage face,
      stage < length faces ->
      nth_error faces stage = Some face ->
      ~ StageCandidateFace period excluded initial_remaining
          faces (S stage) face.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hsound
    stage face Hstage Hface [Hface_of [value Hextract]].
  assert (Hface_periodic : Periodic (FacePeriod period face)).
  { apply face_periodic; [exact Hperiodic|exact Hface_of]. }
  assert (Hnext : StrippingRemainder period excluded initial_remaining
      faces (S stage) value).
  { exact (proj1 (extract_face_subset_difference d period excluded
      (StrippingRemainder period excluded initial_remaining faces (S stage))
      face Hface_periodic value Hextract)). }
  assert (Hcurrent_extract : ExtractFace period face excluded
      (StrippingRemainder period excluded initial_remaining faces stage)
      value).
  { eapply extract_face_remaining_monotone; [|exact Hextract].
    intros candidate Hcandidate.
    now apply stripping_remainder_step_subset in Hcandidate. }
  assert (Hslice : StrippingSlice period excluded initial_remaining
      faces stage value).
  { unfold StrippingSlice. now rewrite Hface. }
  apply (proj1 (stripping_remainder_succ d period excluded
    initial_remaining faces stage Hstage value)) in Hnext.
  tauto.
Qed.

Lemma stripping_current_face_same_set_eliminated : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    (forall face, List.In face faces -> FaceOf (Cone period) face) ->
    forall stage current candidate,
      stage < length faces ->
      nth_error faces stage = Some current ->
      SameSet current candidate ->
      ~ StageCandidateFace period excluded initial_remaining
          faces (S stage) candidate.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hsound
    stage current candidate Hstage Hcurrent Hsame
    [Hcandidate [value Hextract]].
  apply (stripping_current_face_eliminated d period excluded
    initial_remaining faces Hperiodic Hsound stage current Hstage Hcurrent).
  split.
  - apply Hsound. now apply nth_error_In with (n := stage).
  - exists value.
    apply (proj2 (extract_face_same_set d period excluded
      (StrippingRemainder period excluded initial_remaining faces (S stage))
      current candidate Hsame value)).
    exact Hextract.
Qed.

Lemma stripping_remainders_cylindric : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    QCylindric period excluded ->
    QCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    (forall face, List.In face faces -> FaceOf (Cone period) face) ->
    forall stage,
      stage <= length faces ->
      QCylindric period
        (StrippingRemainder period excluded initial_remaining faces stage).
Proof.
  intros d period excluded initial_remaining faces Hperiodic
    Hexcluded_cyl Hinitial_cyl Hsubset Hsound.
  induction stage as [|stage IH]; intros Hbound.
  - exact Hinitial_cyl.
  - assert (Hstage : stage < length faces) by lia.
    assert (Hprevious_cyl : QCylindric period
        (StrippingRemainder period excluded initial_remaining faces stage)).
    { apply IH. lia. }
    assert (Hexcluded_previous : forall value,
        excluded value ->
        StrippingRemainder period excluded initial_remaining faces stage value).
    { intros value Hvalue.
      eapply stripping_excluded_subset_remainder; eauto; lia. }
    destruct (nth_error faces stage) as [face|] eqn:Hface.
    + cbn [StrippingRemainder]. rewrite Hface.
      apply extract_remainder_cylindric; try assumption.
      apply Hsound. now apply nth_error_In with (n := stage).
    + apply nth_error_None in Hface. lia.
Qed.

Lemma stripping_candidates_represented_later : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    OrderedStrippingFaces period faces ->
    forall stage,
      stage <= length faces ->
      forall face,
        StageCandidateFace period excluded initial_remaining faces stage face ->
        exists index representative,
          stage <= index /\
          index < length faces /\
          nth_error faces index = Some representative /\
          SameSet face representative.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hordered.
  destruct Hordered as
    [Hnonempty [Hhead [Hsound [Hcomplete [Hdistinct Horder]]]]].
  intro stage. induction stage as [|previous IH]; intros Hbound face Hcandidate.
  - destruct (Hcomplete face (proj1 Hcandidate)) as
      [representative [Hin Hsame]].
    apply In_nth_error in Hin as [index Hindex].
    exists index, representative. split; [lia|]. split.
    + apply nth_error_Some. now rewrite Hindex.
    + split; assumption.
  - assert (Hstage : previous < length faces) by lia.
    assert (Hcandidate_previous : StageCandidateFace period excluded
        initial_remaining faces previous face).
    { now apply stripping_candidate_monotone in Hcandidate. }
    destruct (IH ltac:(lia) face Hcandidate_previous) as
      [index [representative [Hstage_index [Hindex_bound
        [Hindex Hsame]]]]].
    assert (Hstrict : S previous <= index).
    { destruct (Nat.eq_dec index previous) as [Heq|Hneq]; [|lia].
      subst index.
      destruct (nth_error faces previous) as [current|] eqn:Hcurrent.
      - injection Hindex as Hrepresentative. subst representative.
        exfalso.
        apply (stripping_current_face_same_set_eliminated d period excluded
          initial_remaining faces Hperiodic Hsound previous current face
          Hstage Hcurrent).
        + intro point. specialize (Hsame point). tauto.
        + exact Hcandidate.
      - apply nth_error_None in Hcurrent. lia. }
    exists index, representative. split; [exact Hstrict|].
    split; [exact Hindex_bound|]. split; assumption.
Qed.

Theorem lemma_6_11_stripping_invariants : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    QCylindric period excluded ->
    QCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces ->
    (forall stage,
      stage <= length faces ->
      QCylindric period
        (StrippingRemainder period excluded initial_remaining faces stage)) /\
    (forall stage,
      stage <= length faces ->
      forall face,
        StageCandidateFace period excluded initial_remaining faces stage face ->
        exists index representative,
          stage <= index /\
          index < length faces /\
          nth_error faces index = Some representative /\
          SameSet face representative).
Proof.
  intros d period excluded initial_remaining faces Hperiodic
    Hexcluded Hinitial Hsubset Hordered. split.
  - eapply stripping_remainders_cylindric; eauto.
    exact (proj1 (proj2 (proj2 Hordered))).
  - now apply stripping_candidates_represented_later.
Qed.

Theorem stripping_remainder_finitary : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    QCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces ->
    forall stage,
      stage <= length faces ->
      FinitaryQCylindric period
        (StrippingRemainder period excluded initial_remaining faces stage).
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfinite
    Hexcluded Hinitial_finite Hsubset Hordered stage Hstage.
  assert (Hinitial_cyl : QCylindric period initial_remaining).
  { now apply finitary_qcylindric_implies_cylindric. }
  assert (Hremainder_cyl : QCylindric period
      (StrippingRemainder period excluded initial_remaining faces stage)).
  { eapply stripping_remainders_cylindric; eauto.
    exact (proj1 (proj2 (proj2 Hordered))). }
  eapply finitary_qcylindric_sub; eauto.
  intros value Hvalue.
  now apply stripping_remainder_subset_initial in Hvalue.
Qed.

Theorem stripping_nonempty_slice_maximal_face : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    OrderedStrippingFaces period faces ->
    forall stage face,
      stage < length faces ->
      nth_error faces stage = Some face ->
      (exists value,
        StrippingSlice period excluded initial_remaining faces stage value) ->
      MaximalNonemptyExtractFace period excluded
        (StrippingRemainder period excluded initial_remaining faces stage)
        face.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hordered
    stage face Hstage Hface [value Hslice].
  destruct Hordered as
    [Hnonempty [Hhead [Hsound [Hcomplete [Hdistinct Horder]]]]].
  assert (Hface_of : FaceOf (Cone period) face).
  { apply Hsound. now apply nth_error_In with (n := stage). }
  assert (Hextract : ExtractFace period face excluded
      (StrippingRemainder period excluded initial_remaining faces stage)
      value).
  { apply (proj1 (stripping_slice_spec d period excluded initial_remaining
      faces stage face Hstage Hface value)). exact Hslice. }
  split; [exact Hface_of|]. split; [now exists value|].
  intros larger Hlarger Hsubset [larger_value Hlarger_extract].
  assert (Hcandidate : StageCandidateFace period excluded initial_remaining
      faces stage larger).
  { split; [exact Hlarger|now exists larger_value]. }
  assert (Hordered_all : OrderedStrippingFaces period faces).
  { unfold OrderedStrippingFaces. repeat split; assumption. }
  destruct (stripping_candidates_represented_later d period excluded
    initial_remaining faces Hperiodic Hordered_all stage ltac:(lia)
    larger Hcandidate) as
    [index [representative [Hstage_index [Hindex_bound
      [Hrepresentative Hsame]]]]].
  assert (Hface_subset_representative : FaceSubset face representative).
  { intros point Hpoint.
    apply (proj1 (Hsame point)), Hsubset, Hpoint. }
  assert (Hindex_stage : index <= stage).
  { eapply Horder; eauto. }
  assert (Heq : index = stage) by lia. subst index.
  rewrite Hface in Hrepresentative.
  injection Hrepresentative as Hrep. subst representative.
  intro point. specialize (Hsame point). tauto.
Qed.

Theorem stripping_slice_finitary : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces ->
    forall stage face,
      stage < length faces ->
      nth_error faces stage = Some face ->
      FinitaryQCylindric (FacePeriod period face)
        (StrippingSlice period excluded initial_remaining faces stage).
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfinite Hfull
    Hexcluded_finite Hinitial_finite Hsubset Hordered stage face Hstage Hface.
  destruct (classic (exists value,
      StrippingSlice period excluded initial_remaining faces stage value))
    as [Hnonempty|Hempty].
  - assert (Hexcluded_cyl : QCylindric period excluded).
    { now apply finitary_qcylindric_implies_cylindric. }
    assert (Hremainder_finite : FinitaryQCylindric period
        (StrippingRemainder period excluded initial_remaining faces stage)).
    { eapply stripping_remainder_finitary; eauto. lia. }
    assert (Hexcluded_remainder : forall value,
        excluded value ->
        StrippingRemainder period excluded initial_remaining faces stage value).
    { intros value Hvalue.
      eapply stripping_excluded_subset_remainder; eauto.
      - exact (proj1 (proj2 (proj2 Hordered))).
      - lia. }
    assert (Hmaximal : MaximalNonemptyExtractFace period excluded
        (StrippingRemainder period excluded initial_remaining faces stage)
        face).
    { eapply stripping_nonempty_slice_maximal_face; eauto. }
    assert (Hextract_finite : FinitaryQCylindric (FacePeriod period face)
        (ExtractFace period face excluded
          (StrippingRemainder period excluded initial_remaining faces stage))).
    { eapply lemma_6_10_maximal_extract_finitary; eauto. }
    eapply finitary_qcylindric_congr; [| |exact Hextract_finite].
    + intro value. reflexivity.
    + intro value. symmetry.
      apply stripping_slice_spec with (face := face); assumption.
  - eapply finitary_qcylindric_congr;
      [| |apply empty_finitary_qcylindric].
    + intro value. reflexivity.
    + intro value. split; [intro Hfalse; contradiction|].
      intro Hslice. exfalso. apply Hempty. now exists value.
Qed.

Theorem stripping_no_candidate_at_end : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    OrderedStrippingFaces period faces ->
    forall face,
      ~ StageCandidateFace period excluded initial_remaining
          faces (length faces) face.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hordered
    face Hcandidate.
  destruct (stripping_candidates_represented_later d period excluded
    initial_remaining faces Hperiodic Hordered (length faces)
    (Nat.le_refl _) face Hcandidate) as
    [index [representative [Hlower [Hupper _]]]].
  lia.
Qed.
