From Coq Require Import Arith.PeanoNat Lia List.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone Faces
  FaceStrippingExtract FaceStrippingFinitary FaceStrippingLemma611
  FaceStrippingRecursion FaceStrippingTheorem LatticeGordanInterface
  Periodic QConeCore RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Definition QDiagonal {d}
    (period : ZSet d)
    (relation : ZVec d -> ZVec d -> Prop) : Prop :=
  forall left right increment,
    relation left right ->
    period increment ->
    relation
      (zvec_add left increment)
      (zvec_add right increment).

Definition NoBoundaryEdge {d}
    (excluded remaining : ZSet d)
    (relation : ZVec d -> ZVec d -> Prop) : Prop :=
  forall left right,
    relation left right ->
    excluded left ->
    remaining right ->
    ~ excluded right ->
    False.

Theorem stripping_slice_face_cylindric : forall d
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)) stage face,
    Periodic period ->
    (forall candidate,
      List.In candidate faces -> FaceOf (Cone period) candidate) ->
    nth_error faces stage = Some face ->
    QCylindric
      (FacePeriod period face)
      (StrippingSlice period excluded initial_remaining faces stage).
Proof.
  intros d period excluded initial_remaining faces stage face Hperiodic
    Hfaces Hface.
  unfold StrippingSlice. rewrite Hface.
  apply extract_face_cylindric.
  apply face_periodic; [exact Hperiodic|].
  apply Hfaces. now apply nth_error_In with (n := stage).
Qed.

Theorem stripping_later_slice_in_earlier_remainder : forall d
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)) earlier later,
    Periodic period ->
    (forall face,
      List.In face faces -> FaceOf (Cone period) face) ->
    earlier < later ->
    later < length faces ->
    forall value,
      StrippingSlice period excluded initial_remaining faces later value ->
      StrippingRemainder period excluded initial_remaining faces earlier value.
Proof.
  intros d period excluded initial_remaining faces earlier later Hperiodic
    Hfaces Hearlier Hlater value Hslice.
  apply (stripping_remainder_decreasing d period excluded initial_remaining
    faces earlier later); [lia|].
  eapply stripping_slice_subset_remainder; eassumption.
Qed.

Theorem lemma_6_3_stripping_diagonal_core : forall d
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d))
    (relation : ZVec d -> ZVec d -> Prop),
    Periodic period ->
    (forall face,
      List.In face faces -> FaceOf (Cone period) face) ->
    (forall stage,
      stage <= length faces ->
      QCylindric period
        (StrippingRemainder period excluded initial_remaining faces stage)) ->
    QDiagonal period relation ->
    NoBoundaryEdge excluded initial_remaining relation ->
    forall earlier later left right,
      earlier < later ->
      later < length faces ->
      StrippingSlice period excluded initial_remaining faces later left ->
      StrippingSlice period excluded initial_remaining faces earlier right ->
      ~ relation left right.
Proof.
  intros d period excluded initial_remaining faces relation Hperiodic Hfaces
    Hremainders Hdiagonal Hboundary earlier later left right Hearlier Hlater
    Hleft Hright Hrelation.
  assert (Hearlier_bound : earlier < length faces) by lia.
  destruct (nth_error faces earlier) as [face|] eqn:Hface.
  2: { apply nth_error_None in Hface. lia. }
  assert (Hright_cylindric : QCylindric (FacePeriod period face)
      (StrippingSlice period excluded initial_remaining faces earlier)).
  { eapply stripping_slice_face_cylindric; eassumption. }
  assert (Hleft_remainder : StrippingRemainder period excluded
      initial_remaining faces earlier left).
  { exact (stripping_later_slice_in_earlier_remainder d period excluded
      initial_remaining faces earlier later Hperiodic Hfaces Hearlier Hlater
      left Hleft). }
  assert (Hleft_extract : ExtractFace period face excluded
      (StrippingRemainder period excluded initial_remaining faces earlier)
      left).
  { intros increment Hincrement.
    assert (Hright_shift : StrippingSlice period excluded initial_remaining
        faces earlier (zvec_add right increment)).
    { eapply Hright_cylindric; eassumption. }
    assert (Hright_difference :
        initial_remaining (zvec_add right increment) /\
        ~ excluded (zvec_add right increment)).
    { eapply stripping_slice_subset_initial_difference; eassumption. }
    assert (Hshift_relation : relation
        (zvec_add left increment) (zvec_add right increment)).
    { eapply Hdiagonal; [exact Hrelation|exact (proj1 Hincrement)]. }
    split.
    - exact (Hremainders earlier ltac:(lia) left increment Hleft_remainder
        (proj1 Hincrement)).
    - intro Hleft_excluded.
      destruct Hright_difference as [Hright_remaining Hright_not_excluded].
      eapply Hboundary; eassumption.
  }
  assert (Hleft_earlier : StrippingSlice period excluded initial_remaining
      faces earlier left).
  { unfold StrippingSlice. now rewrite Hface. }
  eapply (stripping_slices_disjoint d period excluded initial_remaining faces
    Hperiodic Hfaces earlier later Hearlier Hlater left).
  now split.
Qed.

Theorem lemma_6_3_stripping_diagonal : forall d
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d))
    (relation : ZVec d -> ZVec d -> Prop),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value,
      excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces ->
    QDiagonal period relation ->
    NoBoundaryEdge excluded initial_remaining relation ->
    forall earlier later left right,
      earlier < later ->
      later < length faces ->
      StrippingSlice period excluded initial_remaining faces later left ->
      StrippingSlice period excluded initial_remaining faces earlier right ->
      ~ relation left right.
Proof.
  intros d period excluded initial_remaining faces relation Hperiodic _ _
    Hexcluded Hremaining Hsubset Hordered Hdiagonal Hboundary.
  assert (Hexcluded_cylindric : QCylindric period excluded).
  { now apply finitary_qcylindric_implies_cylindric. }
  assert (Hremaining_cylindric : QCylindric period initial_remaining).
  { now apply finitary_qcylindric_implies_cylindric. }
  destruct (lemma_6_11_stripping_invariants d period excluded
    initial_remaining faces Hperiodic Hexcluded_cylindric
    Hremaining_cylindric Hsubset Hordered) as [Hremainders _].
  eapply lemma_6_3_stripping_diagonal_core; eauto.
  exact (proj1 (proj2 (proj2 Hordered))).
Qed.

Theorem face_stripping_theorem_diagonal : forall d
    (period excluded initial_remaining : ZSet d)
    (relation : ZVec d -> ZVec d -> Prop),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value,
      excluded value -> initial_remaining value) ->
    QDiagonal period relation ->
    NoBoundaryEdge excluded initial_remaining relation ->
    exists faces : list (QSet d),
      (OrderedStrippingFaces period faces /\
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
           ~ StrippingSlice period excluded initial_remaining faces 0 value)) /\
      (forall earlier later left right,
        earlier < later ->
        later < length faces ->
        StrippingSlice period excluded initial_remaining faces later left ->
        StrippingSlice period excluded initial_remaining faces earlier right ->
        ~ relation left right).
Proof.
  intros d period excluded initial_remaining relation Hperiodic Hfinite Hfull
    Hexcluded Hremaining Hsubset Hdiagonal Hboundary.
  destruct (face_stripping_theorem d period excluded initial_remaining
    Hperiodic Hfinite Hfull Hexcluded Hremaining Hsubset) as
    [faces Hstripping].
  exists faces. split; [exact Hstripping|].
  eapply lemma_6_3_stripping_diagonal; eauto.
  exact (proj1 Hstripping).
Qed.
