From Coq Require Import Arith.PeanoNat Classical_Prop Lia List.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Cone FaceOrder Faces FaceStrippingExtract
  FaceStrippingLemma610 LatticeGordanInterface Periodic QConeCore
  RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.

Fixpoint StrippingRemainder {d}
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)) (stage : nat) : ZSet d :=
  match stage with
  | O => initial_remaining
  | S previous_stage =>
      let previous := StrippingRemainder period excluded initial_remaining
        faces previous_stage in
      match nth_error faces previous_stage with
      | Some face =>
          fun value =>
            previous value /\
            ~ ExtractFace period face excluded previous value
      | None => previous
      end
  end.

Definition StrippingSlice {d}
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)) (stage : nat) : ZSet d :=
  match nth_error faces stage with
  | Some face =>
      ExtractFace period face excluded
        (StrippingRemainder period excluded initial_remaining faces stage)
  | None => fun _ => False
  end.

Theorem stripping_remainder_zero : forall d
    (period excluded initial_remaining : ZSet d) faces,
    SameSet
      (StrippingRemainder period excluded initial_remaining faces 0)
      initial_remaining.
Proof. intros d period excluded initial_remaining faces value; reflexivity. Qed.

Theorem stripping_slice_spec : forall d
    (period excluded initial_remaining : ZSet d) faces stage face,
    stage < length faces ->
    nth_error faces stage = Some face ->
    SameSet
      (StrippingSlice period excluded initial_remaining faces stage)
      (ExtractFace period face excluded
        (StrippingRemainder period excluded initial_remaining faces stage)).
Proof.
  intros d period excluded initial_remaining faces stage face _ Hface value.
  unfold StrippingSlice. now rewrite Hface.
Qed.

Theorem stripping_slice_out_of_range : forall d
    (period excluded initial_remaining : ZSet d) faces stage,
    length faces <= stage ->
    forall value,
      ~ StrippingSlice period excluded initial_remaining faces stage value.
Proof.
  intros d period excluded initial_remaining faces stage Hstage value.
  unfold StrippingSlice.
  assert (Hnone : nth_error faces stage = None).
  { apply nth_error_None. lia. }
  now rewrite Hnone.
Qed.

Theorem stripping_remainder_succ : forall d
    (period excluded initial_remaining : ZSet d) faces stage,
    stage < length faces ->
    SameSet
      (StrippingRemainder period excluded initial_remaining faces (S stage))
      (fun value =>
        StrippingRemainder period excluded initial_remaining faces stage value /\
        ~ StrippingSlice period excluded initial_remaining faces stage value).
Proof.
  intros d period excluded initial_remaining faces stage _ value.
  cbn [StrippingRemainder]. unfold StrippingSlice.
  destruct (nth_error faces stage); cbn; tauto.
Qed.

Lemma stripping_remainder_step_subset : forall d
    (period excluded initial_remaining : ZSet d) faces stage value,
    StrippingRemainder period excluded initial_remaining faces (S stage) value ->
    StrippingRemainder period excluded initial_remaining faces stage value.
Proof.
  intros d period excluded initial_remaining faces stage value Hvalue.
  cbn [StrippingRemainder] in Hvalue.
  destruct (nth_error faces stage); tauto.
Qed.

Theorem stripping_remainder_subset_initial : forall d
    (period excluded initial_remaining : ZSet d) faces stage value,
    StrippingRemainder period excluded initial_remaining faces stage value ->
    initial_remaining value.
Proof.
  intros d period excluded initial_remaining faces stage.
  induction stage as [|stage IH]; intros value Hvalue.
  - exact Hvalue.
  - apply IH. now apply stripping_remainder_step_subset in Hvalue.
Qed.

Lemma stripping_remainder_decreasing : forall d
    (period excluded initial_remaining : ZSet d) faces earlier later,
    earlier <= later ->
    forall value,
      StrippingRemainder period excluded initial_remaining faces later value ->
      StrippingRemainder period excluded initial_remaining faces earlier value.
Proof.
  intros d period excluded initial_remaining faces earlier later Hle.
  induction Hle as [|later Hle IH]; intros value Hvalue.
  - exact Hvalue.
  - apply IH. now apply stripping_remainder_step_subset in Hvalue.
Qed.

Theorem stripping_slice_subset_remainder : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    (forall face, List.In face faces -> FaceOf (Cone period) face) ->
    forall stage,
      stage < length faces ->
      forall value,
        StrippingSlice period excluded initial_remaining faces stage value ->
        StrippingRemainder period excluded initial_remaining faces stage value.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfaces
    stage Hstage value Hslice.
  unfold StrippingSlice in Hslice.
  destruct (nth_error faces stage) as [face|] eqn:Hface;
    [|contradiction].
  pose proof (Hfaces face (nth_error_In _ _ Hface)) as Hface_of.
  pose proof (face_periodic d period face Hperiodic Hface_of) as Hface_periodic.
  exact (proj1 (extract_face_subset_difference d period excluded
    (StrippingRemainder period excluded initial_remaining faces stage)
    face Hface_periodic value Hslice)).
Qed.

Theorem stripping_slice_avoids_excluded : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    (forall face, List.In face faces -> FaceOf (Cone period) face) ->
    forall stage,
      stage < length faces ->
      forall value,
        StrippingSlice period excluded initial_remaining faces stage value ->
        ~ excluded value.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfaces
    stage Hstage value Hslice.
  unfold StrippingSlice in Hslice.
  destruct (nth_error faces stage) as [face|] eqn:Hface;
    [|contradiction].
  pose proof (Hfaces face (nth_error_In _ _ Hface)) as Hface_of.
  pose proof (face_periodic d period face Hperiodic Hface_of) as Hface_periodic.
  exact (proj2 (extract_face_subset_difference d period excluded
    (StrippingRemainder period excluded initial_remaining faces stage)
    face Hface_periodic value Hslice)).
Qed.

Corollary stripping_slice_subset_initial_difference : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    (forall face, List.In face faces -> FaceOf (Cone period) face) ->
    forall stage,
      stage < length faces ->
      forall value,
        StrippingSlice period excluded initial_remaining faces stage value ->
        initial_remaining value /\ ~ excluded value.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfaces
    stage Hstage value Hslice. split.
  - apply (stripping_remainder_subset_initial d period excluded
      initial_remaining faces stage value).
    now apply stripping_slice_subset_remainder.
  - now apply (stripping_slice_avoids_excluded d period excluded
      initial_remaining faces Hperiodic Hfaces stage Hstage value).
Qed.

Theorem stripping_excluded_subset_remainder : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    (forall face, List.In face faces -> FaceOf (Cone period) face) ->
    (forall value, excluded value -> initial_remaining value) ->
    forall stage,
      stage <= length faces ->
      forall value,
        excluded value ->
        StrippingRemainder period excluded initial_remaining faces stage value.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfaces Hsubset.
  induction stage as [|stage IH]; intros Hbound value Hexcluded.
  - now apply Hsubset.
  - assert (Hstage : stage < length faces) by lia.
    assert (Hstage_bound : stage <= length faces) by lia.
    assert (Hprevious :
        StrippingRemainder period excluded initial_remaining faces stage value).
    { apply IH; [lia|exact Hexcluded]. }
    assert (Hsome : nth_error faces stage <> None).
    { now apply nth_error_Some. }
    destruct (nth_error faces stage) as [face|] eqn:Hface;
      [|contradiction].
    cbn [StrippingRemainder]. rewrite Hface. split; [exact Hprevious|].
    pose proof (Hfaces face (nth_error_In _ _ Hface)) as Hface_of.
    exact (proj2 (excluded_subset_extract_remainder d period excluded
      (StrippingRemainder period excluded initial_remaining faces stage)
      face Hperiodic Hface_of
      (fun candidate Hcandidate => IH Hstage_bound candidate Hcandidate)
      value Hexcluded)).
Qed.

Definition ProcessedBefore {d}
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)) (stage : nat) : ZSet d :=
  fun value =>
    exists earlier,
      earlier < stage /\
      StrippingSlice period excluded initial_remaining faces earlier value.

Lemma processed_before_succ : forall d
    (period excluded initial_remaining : ZSet d) faces stage value,
    ProcessedBefore period excluded initial_remaining faces (S stage) value <->
    ProcessedBefore period excluded initial_remaining faces stage value \/
    StrippingSlice period excluded initial_remaining faces stage value.
Proof.
  intros d period excluded initial_remaining faces stage value. split.
  - intros [earlier [Hearlier Hslice]].
    destruct (Nat.eq_dec earlier stage) as [->|Hneq].
    + now right.
    + left. exists earlier. split; [lia|exact Hslice].
  - intros [[earlier [Hearlier Hslice]]|Hslice].
    + exists earlier. split; [lia|exact Hslice].
    + exists stage. split; [lia|exact Hslice].
Qed.

Theorem stripping_remainder_characterization : forall d
    (period excluded initial_remaining : ZSet d) faces stage,
    stage <= length faces ->
    SameSet
      (StrippingRemainder period excluded initial_remaining faces stage)
      (fun value =>
        initial_remaining value /\
        ~ ProcessedBefore period excluded initial_remaining faces stage value).
Proof.
  intros d period excluded initial_remaining faces stage.
  induction stage as [|stage IH]; intros Hbound value.
  - unfold ProcessedBefore. cbn [StrippingRemainder]. split.
    + intro Hvalue. split; [exact Hvalue|]. intros [earlier [Hearlier _]]. lia.
    + tauto.
  - assert (Hstage : stage < length faces) by lia.
    assert (Hstage_bound : stage <= length faces) by lia.
    specialize (IH Hstage_bound value).
    pose proof (stripping_remainder_succ d period excluded initial_remaining
      faces stage Hstage value) as Hsucc.
    pose proof (processed_before_succ d period excluded initial_remaining
      faces stage value) as Hprocessed.
    tauto.
Qed.

Lemma stripping_processed_subset_initial : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    (forall face, List.In face faces -> FaceOf (Cone period) face) ->
    forall stage,
      stage <= length faces ->
      forall value,
        ProcessedBefore period excluded initial_remaining faces stage value ->
        initial_remaining value.
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfaces
    stage Hbound value [earlier [Hearlier Hslice]].
  eapply stripping_remainder_subset_initial.
  eapply stripping_slice_subset_remainder; try eassumption. lia.
Qed.

Theorem stripping_initial_partition : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    (forall face, List.In face faces -> FaceOf (Cone period) face) ->
    forall stage,
      stage <= length faces ->
      SameSet initial_remaining
        (fun value =>
          StrippingRemainder period excluded initial_remaining faces stage value
          \/ ProcessedBefore period excluded initial_remaining faces stage value).
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfaces
    stage Hbound value. split.
  - intro Hinitial.
    destruct (classic
      (ProcessedBefore period excluded initial_remaining faces stage value))
      as [Hprocessed|Hnot_processed]; [now right|left].
    apply (proj2 (stripping_remainder_characterization d period excluded
      initial_remaining faces stage Hbound value)). now split.
  - intros [Hremainder|Hprocessed].
    + now apply stripping_remainder_subset_initial in Hremainder.
    + eapply stripping_processed_subset_initial; eassumption.
Qed.

Theorem stripping_remainder_processed_disjoint : forall d
    (period excluded initial_remaining : ZSet d) faces stage,
    stage <= length faces ->
    forall value,
      ~ (StrippingRemainder period excluded initial_remaining faces stage value /\
         ProcessedBefore period excluded initial_remaining faces stage value).
Proof.
  intros d period excluded initial_remaining faces stage Hbound value
    [Hremainder Hprocessed].
  apply (proj1 (stripping_remainder_characterization d period excluded
    initial_remaining faces stage Hbound value)) in Hremainder.
  tauto.
Qed.

Theorem stripping_slices_disjoint : forall d
    (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    (forall face, List.In face faces -> FaceOf (Cone period) face) ->
    forall earlier later,
      earlier < later ->
      later < length faces ->
      forall value,
        ~ (StrippingSlice period excluded initial_remaining faces earlier value /\
           StrippingSlice period excluded initial_remaining faces later value).
Proof.
  intros d period excluded initial_remaining faces Hperiodic Hfaces
    earlier later Hlt Hlater value [Hearlier Hlater_slice].
  assert (Hlater_remainder :
      StrippingRemainder period excluded initial_remaining faces later value).
  { eapply stripping_slice_subset_remainder; eassumption. }
  assert (Hsuccessor_remainder :
      StrippingRemainder period excluded initial_remaining faces
        (S earlier) value).
  { apply (stripping_remainder_decreasing d period excluded initial_remaining
      faces (S earlier) later); [lia|exact Hlater_remainder]. }
  pose proof (stripping_remainder_succ d period excluded initial_remaining
    faces earlier ltac:(lia) value) as Hsucc.
  apply Hsucc in Hsuccessor_remainder. tauto.
Qed.

Definition StageCandidateFace {d}
    (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)) (stage : nat) (face : QSet d) : Prop :=
  FaceOf (Cone period) face /\
  exists value,
    ExtractFace period face excluded
      (StrippingRemainder period excluded initial_remaining faces stage) value.

Theorem face_stripping_ordered_recursion : forall d
    (period excluded initial_remaining : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    exists faces : list (QSet d),
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
        FaceSubset face_j face_i -> i <= j) /\
      SameSet
        (StrippingRemainder period excluded initial_remaining faces 0)
        initial_remaining.
Proof.
  intros d period excluded initial_remaining Hperiodic Hfinite.
  pose proof (finitely_generated_period_cone_polyhedral d period
    Hperiodic Hfinite) as Hpolyhedral.
  destruct (polyhedral_faces_linearized d (Cone period) Hpolyhedral) as
    [faces [[tail Hfaces] [Hsound [Hcomplete [Hdistinct Hordered]]]]].
  subst faces. exists (Cone period :: tail). split; [discriminate|].
  split; [reflexivity|]. split; [exact Hsound|]. split; [exact Hcomplete|].
  split; [exact Hdistinct|]. split; [exact Hordered|].
  apply stripping_remainder_zero.
Qed.
