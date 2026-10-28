From Coq Require Import Classical_Prop Lia List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Geometry Require Import ClosedLinearization CommonIntegerFaceNormals Cone
  Corollary67Finitary FaceOrder Faces FaceStrippingExtract
  FaceStrippingFinitary FaceStrippingGeometricCore
  FaceStrippingMonotoneSubsequence FaceStrippingOrderFoundation
  LatticeGordanInterface LatticeGordanV MathCompBridge Periodic QConeCore
  RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.

Definition ShiftedSet {d} (anchor : ZVec d) (set : ZSet d) : ZSet d :=
  fun value => set (zvec_add anchor value).

Lemma zvec_add_sub_right : forall d (anchor value : ZVec d),
    zvec_add anchor (zvec_sub value anchor) = value.
Proof. apply zvec_sub_add_cancel. Qed.

Lemma zvec_sub_shift : forall d (anchor value increment : ZVec d),
    zvec_sub (zvec_add value increment) anchor =
      zvec_add (zvec_sub value anchor) increment.
Proof.
  intros d anchor value increment. apply zvec_ext. intro coordinate.
  unfold zvec_sub, zvec_add.
  repeat rewrite (nth_map2 _ _ _ coordinate coordinate coordinate
    eq_refl eq_refl). lia.
Qed.

Lemma shifted_set_roundtrip : forall d (anchor : ZVec d) set value,
    ShiftedSet anchor set (zvec_sub value anchor) <-> set value.
Proof.
  intros. unfold ShiftedSet. rewrite zvec_add_sub_right. reflexivity.
Qed.

Lemma shifted_set_qcylindric : forall d (period set : ZSet d) anchor,
    QCylindric period set -> QCylindric period (ShiftedSet anchor set).
Proof.
  intros d period set anchor Hcylindric base increment Hbase Hincrement.
  unfold ShiftedSet in *. rewrite <- zvec_add_assoc.
  now apply Hcylindric.
Qed.

Lemma shifted_set_finitary_qcylindric : forall d
    (period set : ZSet d) anchor,
    FinitaryQCylindric period set ->
    FinitaryQCylindric period (ShiftedSet anchor set).
Proof.
  intros d period set anchor [bases Hbases].
  exists (List.map (fun base => zvec_sub base anchor) bases).
  intro value. unfold ShiftedSet. split.
  - intro Hvalue. apply (proj1 (Hbases _)) in Hvalue.
    destruct Hvalue as [base [increment [Hbase [Hincrement Heq]]]].
    exists (zvec_sub base anchor), increment. repeat split.
    + apply in_map_iff. exists base. now split.
    + exact Hincrement.
    + apply zvec_ext. intro coordinate.
      apply (f_equal (fun vector => Vector.nth vector coordinate)) in Heq.
      unfold zvec_add, zvec_sub in *.
      rewrite (nth_map2 Z.add anchor value coordinate coordinate coordinate
        eq_refl eq_refl) in Heq.
      rewrite (nth_map2 Z.add base increment coordinate coordinate coordinate
        eq_refl eq_refl) in Heq.
      rewrite (nth_map2 Z.add (Vector.map2 Z.sub base anchor) increment
        coordinate coordinate coordinate eq_refl eq_refl).
      rewrite (nth_map2 Z.sub base anchor coordinate coordinate coordinate
        eq_refl eq_refl). lia.
  - intros [shifted_base [increment [Hbase [Hincrement Heq]]]].
    apply in_map_iff in Hbase.
    destruct Hbase as [base [Hbase_eq Hbase]]. subst shifted_base.
    apply (proj2 (Hbases _)). exists base, increment.
    repeat split; try assumption.
    apply zvec_ext. intro coordinate.
    apply (f_equal (fun vector => Vector.nth vector coordinate)) in Heq.
    unfold zvec_add, zvec_sub in *.
    rewrite (nth_map2 Z.add (Vector.map2 Z.sub base anchor) increment
      coordinate coordinate coordinate eq_refl eq_refl) in Heq.
    rewrite (nth_map2 Z.sub base anchor coordinate coordinate coordinate
      eq_refl eq_refl) in Heq.
    rewrite (nth_map2 Z.add anchor value coordinate coordinate coordinate
      eq_refl eq_refl).
    rewrite (nth_map2 Z.add base increment coordinate coordinate coordinate
      eq_refl eq_refl). lia.
Qed.

Lemma shifted_set_subset : forall d (anchor : ZVec d) left right,
    (forall value, left value -> right value) ->
    forall value, ShiftedSet anchor left value -> ShiftedSet anchor right value.
Proof. firstorder. Qed.

Theorem shifted_extract_face : forall d
    (period excluded remaining : ZSet d) (face : QSet d) anchor value,
    ExtractFace period face
      (ShiftedSet anchor excluded) (ShiftedSet anchor remaining) value <->
    ExtractFace period face excluded remaining (zvec_add anchor value).
Proof.
  intros d period excluded remaining face anchor value.
  unfold ExtractFace, ShiftedSet. split; intros Hextract increment Hincrement;
    specialize (Hextract increment Hincrement).
  - now rewrite zvec_add_assoc.
  - now rewrite <- zvec_add_assoc.
Qed.

Theorem shifted_maximal_nonempty_extract_face : forall d
    (period excluded remaining : ZSet d) (face : QSet d) anchor,
    MaximalNonemptyExtractFace period excluded remaining face ->
    MaximalNonemptyExtractFace period
      (ShiftedSet anchor excluded) (ShiftedSet anchor remaining) face.
Proof.
  intros d period excluded remaining face anchor
    [Hface [[witness Hwitness] Hmaximal]].
  split; [exact Hface|]. split.
  - exists (zvec_sub witness anchor).
    apply (proj2 (shifted_extract_face d period excluded remaining face
      anchor (zvec_sub witness anchor))).
    now rewrite zvec_add_sub_right.
  - intros larger Hlarger Hsubset [value Hvalue].
    apply Hmaximal; [exact Hlarger|exact Hsubset|].
    exists (zvec_add anchor value).
    now apply (proj1 (shifted_extract_face d period excluded remaining larger
      anchor value)).
Qed.

Lemma qcone_combination_mapped_to_conegen : forall d
    (period : ZSet d) generators,
    (forall generator, List.In generator generators -> period generator) ->
    forall generated,
      QConeCombination (List.map zvec_to_qvec generators) generated ->
      ConeGen period generated.
Proof.
  intros d period generators Hgenerators generated Hgenerated.
  induction Hgenerated.
  - constructor.
  - apply in_map_iff in H0.
    destruct H0 as [integer_generator [<- Hin]].
    constructor; [exact H|now apply Hgenerators|exact IHHgenerated].
Qed.

Lemma qcone_mapped_generators_in_period_cone : forall d
    (period : ZSet d) generators,
    (forall generator, List.In generator generators -> period generator) ->
    forall point,
      qcone_generated (List.map zvec_to_qvec generators) point ->
      Cone period point.
Proof.
  intros d period generators Hgenerators point
    [generated [Hgenerated Hpoint]].
  exists generated. split; [|exact Hpoint].
  now apply qcone_combination_mapped_to_conegen with (generators := generators).
Qed.

Lemma generated_value_in_mapped_qcone : forall d
    (generators : list (ZVec d)) value,
    zvec_generated generators value ->
    qcone_generated (List.map zvec_to_qvec generators)
      (zvec_to_qvec value).
Proof.
  intros d generators value [coefficients Hcoefficients].
  assert (Heq : QVecEq (zvec_to_qvec value)
      (qlinear_combination (List.map zvec_to_qvec generators)
        (List.map q_of_nat (Vector.to_list coefficients)))).
  { rewrite <- Hcoefficients. apply zlinear_combination_to_qvec.
    apply length_to_list.
  }
  apply (proj2 (qcone_generated_qvec_ext d _ _ _ Heq)).
  apply qlinear_combination_cone.
  - rewrite !List.length_map. apply length_to_list.
  - apply List.Forall_forall. intros coefficient Hin.
    apply in_map_iff in Hin. destruct Hin as [natural [<- _]].
    unfold q_of_nat, Qle. cbn. lia.
Qed.

Theorem finitely_generated_period_cone_polyhedral : forall d
    (period : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    RationalPolyhedralCone (Cone period).
Proof.
  intros d period Hperiodic
    [generators [Hgenerators Hgenerated]].
  exists (List.map zvec_to_qvec generators). intro point. split.
  - intro Hpoint.
    apply (proj1 (periodic_standard_cone_denominator_clearing
      d period point Hperiodic)) in Hpoint.
    destruct Hpoint as [denominator [value
      [Hdenominator [Hvalue Hpoint]]]].
    assert (Hvalue_qcone : qcone_generated
        (List.map zvec_to_qvec generators) (zvec_to_qvec value)).
    { apply generated_value_in_mapped_qcone, (proj1 (Hgenerated value)).
      exact Hvalue. }
    apply (proj2 (qcone_generated_qvec_ext d _ point
      (qvec_scale (/ q_of_nat denominator) (zvec_to_qvec value)) Hpoint)).
    apply qcone_generated_scale; [apply Qinv_le_0_compat|exact Hvalue_qcone].
      unfold q_of_nat, Qle. cbn. lia.
  - apply qcone_mapped_generators_in_period_cone.
    intros generator Hin. now apply Hgenerators.
Qed.

Definition Subsequence {A : Type} (sequence : nat -> A)
    (indices : nat -> nat) : nat -> A :=
  fun n => sequence (indices n).

Definition AnchoredSequence {d} (anchor : ZVec d)
    (sequence : nat -> ZVec d) : nat -> ZVec d :=
  fun n => zvec_sub (sequence n) anchor.

Lemma anchored_sequence_zero : forall d (sequence : nat -> ZVec d),
    AnchoredSequence (sequence 0%nat) sequence 0%nat = zvec_zero d.
Proof. intros. unfold AnchoredSequence. apply zvec_sub_self. Qed.

Lemma zvec_sub_common_anchor : forall d (anchor left right : ZVec d),
    zvec_sub (zvec_sub right anchor) (zvec_sub left anchor) =
      zvec_sub right left.
Proof.
  intros. apply zvec_ext. intro coordinate.
  unfold zvec_sub.
  repeat rewrite (nth_map2 _ _ _ coordinate coordinate coordinate
    eq_refl eq_refl). lia.
Qed.

Lemma anchored_periodic_le : forall d (period : ZSet d)
    anchor left right,
    PeriodicLe period left right ->
    PeriodicLe period (zvec_sub left anchor) (zvec_sub right anchor).
Proof.
  intros d period anchor left right Hle. unfold PeriodicLe in *.
  now rewrite zvec_sub_common_anchor.
Qed.

Theorem maximal_extract_first_normalization : forall d
    (period excluded remaining : ZSet d) (face : QSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FinitaryQCylindric period remaining ->
    MaximalNonemptyExtractFace period excluded remaining face ->
    forall sequence : nat -> ZVec d,
      (forall n,
        ExtractFace period face excluded remaining (sequence n)) ->
      exists first_indices,
        StrictlyIncreasing first_indices /\
        let sampled := Subsequence sequence first_indices in
        let anchor := sampled 0%nat in
        let normalized := AnchoredSequence anchor sampled in
        normalized 0%nat = zvec_zero d /\
        (forall n, period (normalized n)) /\
        (forall n,
          PeriodicLe period (normalized n) (normalized (S n))) /\
        (forall n,
          ExtractFace period face
            (ShiftedSet anchor excluded) (ShiftedSet anchor remaining)
            (normalized n)) /\
        MaximalNonemptyExtractFace period
          (ShiftedSet anchor excluded) (ShiftedSet anchor remaining) face.
Proof.
  intros d period excluded remaining face Hperiodic Hfinite Hremaining
    Hmaximal sequence Hsequence.
  assert (Hface : FaceOf (Cone period) face) by exact (proj1 Hmaximal).
  assert (Hface_periodic : Periodic (FacePeriod period face)).
  { now apply face_periodic. }
  assert (Hsequence_remaining : forall n, remaining (sequence n)).
  { intro n. exact (proj1 (extract_face_subset_difference d period excluded
      remaining face Hface_periodic (sequence n) (Hsequence n))). }
  destruct (finitary_qcylindric_monotone_subsequence d period remaining
    Hperiodic Hfinite Hremaining sequence Hsequence_remaining) as
    [first_indices [Hindices Hstep]].
  exists first_indices. split; [exact Hindices|].
  cbn zeta. split.
  - apply anchored_sequence_zero.
  - split.
    + intro n. unfold AnchoredSequence, Subsequence.
      exact (periodic_le_sequence d period Hperiodic
        (Subsequence sequence first_indices) Hstep 0%nat n ltac:(lia)).
    + split.
      * intro n. unfold AnchoredSequence.
        apply anchored_periodic_le. exact (Hstep n).
      * split.
        -- intro n. apply (proj2 (shifted_extract_face d period excluded
             remaining face (sequence (first_indices 0%nat))
             (zvec_sub (sequence (first_indices n))
               (sequence (first_indices 0%nat))))).
           rewrite zvec_add_sub_right. apply Hsequence.
        -- now apply shifted_maximal_nonempty_extract_face.
Qed.

Theorem maximal_extract_monotone_subsequence : forall d
    (period excluded remaining : ZSet d) (face : QSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    MaximalNonemptyExtractFace period excluded remaining face ->
    forall sequence : nat -> ZVec d,
      (forall n,
        ExtractFace period face excluded remaining (sequence n)) ->
      exists indices,
        StrictlyIncreasing indices /\
        forall n,
          PeriodicLe (FacePeriod period face)
            (sequence (indices n)) (sequence (indices (S n))).
Proof.
  intros d period excluded remaining face Hperiodic Hfinite Hfull
    Hexcluded Hremaining Hsubset Hmaximal sequence Hsequence.
  destruct (maximal_extract_first_normalization d period excluded remaining
    face Hperiodic Hfinite Hremaining Hmaximal sequence Hsequence) as
    [first_indices [Hfirst_indices Hnormalized]].
  set (sampled := Subsequence sequence first_indices).
  set (anchor := sampled 0%nat).
  set (normalized := AnchoredSequence anchor sampled).
  change (normalized 0%nat = zvec_zero d /\
      (forall n, period (normalized n)) /\
      (forall n, PeriodicLe period (normalized n) (normalized (S n))) /\
      (forall n,
        ExtractFace period face
          (ShiftedSet anchor excluded) (ShiftedSet anchor remaining)
          (normalized n)) /\
      MaximalNonemptyExtractFace period
        (ShiftedSet anchor excluded) (ShiftedSet anchor remaining) face)
    in Hnormalized.
  destruct Hnormalized as
    [Hnormalized_zero [Hnormalized_period
      [Hnormalized_step [Hnormalized_extract Hshifted_maximal]]]].
  assert (Hpolyhedral : RationalPolyhedralCone (Cone period)).
  { now apply finitely_generated_period_cone_polyhedral. }
  destruct (polyhedral_common_integer_face_normals d (Cone period)
    Hpolyhedral) as [normals [Hcone [Hsupports Hfaces]]].
  assert (Hsupport_list : List.Forall
      (fun normal => SupportingNormal (Cone period) (zvec_to_qvec normal))
      normals).
  { apply List.Forall_forall. exact Hsupports. }
  destruct (finite_supporting_normals_prepared_reindex d period normals
    normalized Hsupport_list Hnormalized_step) as
    [unbounded [start
      [Hunbounded [Hconstant [Hunbounded_tail Hinner_monotone]]]]].
  set (prepared := tail_reindex normalized start).
  assert (Hprepared_period : forall n, period (prepared n)).
  { intro n. unfold prepared, tail_reindex. apply Hnormalized_period. }
  assert (Hprepared_step : forall n,
      PeriodicLe period (prepared n) (prepared (S n))).
  { intro n. unfold prepared, tail_reindex.
    replace (start + S n)%nat with (S (start + n)) by lia.
    apply Hnormalized_step. }
  assert (Hprepared_extract : forall n,
      ExtractFace period face
        (ShiftedSet anchor excluded) (ShiftedSet anchor remaining)
        (prepared n)).
  { intro n. unfold prepared, tail_reindex. apply Hnormalized_extract. }
  assert (Hshifted_excluded_cylindric :
      QCylindric period (ShiftedSet anchor excluded)).
  { apply shifted_set_qcylindric,
      finitary_qcylindric_implies_cylindric; assumption. }
  assert (Hshifted_remaining_cylindric :
      QCylindric period (ShiftedSet anchor remaining)).
  { apply shifted_set_qcylindric,
      finitary_qcylindric_implies_cylindric; assumption. }
  assert (Hshifted_subset : forall value,
      ShiftedSet anchor excluded value ->
      ShiftedSet anchor remaining value).
  { now apply shifted_set_subset. }
  destruct (maximal_extract_prepared_chain_face_collapse d period
    (ShiftedSet anchor excluded) (ShiftedSet anchor remaining) face
    normals unbounded prepared Hperiodic Hfinite Hfull Hshifted_maximal
    Hcone Hshifted_excluded_cylindric Hshifted_remaining_cylindric
    Hshifted_subset (Hprepared_period 0%nat) Hprepared_extract Hprepared_step)
    as [active [tight [Hactive [Htight [Htight_normals Hcollapse]]]]].
  - intros normal Hin. split.
    + exact (proj1 (proj1 (Hunbounded normal) Hin)).
    + unfold prepared. now apply Hunbounded_tail.
  - intros normal Hnormal Hnot n.
    unfold prepared. now apply Hconstant.
  - set (larger := ThresholdFace (Cone period) tight).
    set (slice := RationalThresholdSlice period normals tight
      (prepared_threshold prepared)).
    change (FaceOf (Cone period) larger /\
      FaceSubset face larger /\
      FinitaryQCylindric (FacePeriod period larger) slice /\
      (forall n, slice (prepared n)) /\
      ExtractFace period larger (ShiftedSet anchor excluded)
        (ShiftedSet anchor remaining) (prepared 0%nat) /\
      SameSet face larger) in Hcollapse.
    destruct Hcollapse as [Hlarger_face [_
      [Hslice [Hprepared_slice [_ Hsame]]]]].
    assert (Hlarger_periodic : Periodic (FacePeriod period larger)).
    { now apply face_periodic. }
    assert (Hlarger_finite :
        FinitelyGeneratedPeriodic (FacePeriod period larger)).
    { now apply face_periodic_finitely_generated. }
    destruct (finitary_qcylindric_monotone_subsequence d
      (FacePeriod period larger) slice Hlarger_periodic Hlarger_finite
      Hslice prepared Hprepared_slice) as
      [second_indices [Hsecond_indices Hsecond_step]].
    set (combined := fun n => first_indices (start + second_indices n)%nat).
    exists combined. split.
    + unfold combined. apply strictly_increasing_compose;
        [exact Hfirst_indices|].
      intro n. specialize (Hsecond_indices n). lia.
    + intro n. specialize (Hsecond_step n).
      unfold prepared, tail_reindex, normalized, AnchoredSequence,
        sampled, Subsequence in Hsecond_step.
      unfold combined, PeriodicLe in Hsecond_step |- *.
      rewrite zvec_sub_common_anchor in Hsecond_step.
      destruct Hsecond_step as [Hperiod_difference Hlarger_difference].
      split; [exact Hperiod_difference|].
      now apply (proj2 (Hsame _)).
Qed.
