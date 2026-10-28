From Coq Require Import Lia List Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Cone Faces FaceStrippingExtract
  FaceStrippingRecursion FaceStrippingMinimalFace MathCompBridge Periodic
  QConeCore RationalDefinability.
From Mell.Order Require Import PeriodicOrder.
From Mell.Audit Require Import FaceStrippingMinimalFaceExamples.

Import ListNotations.

Check @StrippingRemainder.
Check @StrippingSlice.
Check @stripping_remainder_zero.
Check @stripping_slice_spec.
Check @stripping_remainder_succ.
Check @stripping_slice_out_of_range.
Check @stripping_remainder_subset_initial.
Check @stripping_slice_subset_remainder.
Check @stripping_slice_avoids_excluded.
Check @stripping_excluded_subset_remainder.
Check @ProcessedBefore.
Check @stripping_remainder_characterization.
Check @stripping_initial_partition.
Check @stripping_remainder_processed_disjoint.
Check @stripping_slices_disjoint.
Check @StageCandidateFace.
Check @face_stripping_ordered_recursion.

Check nat_face_period_is_zero.
Check two_nat_face_period_is_zero.
Check integer_face_period_is_full.
Check nat_square_face_period_is_zero.
Check nat_times_integer_face_period_is_second_axis.

Example d1_single_max_face_empty_excluded : forall d
    (period : ZSet d),
    Periodic.Periodic period ->
    SameSet
      (StrippingSlice period (fun _ => False) period [Cone period] 0)
      period.
Proof.
  intros d period Hperiodic value. split.
  - intro Hslice. cbn [StrippingSlice] in Hslice.
    pose proof (Hslice (zvec_zero d)
      (proj2 ((face_period_self d period Hperiodic) (zvec_zero d))
        (proj1 Hperiodic))) as Hzero.
    now rewrite zvec_add_zero_right in Hzero.
  - intros Hvalue increment [Hincrement _]. split.
    + now apply (proj2 Hperiodic value increment).
    + tauto.
Qed.

Example d1_empty_initial_stays_empty : forall d
    (period excluded : ZSet d) faces stage value,
    ~ StrippingRemainder period excluded (fun _ => False) faces stage value.
Proof.
  intros d period excluded faces stage value Hvalue.
  exact (stripping_remainder_subset_initial d period excluded
    (fun _ => False) faces stage value Hvalue).
Qed.

Example d1_equal_excluded_slice_empty : forall d
    (period remaining : ZSet d) faces,
    Periodic.Periodic period ->
    (forall face, List.In face faces -> Faces.FaceOf (Cone period) face) ->
    forall stage : nat,
      (stage < length faces)%nat ->
      forall value,
        ~ StrippingSlice period remaining remaining faces stage value.
Proof.
  intros d period remaining faces Hperiodic Hfaces stage Hstage value Hslice.
  pose proof (stripping_slice_subset_remainder d period remaining remaining
    faces Hperiodic Hfaces stage Hstage value Hslice) as Hremainder.
  pose proof (stripping_remainder_subset_initial d period remaining remaining
    faces stage value Hremainder) as Hremaining.
  exact (stripping_slice_avoids_excluded d period remaining remaining faces
    Hperiodic Hfaces stage Hstage value Hslice Hremaining).
Qed.

Example d1_dimension_zero_single_face :
    SameSet
      (StrippingSlice (fun _ : ZVec 0 => True) (fun _ => False)
        (fun _ => True) [Cone (fun _ : ZVec 0 => True)] 0)
      (fun _ => True).
Proof.
  apply d1_single_max_face_empty_excluded. split; firstorder.
Qed.

Example d1_zero_period_single_face :
    SameSet
      (StrippingSlice (fun value : ZVec 1 => value = zvec_zero 1)
        (fun _ => False) (fun value => value = zvec_zero 1)
        [Cone (fun value : ZVec 1 => value = zvec_zero 1)] 0)
      (fun value => value = zvec_zero 1).
Proof.
  apply d1_single_max_face_empty_excluded. split.
  - reflexivity.
  - intros left right -> ->. apply zvec_add_zero_left.
Qed.

Example d1_nat_single_face :=
  d1_single_max_face_empty_excluded 1 d0_nat_period d0_nat_periodic.

Example d1_two_nat_single_face :=
  d1_single_max_face_empty_excluded 1 d0_two_nat_period d0_two_nat_periodic.

Example d1_nat_square_single_face :=
  d1_single_max_face_empty_excluded 2 d0_nat_square_period
    d0_nat_square_periodic.

Example d1_integer_single_face :=
  d1_single_max_face_empty_excluded 1 d0_integer_period d0_integer_periodic.

Example d1_nat_times_integer_single_face :=
  d1_single_max_face_empty_excluded 2 d0_nat_times_integer_period
    d0_nat_times_integer_periodic.

Definition d1_nat_faces : list (QSet 1) :=
  [Cone d0_nat_period; ConeLineality (Cone d0_nat_period)].

Example d1_nat_slice_zero_empty : forall value,
    ~ StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
        d1_nat_faces 0 value.
Proof.
  intros value Hslice.
  assert (Hzero_period : d0_nat_period (zvec_zero 1)) by
    exact (proj1 d0_nat_periodic).
  assert (Hzero_face : FacePeriod d0_nat_period (Cone d0_nat_period)
      (zvec_zero 1)).
  { apply (proj2 ((face_period_self 1 d0_nat_period d0_nat_periodic)
      (zvec_zero 1))).
    exact Hzero_period. }
  cbn [StrippingSlice d1_nat_faces] in Hslice.
  pose proof (Hslice (zvec_zero 1) Hzero_face) as Hzero_result.
  rewrite zvec_add_zero_right in Hzero_result.
  destruct Hzero_result as [Hvalue _].
  assert (Htwo_period : d0_nat_period (d0_z1 2)).
  { unfold d0_nat_period, d0_z1. cbn. lia. }
  assert (Htwo_face : FacePeriod d0_nat_period (Cone d0_nat_period)
      (d0_z1 2)).
  { apply (proj2 ((face_period_self 1 d0_nat_period d0_nat_periodic)
      (d0_z1 2))).
    exact Htwo_period. }
  pose proof (Hslice (d0_z1 2) Htwo_face) as Htwo_result.
  apply (proj2 Htwo_result). unfold d0_nat_excluded, d0_nat_period in *.
  unfold zvec_add, d0_z1.
  rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1 eq_refl eq_refl).
  cbn. change (0 + 2 <= Vector.nth value Fin.F1 + 2)%Z.
  exact (proj1 (Z.add_le_mono_r 0 (Vector.nth value Fin.F1) 2) Hvalue).
Qed.

Example d1_nat_remainder_zero :
    SameSet
      (StrippingRemainder d0_nat_period d0_nat_excluded d0_nat_period
        d1_nat_faces 0)
      d0_nat_period.
Proof. apply stripping_remainder_zero. Qed.

Example d1_nat_remainder_one :
    SameSet
      (StrippingRemainder d0_nat_period d0_nat_excluded d0_nat_period
        d1_nat_faces 1)
      d0_nat_period.
Proof.
  intro value. cbn [StrippingRemainder d1_nat_faces]. split.
  - intros [Hvalue _]. exact Hvalue.
  -
  intro Hvalue. split; [exact Hvalue|].
  change (~ StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
    d1_nat_faces 0 value). apply d1_nat_slice_zero_empty.
Qed.

Example d1_nat_slice_one : forall value,
    StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
      d1_nat_faces 1 value <->
    Vector.nth value Fin.F1 = 0%Z \/
    Vector.nth value Fin.F1 = 1%Z.
Proof.
  intro value. transitivity
    (ExtractFace d0_nat_period (ConeLineality (Cone d0_nat_period))
      d0_nat_excluded d0_nat_period value).
  - cbn [StrippingSlice d1_nat_faces]. split.
    + intros Hextract increment Hinc.
      destruct (Hextract increment Hinc) as [Hrem Hnot]. split.
      * now apply (proj1 (d1_nat_remainder_one
          (zvec_add value increment))).
      * exact Hnot.
    + intros Hextract increment Hinc.
      destruct (Hextract increment Hinc) as [Hrem Hnot]. split.
      * now apply (proj2 (d1_nat_remainder_one
          (zvec_add value increment))).
      * exact Hnot.
  - apply nat_tail_extract_is_zero_or_one.
Qed.

Example d1_nat_remainder_two :
    SameSet
      (StrippingRemainder d0_nat_period d0_nat_excluded d0_nat_period
        d1_nat_faces 2)
      d0_nat_excluded.
Proof.
  intro value. split.
  - intro Hvalue.
    apply (proj1 (stripping_remainder_succ 1 d0_nat_period
      d0_nat_excluded d0_nat_period d1_nat_faces 1 ltac:(cbn; lia)
      value)) in Hvalue.
    destruct Hvalue as [Hremaining Hnot_slice].
    apply (proj1 (d1_nat_remainder_one value)) in Hremaining.
    assert (Hnot01 : ~ (Vector.nth value Fin.F1 = 0%Z \/
        Vector.nth value Fin.F1 = 1%Z)).
    { intro Hcases. apply Hnot_slice.
      now apply (proj2 (d1_nat_slice_one value)). }
    unfold d0_nat_period in Hremaining.
    unfold d0_nat_excluded. lia.
  - intro Hexcluded.
    apply (proj2 (stripping_remainder_succ 1 d0_nat_period
      d0_nat_excluded d0_nat_period d1_nat_faces 1 ltac:(cbn; lia)
      value)). split.
    + apply (proj2 (d1_nat_remainder_one value)).
      unfold d0_nat_period, d0_nat_excluded in *. lia.
    + intro Hslice. apply (proj1 (d1_nat_slice_one value)) in Hslice.
      unfold d0_nat_excluded in Hexcluded. lia.
Qed.

Example d1_nat_slice_out_of_range : forall value,
    ~ StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
        d1_nat_faces 2 value.
Proof.
  intro value.
  assert (Hbound : (length d1_nat_faces <= 2)%nat).
  { unfold d1_nat_faces. reflexivity. }
  exact (stripping_slice_out_of_range 1 d0_nat_period d0_nat_excluded
    d0_nat_period d1_nat_faces 2 Hbound value).
Qed.

Definition d1_nat_with_gap : ZSet 1 :=
  fun value => d0_nat_period value \/ value = d0_z1 (-2).

Example d1_multiple_nonempty_slice_zero :
    StrippingSlice d0_nat_period (fun _ => False) d1_nat_with_gap
      d1_nat_faces 0 (zvec_zero 1).
Proof.
  intros increment [Hincrement _]. split; [left|tauto].
  rewrite zvec_add_zero_left. exact Hincrement.
Qed.

Example d1_multiple_nonempty_slice_one :
    StrippingSlice d0_nat_period (fun _ => False) d1_nat_with_gap
      d1_nat_faces 1 (d0_z1 (-2)).
Proof.
  intros increment Hincrement.
  apply (proj1 (nat_face_period_is_zero increment)) in Hincrement.
  assert (Hzero : increment = zvec_zero 1).
  { apply zvec_ext. intro index.
    refine (Fin.caseS' index (fun index => _) _ _).
    - unfold zvec_zero. rewrite Vector.const_nth. exact Hincrement.
    - intro impossible. inversion impossible. }
  subst increment. rewrite zvec_add_zero_right. split; [|tauto].
  apply (proj2 (stripping_remainder_succ 1 d0_nat_period
    (fun _ => False) d1_nat_with_gap d1_nat_faces 0 ltac:(cbn; lia)
    (d0_z1 (-2)))). split.
  - now right.
  - intro Hslice.
    specialize (Hslice (d0_z1 1)).
    assert (Hone : FacePeriod d0_nat_period (Cone d0_nat_period)
        (d0_z1 1)).
    { apply (proj2 ((face_period_self 1 d0_nat_period d0_nat_periodic)
        (d0_z1 1))). unfold d0_nat_period, d0_z1. cbn. lia. }
    specialize (Hslice Hone). destruct Hslice as [Hremaining _].
    unfold d1_nat_with_gap, d0_nat_period, zvec_add, d0_z1 in Hremaining.
    cbn in Hremaining.
    destruct Hremaining as [Hnonnegative|Heq]; [lia|].
    pose proof (f_equal (fun value => Vector.nth value Fin.F1) Heq) as Hhead.
    cbn in Hhead. lia.
Qed.

Definition d1_two_nat_translate : ZSet 1 :=
  fun value => exists increment,
    d0_two_nat_period increment /\
    value = zvec_add (d0_z1 1) increment.

Definition d1_two_nat_faces : list (QSet 1) := [Cone d0_two_nat_period].

Example d1_two_nat_slice_zero_is_translate :
    SameSet
      (StrippingSlice d0_two_nat_period (fun _ => False)
        d1_two_nat_translate d1_two_nat_faces 0)
      d1_two_nat_translate.
Proof.
  intro value. split.
  - intro Hslice.
    cbn [StrippingSlice d1_two_nat_faces] in Hslice.
    specialize (Hslice (zvec_zero 1)
      (proj2 ((face_period_self 1 d0_two_nat_period d0_two_nat_periodic)
        (zvec_zero 1))
        (proj1 d0_two_nat_periodic))).
    now rewrite zvec_add_zero_right in Hslice.
  - intros [base [Hbase ->]] increment [Hincrement _]. split.
    + exists (zvec_add base increment). split.
      * exact (proj2 d0_two_nat_periodic base increment Hbase Hincrement).
      * now rewrite zvec_add_assoc.
    + tauto.
Qed.

Example d1_two_nat_remainder_one_empty :
    SameSet
      (StrippingRemainder d0_two_nat_period (fun _ => False)
        d1_two_nat_translate d1_two_nat_faces 1)
      (fun _ => False).
Proof.
  intro value. split; [|tauto].
  intro Hvalue. apply (proj1 (stripping_remainder_succ 1
    d0_two_nat_period (fun _ => False) d1_two_nat_translate
    d1_two_nat_faces 0 ltac:(cbn; lia) value)) in Hvalue.
  destruct Hvalue as [Htranslate Hnot].
  apply Hnot, (proj2 (d1_two_nat_slice_zero_is_translate value)), Htranslate.
Qed.

Example d1_nat_times_integer_minimal_face_nonzero :
    FacePeriod d0_nat_times_integer_period
      (ConeLineality (Cone d0_nat_times_integer_period)) (d0_z2 0 1).
Proof.
  apply (proj2 (nat_times_integer_face_period_is_second_axis (d0_z2 0 1))).
  reflexivity.
Qed.

Print Assumptions stripping_remainder_zero.
Print Assumptions stripping_slice_spec.
Print Assumptions stripping_remainder_succ.
Print Assumptions stripping_excluded_subset_remainder.
Print Assumptions stripping_remainder_characterization.
Print Assumptions stripping_initial_partition.
Print Assumptions stripping_slices_disjoint.
Print Assumptions face_stripping_ordered_recursion.
