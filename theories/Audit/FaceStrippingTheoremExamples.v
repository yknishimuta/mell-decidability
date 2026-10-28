From Coq Require Import Fin Lia List Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import FaceStrippingExtract FaceStrippingFinitary
  FaceStrippingLemma611 FaceStrippingRecursion FaceStrippingTheorem
  MathCompBridge Periodic QConeCore RationalDefinability.
From Mell.Order Require Import PeriodicOrder.
From Mell.Audit Require Import FaceStrippingLemma611Examples
  FaceStrippingMinimalFaceExamples FaceStrippingRecursionExamples.

Import ListNotations.

Check @BackwardPeriodCover.
Check @stripping_final_remainder_eq_excluded.
Check @stripping_complete_partition.
Check @stripping_partition_slices_disjoint.
Check @stripping_finitary_stage_package.
Check @stripping_first_slice_empty.
Check @face_stripping_theorem.

Lemma d3_nat_excluded_finitary :
    FinitaryQCylindric d0_nat_period d0_nat_excluded.
Proof.
  exists [d0_z1 2]. intro value. split.
  - intro Hvalue.
    exists (d0_z1 2), (zvec_sub value (d0_z1 2)). repeat split.
    + now left.
    + unfold d0_nat_period, d0_nat_excluded, zvec_sub in *.
      rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1
        eq_refl eq_refl). unfold d0_z1. cbn. lia.
    + symmetry. apply zvec_sub_add_cancel.
  - intros [base [increment [[Hbase|Hfalse] [Hincrement ->]]]].
    + subst base. apply d0_nat_excluded_cylindric.
      * unfold d0_nat_excluded, d0_z1. cbn. lia.
      * exact Hincrement.
    + contradiction.
Qed.

Lemma d3_nat_backward_period_cover :
    BackwardPeriodCover d0_nat_period d0_nat_excluded d0_nat_period.
Proof.
  intros value Hvalue. exists (d0_z1 2). split.
  - unfold d0_nat_period, d0_z1. cbn. lia.
  - unfold d0_nat_excluded, d0_nat_period, zvec_add in *.
    rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1
      eq_refl eq_refl). unfold d0_z1. cbn. lia.
Qed.

Example d3_nat_face_stripping_application :
    exists faces : list (QSet 1),
      OrderedStrippingFaces d0_nat_period faces /\
      SameSet
        (StrippingRemainder d0_nat_period d0_nat_excluded d0_nat_period
          faces (length faces))
        d0_nat_excluded /\
      (forall value,
        (d0_nat_period value /\ ~ d0_nat_excluded value) <->
        exists stage : nat,
          (stage < length faces)%nat /\
          StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
            faces stage value) /\
      (forall value,
        ~ StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
            faces 0 value).
Proof.
  destruct (face_stripping_theorem 1 d0_nat_period d0_nat_excluded
    d0_nat_period d0_nat_periodic d0_nat_finitely_generated d0_nat_full
    d3_nat_excluded_finitary
    (period_finitary_self 1 d0_nat_period d0_nat_periodic)
    ltac:(intros value Hvalue; unfold d0_nat_excluded, d0_nat_period in *;
      lia)) as
    [faces [Hordered [_ [_ [Hfinal [_ [_ [_ [Hpartition Hfirst]]]]]]]]].
  exists faces. split; [exact Hordered|].
  split; [exact Hfinal|].
  split; [exact Hpartition|].
  now apply Hfirst, d3_nat_backward_period_cover.
Qed.

Example d3_nat_concrete_trace :
    (forall value,
      ~ StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
          d1_nat_faces 0 value) /\
    (forall value,
      StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
        d1_nat_faces 1 value <->
      Vector.nth value Fin.F1 = 0%Z \/
      Vector.nth value Fin.F1 = 1%Z) /\
    SameSet
      (StrippingRemainder d0_nat_period d0_nat_excluded d0_nat_period
        d1_nat_faces 2)
      d0_nat_excluded.
Proof.
  split.
  - apply d1_nat_slice_zero_empty.
  - split.
    + apply d1_nat_slice_one.
    + apply d1_nat_remainder_two.
Qed.

Example d3_two_nat_translated_trace :
    SameSet
      (StrippingSlice d0_two_nat_period (fun _ => False)
        d1_two_nat_translate d1_two_nat_faces 0)
      d1_two_nat_translate /\
    SameSet
      (StrippingRemainder d0_two_nat_period (fun _ => False)
        d1_two_nat_translate d1_two_nat_faces 1)
      (fun _ => False).
Proof. split; [apply d1_two_nat_slice_zero_is_translate|
  apply d1_two_nat_remainder_one_empty]. Qed.

Check d2_dimension_zero_ordered_faces.
Check d1_empty_initial_stays_empty.
Check d1_equal_excluded_slice_empty.
Check d1_nat_times_integer_minimal_face_nonzero.
Check d0_nat_square_periodic.
Check d0_integer_periodic.

Print Assumptions stripping_final_remainder_eq_excluded.
Print Assumptions stripping_complete_partition.
Print Assumptions stripping_partition_slices_disjoint.
Print Assumptions stripping_finitary_stage_package.
Print Assumptions stripping_first_slice_empty.
Print Assumptions face_stripping_theorem.
