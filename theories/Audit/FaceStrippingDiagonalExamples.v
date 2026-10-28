From Coq Require Import Fin Lia List Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Cone FaceStrippingDiagonal FaceStrippingExtract
  FaceStrippingFinitary FaceStrippingLemma611 FaceStrippingMinimalFace
  FaceStrippingRecursion Periodic RationalDefinability.
From Mell.Order Require Import PeriodicOrder.
From Mell.Audit Require Import FaceStrippingLemma611Examples
  FaceStrippingMinimalFaceExamples FaceStrippingRecursionExamples
  FaceStrippingTheoremExamples.

Import ListNotations.

Check @QDiagonal.
Check @NoBoundaryEdge.
Check @stripping_slice_face_cylindric.
Check @stripping_later_slice_in_earlier_remainder.
Check @lemma_6_3_stripping_diagonal.
Check @face_stripping_theorem_diagonal.

Definition d3e_empty_relation {d} : ZVec d -> ZVec d -> Prop :=
  fun _ _ => False.

Definition d3e_identity_relation {d} : ZVec d -> ZVec d -> Prop :=
  fun left right => left = right.

Definition d3e_shift_one_relation : ZVec 1 -> ZVec 1 -> Prop :=
  fun left right => right = zvec_add left (d0_z1 1).

Example d3e_empty_relation_diagonal : forall d (period : ZSet d),
    QDiagonal period (@d3e_empty_relation d).
Proof. intros d period left right increment Hfalse. contradiction. Qed.

Example d3e_identity_relation_diagonal : forall d (period : ZSet d),
    QDiagonal period (@d3e_identity_relation d).
Proof. intros d period left right increment -> _. reflexivity. Qed.

Example d3e_shift_one_relation_diagonal : forall period : ZSet 1,
    QDiagonal period d3e_shift_one_relation.
Proof.
  intros period left right increment Hrelation _.
  unfold d3e_shift_one_relation in *. subst right.
  rewrite !zvec_add_assoc. f_equal. apply zvec_add_comm.
Qed.

Example d3e_shift_one_relation_is_asymmetric :
    d3e_shift_one_relation (d0_z1 0) (d0_z1 1) /\
    ~ d3e_shift_one_relation (d0_z1 1) (d0_z1 0).
Proof.
  split.
  - unfold d3e_shift_one_relation, zvec_add, d0_z1. cbn. reflexivity.
  - unfold d3e_shift_one_relation. intro Heq.
    pose proof (f_equal (fun value => Vector.nth value Fin.F1) Heq) as Hhead.
    unfold zvec_add, d0_z1 in Hhead. cbn in Hhead. lia.
Qed.

Example d3e_identity_no_boundary : forall d
    (excluded remaining : ZSet d),
    NoBoundaryEdge excluded remaining (@d3e_identity_relation d).
Proof.
  intros d excluded remaining left right -> Hexcluded _ Hnot_excluded.
  contradiction.
Qed.

Example d3e_shift_one_nat_no_boundary :
    NoBoundaryEdge d0_nat_excluded d0_nat_period d3e_shift_one_relation.
Proof.
  intros left right Hrelation Hleft _ Hright_not_excluded.
  apply Hright_not_excluded.
  unfold d3e_shift_one_relation in Hrelation. subst right.
  unfold d0_nat_excluded in *. unfold zvec_add.
  rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1
    eq_refl eq_refl). unfold d0_z1. cbn. lia.
Qed.

Example d3e_nat_identity_face_stripping :
    exists faces : list (QSet 1),
      OrderedStrippingFaces d0_nat_period faces /\
      forall (earlier later : nat) left right,
        (earlier < later)%nat ->
        (later < length faces)%nat ->
        StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
          faces later left ->
        StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
          faces earlier right ->
        ~ d3e_identity_relation left right.
Proof.
  destruct (face_stripping_theorem_diagonal 1 d0_nat_period
    d0_nat_excluded d0_nat_period d3e_identity_relation
    d0_nat_periodic d0_nat_finitely_generated d0_nat_full
    d3_nat_excluded_finitary
    (period_finitary_self 1 d0_nat_period d0_nat_periodic)
    ltac:(intros value Hvalue; unfold d0_nat_excluded, d0_nat_period in *;
      lia)
    (d3e_identity_relation_diagonal 1 d0_nat_period)
    (d3e_identity_no_boundary 1 d0_nat_excluded d0_nat_period)) as
    [faces [Hstripping Hdiagonal]].
  exists faces. split; [exact (proj1 Hstripping)|exact Hdiagonal].
Qed.

Example d3e_nat_asymmetric_face_stripping :
    exists faces : list (QSet 1),
      OrderedStrippingFaces d0_nat_period faces /\
      forall (earlier later : nat) left right,
        (earlier < later)%nat ->
        (later < length faces)%nat ->
        StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
          faces later left ->
        StrippingSlice d0_nat_period d0_nat_excluded d0_nat_period
          faces earlier right ->
        ~ d3e_shift_one_relation left right.
Proof.
  destruct (face_stripping_theorem_diagonal 1 d0_nat_period
    d0_nat_excluded d0_nat_period d3e_shift_one_relation
    d0_nat_periodic d0_nat_finitely_generated d0_nat_full
    d3_nat_excluded_finitary
    (period_finitary_self 1 d0_nat_period d0_nat_periodic)
    ltac:(intros value Hvalue; unfold d0_nat_excluded, d0_nat_period in *;
      lia)
    (d3e_shift_one_relation_diagonal d0_nat_period)
    d3e_shift_one_nat_no_boundary) as [faces [Hstripping Hdiagonal]].
  exists faces. split; [exact (proj1 Hstripping)|exact Hdiagonal].
Qed.

(* A valid two-slice example distinguishing the converse direction. *)
Definition d3e_two_nat_excluded : ZSet 1 :=
  fun value =>
    (2 <= Vector.nth value Fin.F1)%Z /\
    Z.Even (Vector.nth value Fin.F1).

Definition d3e_two_nat_faces : list (QSet 1) :=
  [Cone d0_two_nat_period;
   ConeLineality (Cone d0_two_nat_period)].

Definition d3e_earlier_to_later_relation : ZVec 1 -> ZVec 1 -> Prop :=
  fun left right =>
    exists increment,
      d0_two_nat_period increment /\
      left = zvec_add (d0_z1 1) increment /\
      right = increment.

Lemma d3e_two_nat_remaining_cylindric :
    QCylindric d0_two_nat_period d0_nat_period.
Proof.
  intros base increment Hbase [Hincrement _].
  unfold d0_nat_period, zvec_add in *.
  rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1
    eq_refl eq_refl). lia.
Qed.

Lemma d3e_two_nat_excluded_cylindric :
    QCylindric d0_two_nat_period d3e_two_nat_excluded.
Proof.
  intros base increment [Hbase [base_half Hbase_even]]
    [Hincrement [increment_half Hincrement_even]].
  unfold d3e_two_nat_excluded, zvec_add in *.
  rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1
    eq_refl eq_refl). split; [lia|].
  exists (base_half + increment_half)%Z. lia.
Qed.

Example d3e_two_nat_earlier_slice_member :
    StrippingSlice d0_two_nat_period d3e_two_nat_excluded d0_nat_period
      d3e_two_nat_faces 0 (d0_z1 1).
Proof.
  intros increment [Hincrement _]. split.
  - apply d3e_two_nat_remaining_cylindric.
    + unfold d0_nat_period, d0_z1. cbn. lia.
    + exact Hincrement.
  - intros [_ [sum_half Hsum]].
    destruct Hincrement as [_ [half Hhalf]].
    assert (Hcoordinate :
        Vector.nth (zvec_add (d0_z1 1) increment) Fin.F1 =
        (1 + Vector.nth increment Fin.F1)%Z).
    { unfold zvec_add, d0_z1.
      rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1
        eq_refl eq_refl). reflexivity. }
    rewrite Hcoordinate in Hsum. lia.
Qed.

Example d3e_two_nat_later_slice_member :
    StrippingSlice d0_two_nat_period d3e_two_nat_excluded d0_nat_period
      d3e_two_nat_faces 1 (d0_z1 0).
Proof.
  intros increment Hincrement.
  apply (proj1 (two_nat_face_period_is_zero increment)) in Hincrement.
  assert (Hzero : increment = zvec_zero 1).
  { apply zvec_ext. intro index.
    refine (Fin.caseS' index (fun index => _) _ _).
    - unfold zvec_zero. rewrite Vector.const_nth. exact Hincrement.
    - intro impossible. inversion impossible. }
  subst increment. rewrite zvec_add_zero_right. split.
  - apply (proj2 (stripping_remainder_succ 1 d0_two_nat_period
      d3e_two_nat_excluded d0_nat_period d3e_two_nat_faces 0
      ltac:(cbn; lia) (d0_z1 0))). split.
    + unfold d0_nat_period, d0_z1. cbn. lia.
    + intro Hslice.
      specialize (Hslice (d0_z1 2)).
      assert (Htwo : FacePeriod d0_two_nat_period
          (Cone d0_two_nat_period) (d0_z1 2)).
      { apply (proj2 ((face_period_self 1 d0_two_nat_period
          d0_two_nat_periodic) (d0_z1 2))).
        unfold d0_two_nat_period, d0_z1. cbn. split; [lia|].
        exists 1%Z. lia. }
      specialize (Hslice Htwo). destruct Hslice as [_ Hnot_excluded].
      apply Hnot_excluded.
      unfold d3e_two_nat_excluded, d0_z1. cbn. split; [lia|].
      exists 1%Z. lia.
  - unfold d3e_two_nat_excluded, d0_z1. cbn. lia.
Qed.

Example d3e_earlier_to_later_relation_diagonal :
    QDiagonal d0_two_nat_period d3e_earlier_to_later_relation.
Proof.
  intros left right delta
    [increment [Hincrement [Hleft Hright]]] Hdelta.
  subst left right. exists (zvec_add increment delta). split.
  - exact (proj2 d0_two_nat_periodic increment delta Hincrement Hdelta).
  - split; [now rewrite zvec_add_assoc|reflexivity].
Qed.

Example d3e_earlier_to_later_no_boundary :
    NoBoundaryEdge d3e_two_nat_excluded d0_nat_period
      d3e_earlier_to_later_relation.
Proof.
  intros left right [increment [Hincrement [Hleft Hright]]]
    Hleft_excluded _ _. subst left right.
  destruct Hincrement as [_ [increment_half Hincrement_even]].
  destruct Hleft_excluded as [_ [left_half Hleft_even]].
  assert (Hcoordinate :
      Vector.nth (zvec_add (d0_z1 1) increment) Fin.F1 =
      (1 + Vector.nth increment Fin.F1)%Z).
  { unfold zvec_add, d0_z1.
    rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1
      eq_refl eq_refl). reflexivity. }
  rewrite Hcoordinate in Hleft_even. lia.
Qed.

Example d3e_allowed_earlier_to_later_edge :
    StrippingSlice d0_two_nat_period d3e_two_nat_excluded d0_nat_period
      d3e_two_nat_faces 0 (d0_z1 1) /\
    StrippingSlice d0_two_nat_period d3e_two_nat_excluded d0_nat_period
      d3e_two_nat_faces 1 (d0_z1 0) /\
    d3e_earlier_to_later_relation (d0_z1 1) (d0_z1 0).
Proof.
  split; [exact d3e_two_nat_earlier_slice_member|]. split.
  - exact d3e_two_nat_later_slice_member.
  - exists (zvec_zero 1). split.
    + exact (proj1 d0_two_nat_periodic).
    + now rewrite zvec_add_zero_right.
Qed.

Check d2_dimension_zero_ordered_faces.
Check d0_two_nat_periodic.
Check d0_nat_square_periodic.
Check d0_integer_periodic.
Check d0_nat_times_integer_periodic.
Check d1_nat_times_integer_minimal_face_nonzero.
Check d1_empty_initial_stays_empty.
Check d1_equal_excluded_slice_empty.
Check d1_two_nat_slice_zero_is_translate.
Check d1_two_nat_remainder_one_empty.
Check d1_multiple_nonempty_slice_zero.
Check d1_multiple_nonempty_slice_one.

Print Assumptions stripping_slice_face_cylindric.
Print Assumptions stripping_later_slice_in_earlier_remainder.
Print Assumptions lemma_6_3_stripping_diagonal_core.
Print Assumptions lemma_6_3_stripping_diagonal.
Print Assumptions face_stripping_theorem_diagonal.
