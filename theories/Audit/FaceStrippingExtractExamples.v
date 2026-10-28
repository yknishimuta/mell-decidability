From Coq Require Import Fin Lia List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Cone Faces FaceStrippingExtract
  MathCompBridge Periodic QConeCore RationalDefinability RationalHToV.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Q_scope.

Set Printing Implicit.

Check @QCylindric.
Check @FinitaryQCylindric.
Check @FacePeriod.
Check @face_periodic.
Check @face_periodic_finitely_generated.
Check @ExtractFace.
Check @extract_face_subset_difference.
Check @extract_face_cylindric.
Check @face_period_self.
Check @extract_empty_excluded_face_period.
Check @extract_equal_excluded_empty.
Check @extract_face_not_period_cylindric_if_proper.
Check @excluded_subset_extract_remainder.
Check @extract_remainder_cylindric.

Print Assumptions face_periodic.
Print Assumptions face_linear_combination_filter.
Print Assumptions face_periodic_finitely_generated.
Print Assumptions extract_face_subset_difference.
Print Assumptions extract_face_cylindric.
Print Assumptions excluded_subset_extract_remainder.
Print Assumptions extract_remainder_cylindric.

Lemma generated_period_finitely_generated : forall d
    (generators : list (ZVec d)),
    FinitelyGeneratedPeriodic (zvec_generated generators).
Proof.
  intros d generators. exists generators. split.
  - intros generator Hin. now apply generated_generator.
  - intro value. reflexivity.
Qed.

Example face_period_dimension_zero :
    FinitelyGeneratedPeriodic
      (FacePeriod (@zvec_generated 0 [])
        (Cone (@zvec_generated 0 []))).
Proof.
  apply face_periodic_finitely_generated.
  - apply generated_period_finitely_generated.
  - apply face_self.
Qed.

Example zero_period_maximal_face : forall d,
    FinitelyGeneratedPeriodic
      (FacePeriod (@zvec_generated d [])
        (Cone (@zvec_generated d []))).
Proof.
  intro d. apply face_periodic_finitely_generated.
  - apply generated_period_finitely_generated.
  - apply face_self.
Qed.

Definition extract_z1 (value : Z) : ZVec 1 := Vector.of_list [value].
Definition extract_z2 (left right : Z) : ZVec 2 :=
  Vector.of_list [left; right].

Definition extract_nat_period : ZSet 1 :=
  zvec_generated [extract_z1 1].

Definition extract_quadrant_period : ZSet 2 :=
  zvec_generated [extract_z2 1 0; extract_z2 0 1].

Definition extract_lineality_period : ZSet 1 :=
  zvec_generated [extract_z1 1; extract_z1 (-1)].

Definition extract_q1 (value : Q) : QVec 1 :=
  fun index => Fin.caseS' index (fun _ => Q) value
    (fun impossible => Fin.case0 (fun _ => Q) impossible).

Definition extract_nat_zero_face : QSet 1 :=
  fun point =>
    Cone extract_nat_period point /\
    NormalOrthogonal [extract_q1 1] point.

Lemma extract_nat_period_nonnegative : forall value,
    extract_nat_period value -> (0 <= Vector.nth value Fin.F1)%Z.
Proof.
  intros value [coefficients Hvalue].
  remember (Vector.to_list coefficients) as coefficient_list eqn:Hlist.
  assert (Hlength : length coefficient_list = 1%nat).
  { rewrite Hlist, length_to_list. reflexivity. }
  destruct coefficient_list as [|coefficient coefficient_list];
    [discriminate|].
  destruct coefficient_list as [|extra coefficient_list];
    [|discriminate].
  rewrite <- Hvalue. cbn [zvec_linear_combination]. unfold zvec_add.
  rewrite (nth_map2 Z.add _ _ Fin.F1 Fin.F1 Fin.F1 eq_refl eq_refl),
    nth_zvec_nsmul.
  unfold extract_z1. cbn. lia.
Qed.

Lemma extract_nat_supporting_normal :
    SupportingNormal (Cone extract_nat_period) (extract_q1 1).
Proof.
  intros point [generated [Hgenerated Hpoint]].
  setoid_rewrite (qinner_qvec_ext_right 1 (extract_q1 1)
    point generated Hpoint).
  clear point Hpoint. induction Hgenerated.
  - setoid_rewrite qinner_zero_right. apply Qle_refl.
  - setoid_rewrite qinner_add_right.
    setoid_rewrite qinner_scale_right.
    setoid_replace 0 with (0 + 0) by ring.
    apply Qplus_le_compat; [|exact IHHgenerated].
    apply Qmult_le_0_compat; [exact H|].
    setoid_replace
      (qinner (extract_q1 1) (zvec_to_qvec value))
      with (inject_Z (Vector.nth value Fin.F1)).
    + unfold Qle, inject_Z. cbn.
      pose proof (extract_nat_period_nonnegative value H0). lia.
    + unfold qinner, extract_q1, zvec_to_qvec, qrow_apply,
        qvec_to_vector. cbn. ring.
Qed.

Lemma extract_nat_zero_face_is_face :
    FaceOf (Cone extract_nat_period) extract_nat_zero_face.
Proof.
  exists [extract_q1 1]. split.
  - constructor; [apply extract_nat_supporting_normal|constructor].
  - intro point. reflexivity.
Qed.

Lemma extract_one_not_in_nat_zero_face :
    ~ extract_nat_zero_face (zvec_to_qvec (extract_z1 1)).
Proof.
  intros [_ Horthogonal].
  specialize (Horthogonal (extract_q1 1)).
  assert (Hin : List.In (extract_q1 1) [extract_q1 1]) by now left.
  specialize (Horthogonal Hin).
  unfold qinner, extract_q1, extract_z1, zvec_to_qvec,
    qrow_apply, qvec_to_vector in Horthogonal. cbn in Horthogonal.
  discriminate Horthogonal.
Qed.

Example nat_period_maximal_face_finitely_generated :
    FinitelyGeneratedPeriodic
      (FacePeriod extract_nat_period (Cone extract_nat_period)).
Proof.
  apply face_periodic_finitely_generated.
  - apply generated_period_finitely_generated.
  - apply face_self.
Qed.

Example quadrant_period_maximal_face_finitely_generated :
    FinitelyGeneratedPeriodic
      (FacePeriod extract_quadrant_period (Cone extract_quadrant_period)).
Proof.
  apply face_periodic_finitely_generated.
  - apply generated_period_finitely_generated.
  - apply face_self.
Qed.

Example nonpointed_lineality_maximal_face_finitely_generated :
    FinitelyGeneratedPeriodic
      (FacePeriod extract_lineality_period (Cone extract_lineality_period)).
Proof.
  apply face_periodic_finitely_generated.
  - apply generated_period_finitely_generated.
  - apply face_self.
Qed.

Example nonzero_period_zero_face_finitely_generated :
    FinitelyGeneratedPeriodic
      (FacePeriod extract_nat_period extract_nat_zero_face).
Proof.
  apply face_periodic_finitely_generated.
  - apply generated_period_finitely_generated.
  - apply extract_nat_zero_face_is_face.
Qed.

Example proper_face_extract_is_not_full_period_cylindric :
    ~ QCylindric extract_nat_period
      (ExtractFace extract_nat_period extract_nat_zero_face
        (fun _ => False)
        (FacePeriod extract_nat_period extract_nat_zero_face)).
Proof.
  apply extract_face_not_period_cylindric_if_proper.
  - apply generated_periodic.
  - apply extract_nat_zero_face_is_face.
  - exists (extract_z1 1). split.
    + apply generated_generator. now left.
    + apply extract_one_not_in_nat_zero_face.
Qed.

Example maximal_face_period_is_original :
    SameSet
      (FacePeriod extract_quadrant_period (Cone extract_quadrant_period))
      extract_quadrant_period.
Proof.
  apply face_period_self, generated_periodic.
Qed.

Example empty_excluded_extract_is_face_period :
    SameSet
      (ExtractFace extract_quadrant_period (Cone extract_quadrant_period)
        (fun _ => False)
        (FacePeriod extract_quadrant_period (Cone extract_quadrant_period)))
      (FacePeriod extract_quadrant_period (Cone extract_quadrant_period)).
Proof.
  apply extract_empty_excluded_face_period.
  apply face_periodic; [apply generated_periodic|apply face_self].
Qed.

Example excluded_equal_remaining_has_empty_extract :
    forall value,
      ~ ExtractFace extract_nat_period (Cone extract_nat_period)
          extract_nat_period extract_nat_period value.
Proof.
  apply extract_equal_excluded_empty.
  apply face_periodic; [apply generated_periodic|apply face_self].
Qed.

Example empty_excluded_remainder_is_cylindric :
    QCylindric extract_nat_period
      (fun value =>
        extract_nat_period value /\
        ~ ExtractFace extract_nat_period (Cone extract_nat_period)
            (fun _ => False) extract_nat_period value).
Proof.
  apply extract_remainder_cylindric.
  - apply generated_periodic.
  - apply face_self.
  - intros base increment Hfalse. contradiction.
  - intros base increment Hbase Hincrement.
    now apply (proj2 (generated_periodic 1 [extract_z1 1]) base increment).
  - intros value Hfalse. contradiction.
Qed.
