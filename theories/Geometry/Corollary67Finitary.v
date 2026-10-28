From Coq Require Import Lia List QArith Qround Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization CommonIntegerFaceNormals Cone
  FaceStrippingBases FaceStrippingExtract Faces FiniteFaces MathCompBridge
  Periodic QConeCore RationalDefinability RationalHToV.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Definition ThresholdFace {d} (cone : QSet d)
    (tight : list (ZVec d)) : QSet d :=
  fun point =>
    cone point /\
    forall normal, List.In normal tight ->
      qinner (zvec_to_qvec normal) point == 0.

Definition RationalThresholdSlice {d} (period : ZSet d)
    (normals tight : list (ZVec d))
    (threshold : ZVec d -> Q) : ZSet d :=
  fun value =>
    period value /\
    (forall normal, List.In normal normals ->
      threshold normal <=
        qinner (zvec_to_qvec normal) (zvec_to_qvec value)) /\
    (forall normal, List.In normal tight ->
      qinner (zvec_to_qvec normal) (zvec_to_qvec value) ==
        threshold normal).

Definition rational_threshold_constraints {d}
    (normals tight : list (ZVec d))
    (threshold : ZVec d -> Q) : list (ZVec d * Z) :=
  List.map (fun normal => (normal, 0%Z)) normals ++
  List.map (fun normal => (normal, Qceiling (threshold normal))) normals ++
  List.map (fun normal =>
    (zvec_opp normal, Qceiling (- threshold normal))) tight.

Lemma qinner_zvec_to_qvec : forall d (normal value : ZVec d),
    qinner (zvec_to_qvec normal) (zvec_to_qvec value) ==
      inject_Z (zinner normal value).
Proof.
  intros d normal. induction normal as [|head d tail IH]; intro value.
  - refine (Vector.case0 (fun value => _) _ value). reflexivity.
  - refine (Vector.caseS' value (fun value => _) _).
    intros value_head value_tail. cbn [qinner qrow_apply qvec_to_vector
      zvec_to_qvec qdot zinner].
    rewrite inject_Z_plus, inject_Z_mult. apply Qplus_comp; [reflexivity|].
    exact (IH value_tail).
Qed.

Lemma zinner_opp_left : forall d (normal value : ZVec d),
    zinner (zvec_opp normal) value = (- zinner normal value)%Z.
Proof.
  intros d normal. induction normal as [|head d tail IH]; intro value.
  - refine (Vector.case0 (fun value => _) _ value). reflexivity.
  - refine (Vector.caseS' value (fun value => _) _).
    intros value_head value_tail. cbn [zvec_opp zinner Vector.map].
    rewrite IH. ring.
Qed.

Lemma integer_ge_rational_iff_ceiling : forall (n : Z) (r : Q),
    r <= inject_Z n <-> (Qceiling r <= n)%Z.
Proof.
  intros n r. split.
  - intro H. pose proof (Qceiling_resp_le r (inject_Z n) H) as Hceil.
    now rewrite Qceiling_Z in Hceil.
  - intro H. eapply Qle_trans; [apply Qle_ceiling|].
    rewrite <- Zle_Qle. exact H.
Qed.

Lemma integer_eq_rational_iff_two_ceilings : forall (n : Z) (r : Q),
    inject_Z n == r <->
      (Qceiling r <= n)%Z /\ (Qceiling (- r) <= - n)%Z.
Proof.
  intros n r. split.
  - intro Heq. split.
    + apply (proj1 (integer_ge_rational_iff_ceiling n r)).
      apply (proj2 (Qle_lteq _ _)). right. now symmetry.
    + apply (proj1 (integer_ge_rational_iff_ceiling (- n) (- r))).
      rewrite inject_Z_opp. apply (proj2 (Qle_lteq _ _)). right.
      symmetry. now apply Qopp_comp.
  - intros [Hlower Hupper]. apply Qle_antisym.
    + apply (proj2 (integer_ge_rational_iff_ceiling (- n) (- r))) in Hupper.
      rewrite inject_Z_opp in Hupper.
      pose proof (Qopp_le_compat _ _ Hupper) as Hreverse.
      now rewrite !Qopp_involutive in Hreverse.
    + now apply (proj2 (integer_ge_rational_iff_ceiling n r)).
Qed.

Lemma affine_rational_threshold_constraints_iff : forall d
    (normals tight : list (ZVec d)) threshold value,
    AffineSolutions (rational_threshold_constraints normals tight threshold)
      value <->
    (forall normal, List.In normal normals ->
      (0 <= zinner normal value)%Z) /\
    (forall normal, List.In normal normals ->
      (Qceiling (threshold normal) <= zinner normal value)%Z) /\
    (forall normal, List.In normal tight ->
      (Qceiling (- threshold normal) <= - zinner normal value)%Z).
Proof.
  intros d normals tight threshold value. split.
  - intro H. repeat split; intros normal Hin.
    + apply (H (normal, 0%Z)). unfold rational_threshold_constraints.
      apply in_or_app. left. apply in_map_iff.
      exists normal. now split.
    + apply (H (normal, Qceiling (threshold normal))).
      unfold rational_threshold_constraints. apply in_or_app. right.
      apply in_or_app. left. apply in_map_iff.
      exists normal. now split.
    + specialize (H (zvec_opp normal, Qceiling (- threshold normal))).
      unfold rational_threshold_constraints in H. specialize (H ltac:(
        apply in_or_app; right; apply in_or_app; right; apply in_map_iff;
        exists normal; now split)).
      cbn in H. now rewrite zinner_opp_left in H.
  - intros [Hzero [Hlower Hupper]] constraint Hin.
    unfold rational_threshold_constraints in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + apply in_map_iff in Hin as [normal [Heq Hin]]. subst constraint.
      cbn. now apply Hzero.
    + apply in_app_or in Hin as [Hin | Hin].
      * apply in_map_iff in Hin as [normal [Heq Hin]]. subst constraint.
        cbn. now apply Hlower.
      * apply in_map_iff in Hin as [normal [Heq Hin]]. subst constraint.
        cbn. rewrite zinner_opp_left. now apply Hupper.
Qed.

Lemma homogeneous_rational_threshold_constraints_iff : forall d
    (normals tight : list (ZVec d)) threshold value,
    HomogeneousSolutions
      (rational_threshold_constraints normals tight threshold) value <->
    (forall normal, List.In normal normals ->
      (0 <= zinner normal value)%Z) /\
    (forall normal, List.In normal tight ->
      (0 <= - zinner normal value)%Z).
Proof.
  intros d normals tight threshold value. split.
  - intro H. split; intros normal Hin.
    + apply (H (normal, 0%Z)). unfold rational_threshold_constraints.
      apply in_or_app. left. apply in_map_iff.
      exists normal. now split.
    + specialize (H (zvec_opp normal, Qceiling (- threshold normal))).
      unfold rational_threshold_constraints in H. specialize (H ltac:(
        apply in_or_app; right; apply in_or_app; right; apply in_map_iff;
        exists normal; now split)).
      cbn in H. now rewrite zinner_opp_left in H.
  - intros [Hpositive Hnegative] constraint Hin.
    unfold rational_threshold_constraints in Hin.
    apply in_app_or in Hin as [Hin | Hin].
    + apply in_map_iff in Hin as [normal [Heq Hin]]. subst constraint.
      cbn. now apply Hpositive.
    + apply in_app_or in Hin as [Hin | Hin].
      * apply in_map_iff in Hin as [normal [Heq Hin]]. subst constraint.
        cbn. now apply Hpositive.
      * apply in_map_iff in Hin as [normal [Heq Hin]]. subst constraint.
        cbn. rewrite zinner_opp_left. now apply Hnegative.
Qed.

Lemma integer_qinner_nonnegative_iff : forall d
    (normal value : ZVec d),
    0 <= qinner (zvec_to_qvec normal) (zvec_to_qvec value) <->
      (0 <= zinner normal value)%Z.
Proof.
  intros d normal value.
  pose proof (qinner_zvec_to_qvec d normal value) as Hinner.
  split; intro H.
  - rewrite Zle_Qle.
    now setoid_rewrite <- Hinner.
  - rewrite Zle_Qle in H.
    now setoid_rewrite Hinner.
Qed.

Lemma integer_qinner_ge_rational_iff_ceiling : forall d
    (normal value : ZVec d) threshold,
    threshold <= qinner (zvec_to_qvec normal) (zvec_to_qvec value) <->
      (Qceiling threshold <= zinner normal value)%Z.
Proof.
  intros d normal value threshold.
  pose proof (qinner_zvec_to_qvec d normal value) as Hinner.
  split; intro H.
  - apply (proj1 (integer_ge_rational_iff_ceiling
      (zinner normal value) threshold)).
    now setoid_rewrite <- Hinner.
  - apply (proj2 (integer_ge_rational_iff_ceiling
      (zinner normal value) threshold)) in H.
    now setoid_rewrite Hinner.
Qed.

Lemma integer_qinner_eq_rational_iff_two_ceilings : forall d
    (normal value : ZVec d) threshold,
    qinner (zvec_to_qvec normal) (zvec_to_qvec value) == threshold <->
      (Qceiling threshold <= zinner normal value)%Z /\
      (Qceiling (- threshold) <= - zinner normal value)%Z.
Proof.
  intros d normal value threshold.
  pose proof (qinner_zvec_to_qvec d normal value) as Hinner.
  rewrite <- (integer_eq_rational_iff_two_ceilings
    (zinner normal value) threshold).
  split; intro H.
  - transitivity (qinner (zvec_to_qvec normal) (zvec_to_qvec value));
      [symmetry; exact Hinner|exact H].
  - transitivity (inject_Z (zinner normal value)); [exact Hinner|exact H].
Qed.

Lemma full_periodic_member_iff_difference_cone : forall d
    (period : ZSet d),
    Periodic period -> FullPeriodic period -> forall value,
      period value <->
      Difference period value /\ Cone period (zvec_to_qvec value).
Proof.
  intros d period Hperiodic Hfull value.
  exact (proj1 (full_periodic_iff_linearization_fixed d period Hperiodic)
    Hfull value).
Qed.

Lemma rational_slice_affine_group_iff : forall d
    (period : ZSet d) (normals tight : list (ZVec d)) threshold,
    Periodic period -> FullPeriodic period ->
    (forall point : QVec d,
      Cone period point <->
      forall normal, List.In normal normals ->
        0 <= qinner (zvec_to_qvec normal) point) ->
    (forall normal, List.In normal tight -> List.In normal normals) ->
    SameSet
      (RationalThresholdSlice period normals tight threshold)
      (AffineGroupSolutions (Difference period)
        (rational_threshold_constraints normals tight threshold)).
Proof.
  intros d period normals tight threshold Hperiodic Hfull Hcone Htight value.
  pose proof (full_periodic_member_iff_difference_cone d period
    Hperiodic Hfull value) as Hfull_value.
  split.
  - intros [Hperiod [Hlower Hequal]]. split.
    + exact (proj1 (proj1 Hfull_value Hperiod)).
    + apply (proj2 (affine_rational_threshold_constraints_iff
        d normals tight threshold value)). repeat split.
      * intros normal Hin. apply (proj1 (integer_qinner_nonnegative_iff
          d normal value)).
        exact (proj1 (Hcone (zvec_to_qvec value))
          (proj2 (proj1 Hfull_value Hperiod)) normal Hin).
      * intros normal Hin. apply (proj1
          (integer_qinner_ge_rational_iff_ceiling
            d normal value (threshold normal))). now apply Hlower.
      * intros normal Hin. pose proof (Hequal normal Hin) as Heq.
        apply (proj1 (integer_qinner_eq_rational_iff_two_ceilings
          d normal value (threshold normal))) in Heq. tauto.
  - intros [Hdifference Hconstraints].
    apply (proj1 (affine_rational_threshold_constraints_iff
      d normals tight threshold value)) in Hconstraints.
    destruct Hconstraints as [Hzero [Hlower Hupper]].
    assert (Hvalue_cone : Cone period (zvec_to_qvec value)).
    { apply (proj2 (Hcone (zvec_to_qvec value))). intros normal Hin.
      now apply (proj2 (integer_qinner_nonnegative_iff d normal value)),
        Hzero. }
    split.
    + apply (proj2 Hfull_value). now split.
    + split.
      * intros normal Hin. apply (proj2
          (integer_qinner_ge_rational_iff_ceiling
            d normal value (threshold normal))). now apply Hlower.
      * intros normal Hin. apply (proj2
          (integer_qinner_eq_rational_iff_two_ceilings
            d normal value (threshold normal))). split.
        -- apply Hlower. now apply Htight.
        -- now apply Hupper.
Qed.

Lemma threshold_face_is_face : forall d (period : ZSet d)
    (normals tight : list (ZVec d)),
    (forall point : QVec d,
      Cone period point <->
      forall normal, List.In normal normals ->
        0 <= qinner (zvec_to_qvec normal) point) ->
    (forall normal, List.In normal tight -> List.In normal normals) ->
    FaceOf (Cone period) (ThresholdFace (Cone period) tight).
Proof.
  intros d period normals tight Hcone Htight.
  exists (List.map zvec_to_qvec tight). split.
  - apply List.Forall_forall. intros rational_normal Hin.
    apply in_map_iff in Hin as [normal [Heq Hin]]. subst rational_normal.
    intros point Hpoint. exact (proj1 (Hcone point) Hpoint normal (Htight _ Hin)).
  - intro point. split.
    + intros [Hpoint Hz]. split; [exact Hpoint|].
      intros rational_normal Hin.
      apply in_map_iff in Hin as [normal [Heq Hin]]. subst rational_normal.
      now apply Hz.
    + intros [Hpoint Hz]. split; [exact Hpoint|].
      intros normal Hin. apply Hz. apply in_map. exact Hin.
Qed.

Lemma homogeneous_group_face_period_iff : forall d
    (period : ZSet d) (normals tight : list (ZVec d)) threshold,
    Periodic period -> FullPeriodic period ->
    (forall point : QVec d,
      Cone period point <->
      forall normal, List.In normal normals ->
        0 <= qinner (zvec_to_qvec normal) point) ->
    (forall normal, List.In normal tight -> List.In normal normals) ->
    SameSet
      (HomogeneousGroupSolutions (Difference period)
        (rational_threshold_constraints normals tight threshold))
      (FacePeriod period (ThresholdFace (Cone period) tight)).
Proof.
  intros d period normals tight threshold Hperiodic Hfull Hcone Htight value.
  pose proof (full_periodic_member_iff_difference_cone d period
    Hperiodic Hfull value) as Hfull_value.
  split.
  - intros [Hdifference Hconstraints].
    apply (proj1 (homogeneous_rational_threshold_constraints_iff
      d normals tight threshold value)) in Hconstraints.
    destruct Hconstraints as [Hpositive Hnegative].
    assert (Hvalue_cone : Cone period (zvec_to_qvec value)).
    { apply (proj2 (Hcone (zvec_to_qvec value))). intros normal Hin.
      now apply (proj2 (integer_qinner_nonnegative_iff d normal value)),
        Hpositive. }
    split.
    + apply (proj2 Hfull_value). now split.
    + split; [exact Hvalue_cone|]. intros normal Hin.
      assert (Hzero : zinner normal value = 0%Z) by
        (specialize (Hpositive normal (Htight normal Hin));
         specialize (Hnegative normal Hin); lia).
      transitivity (inject_Z (zinner normal value)).
      * apply qinner_zvec_to_qvec.
      * now rewrite Hzero.
  - intros [Hperiod [Hvalue_cone Hzero]]. split.
    + exact (proj1 (proj1 Hfull_value Hperiod)).
    + apply (proj2 (homogeneous_rational_threshold_constraints_iff
        d normals tight threshold value)). split.
      * intros normal Hin. apply (proj1 (integer_qinner_nonnegative_iff
          d normal value)). exact (proj1 (Hcone _) Hvalue_cone normal Hin).
      * intros normal Hin.
        assert (Hzero_q : inject_Z (zinner normal value) == 0).
        { transitivity
            (qinner (zvec_to_qvec normal) (zvec_to_qvec value)).
          - symmetry. apply qinner_zvec_to_qvec.
          - now apply Hzero. }
        apply (proj1 (inject_Z_injective (zinner normal value) 0%Z))
          in Hzero_q. lia.
Qed.

Lemma threshold_face_periodic : forall d (period : ZSet d)
    (normals tight : list (ZVec d)),
    Periodic period ->
    (forall point : QVec d,
      Cone period point <->
      forall normal, List.In normal normals ->
        0 <= qinner (zvec_to_qvec normal) point) ->
    (forall normal, List.In normal tight -> List.In normal normals) ->
    Periodic (FacePeriod period (ThresholdFace (Cone period) tight)).
Proof.
  intros. apply face_periodic; [assumption|].
  now apply threshold_face_is_face with (normals := normals).
Qed.

Lemma threshold_face_periodic_finitely_generated : forall d
    (period : ZSet d) (normals tight : list (ZVec d)),
    FinitelyGeneratedPeriodic period ->
    (forall point : QVec d,
      Cone period point <->
      forall normal, List.In normal normals ->
        0 <= qinner (zvec_to_qvec normal) point) ->
    (forall normal, List.In normal tight -> List.In normal normals) ->
    FinitelyGeneratedPeriodic
      (FacePeriod period (ThresholdFace (Cone period) tight)).
Proof.
  intros. apply face_periodic_finitely_generated; [assumption|].
  now apply threshold_face_is_face with (normals := normals).
Qed.

Lemma finitary_qcylindric_congr : forall d (period period' set set' : ZSet d),
    SameSet period period' -> SameSet set set' ->
    FinitaryQCylindric period set ->
    FinitaryQCylindric period' set'.
Proof.
  intros d period period' set set' Hperiod Hset [bases Hbases].
  exists bases. intro value. split.
  - intro Hvalue.
    pose proof (proj2 (Hset value) Hvalue) as Hvalue_set.
    apply (proj1 (Hbases value)) in Hvalue_set.
    destruct Hvalue_set as [base [increment [Hin [Hincrement Heq]]]].
    exists base, increment. repeat split; try assumption.
    now apply (proj1 (Hperiod increment)).
  - intros [base [increment [Hin [Hincrement Heq]]]].
    apply (proj1 (Hset value)), (proj2 (Hbases value)).
    exists base, increment. repeat split; try assumption.
    now apply (proj2 (Hperiod increment)).
Qed.

Theorem corollary_6_7_finitary : forall d
    (period : ZSet d) (normals tight : list (ZVec d))
    (threshold : ZVec d -> Q),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    (forall point : QVec d,
      Cone period point <->
      forall normal, List.In normal normals ->
        0 <= qinner (zvec_to_qvec normal) point) ->
    (forall normal, List.In normal tight -> List.In normal normals) ->
    FinitaryQCylindric
      (FacePeriod period (ThresholdFace (Cone period) tight))
      (RationalThresholdSlice period normals tight threshold).
Proof.
  intros d period normals tight threshold Hperiodic Hgenerated Hfull
    Hcone Htight.
  pose proof (difference_group_finitely_generated d period Hperiodic)
    as Hdifference_generated.
  pose proof (affine_group_inequalities_finitary d (Difference period)
    (rational_threshold_constraints normals tight threshold)
    Hdifference_generated) as Hfinitary.
  eapply finitary_qcylindric_congr; [| |exact Hfinitary].
  - exact (homogeneous_group_face_period_iff d period normals tight threshold
      Hperiodic Hfull Hcone Htight).
  - apply same_set_sym. exact (rational_slice_affine_group_iff d period
      normals tight threshold Hperiodic Hfull Hcone Htight).
Qed.
