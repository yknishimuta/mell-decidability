From Coq Require Import Fin Lia List QArith Qring Vector.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone Corollary67Finitary
  FaceOrder Faces FaceStrippingExtract FaceStrippingLemma610
  FaceStrippingOrderFoundation FiniteFaces LatticeGordanInterface MathCompBridge
  Periodic QConeCore QIntegerHRep RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Q_scope.

Definition ConeLineality {d} (cone : QSet d) : QSet d :=
  fun value =>
    cone value /\
    cone (qvec_scale (-1) value).

Definition MinimalConeFace {d} (cone face : QSet d) : Prop :=
  FaceOf cone face /\
  forall other,
    FaceOf cone other ->
    FaceSubset face other.

Lemma qinner_nonnegative_opp_zero : forall d
    (normal value : QVec d),
    0 <= qinner normal value ->
    0 <= qinner normal (qvec_scale (-1) value) ->
    qinner normal value == 0.
Proof.
  intros d normal value Hpositive Hnegative.
  setoid_rewrite (qinner_scale_right d normal (-1) value) in Hnegative.
  assert (Hupper : qinner normal value <= 0).
  { pose proof (Qopp_le_compat _ _ Hnegative) as Hopp.
    setoid_replace (- (-1 * qinner normal value))
      with (qinner normal value) in Hopp by ring.
    setoid_replace (- 0) with 0 in Hopp by ring.
    exact Hopp. }
  now apply Qle_antisym.
Qed.

Lemma cone_lineality_hrep : forall d (cone : QSet d)
    (integer_normals : list (ZVec d)),
    (forall value : QVec d,
      cone value <->
      forall normal : ZVec d,
        List.In normal integer_normals ->
        0 <= qinner (zvec_to_qvec normal) value) ->
    SameSet (ConeLineality cone)
      (fun value =>
        cone value /\
        NormalOrthogonal
          (List.map (@zvec_to_qvec d) integer_normals) value).
Proof.
  intros d cone integer_normals Hcone value. split.
  - intros [Hvalue Hnegative]. split; [exact Hvalue|].
    intros normal Hin.
    apply in_map_iff in Hin as [integer_normal [<- Hin]].
    apply qinner_nonnegative_opp_zero.
    + apply (proj1 (Hcone value) Hvalue). exact Hin.
    + apply (proj1 (Hcone (qvec_scale (-1) value)) Hnegative).
      exact Hin.
  - intros [Hvalue Horthogonal]. split; [exact Hvalue|].
    apply (proj2 (Hcone (qvec_scale (-1) value))).
    intros integer_normal Hin.
    setoid_rewrite (qinner_scale_right d
      (zvec_to_qvec integer_normal) (-1) value).
    setoid_rewrite (Horthogonal (zvec_to_qvec integer_normal)).
    + unfold Qle. cbn. lia.
    + apply in_map. exact Hin.
Qed.

Lemma cone_lineality_face : forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    FaceOf cone (ConeLineality cone).
Proof.
  intros d cone Hpolyhedral.
  destruct (polyhedral_cone_integer_hrep d cone Hpolyhedral) as
    [integer_normals Hcone].
  exists (List.map (@zvec_to_qvec d) integer_normals). split.
  - apply List.Forall_forall. intros normal Hin.
    apply in_map_iff in Hin as [integer_normal [<- Hin]].
    intros point Hpoint. apply (proj1 (Hcone point) Hpoint).
    exact Hin.
  - apply cone_lineality_hrep. exact Hcone.
Qed.

Lemma cone_lineality_subset_face : forall d
    (cone face : QSet d),
    FaceOf cone face ->
    FaceSubset (ConeLineality cone) face.
Proof.
  intros d cone face [normals [Hsupport Hface]] value
    [Hvalue Hnegative].
  apply (proj2 (Hface value)). split; [exact Hvalue|].
  intros normal Hin.
  apply qinner_nonnegative_opp_zero.
  - apply (proj1 (List.Forall_forall _ _) Hsupport normal Hin).
    exact Hvalue.
  - apply (proj1 (List.Forall_forall _ _) Hsupport normal Hin).
    exact Hnegative.
Qed.

Theorem polyhedral_lineality_minimal_face :
  forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    MinimalConeFace cone (ConeLineality cone).
Proof.
  intros d cone Hpolyhedral. split.
  - now apply cone_lineality_face.
  - intros other Hother. now apply cone_lineality_subset_face.
Qed.

Lemma zvec_to_qvec_opp : forall d (value : ZVec d),
    QVecEq (zvec_to_qvec (zvec_opp value))
      (qvec_scale (-1) (zvec_to_qvec value)).
Proof.
  intros d value index. unfold zvec_to_qvec, zvec_opp, qvec_scale.
  rewrite (Vector.nth_map _ _ index index eq_refl), inject_Z_opp. ring.
Qed.

Lemma lineality_face_period_inverse : forall d
    (period : ZSet d) (value : ZVec d),
    Periodic period ->
    FullPeriodic period ->
    FacePeriod period (ConeLineality (Cone period)) value ->
    period (zvec_opp value).
Proof.
  intros d period value Hperiodic Hfull
    [Hvalue [Hvalue_cone Hnegative_cone]].
  apply (proj2 (full_periodic_member_iff_difference_cone d period
    Hperiodic Hfull (zvec_opp value))). split.
  - apply difference_opp.
    exact (proj1 (proj1 (full_periodic_member_iff_difference_cone d period
      Hperiodic Hfull value) Hvalue)).
  - apply (proj1 (cone_qvec_extensional d period
      (qvec_scale (-1) (zvec_to_qvec value))
      (zvec_to_qvec (zvec_opp value))
      (qvec_eq_sym _ _ _ (zvec_to_qvec_opp d value)))).
    exact Hnegative_cone.
Qed.

Lemma lineality_face_period_inverse_closed : forall d
    (period : ZSet d) (value : ZVec d),
    Periodic period ->
    FullPeriodic period ->
    FacePeriod period (ConeLineality (Cone period)) value ->
    FacePeriod period (ConeLineality (Cone period)) (zvec_opp value).
Proof.
  intros d period value Hperiodic Hfull
    [Hvalue [Hvalue_cone Hnegative_cone]]. split.
  - apply lineality_face_period_inverse; try assumption.
    now repeat split.
  - split.
    + apply (proj1 (cone_qvec_extensional d period
        (qvec_scale (-1) (zvec_to_qvec value))
        (zvec_to_qvec (zvec_opp value))
        (qvec_eq_sym _ _ _ (zvec_to_qvec_opp d value)))).
      exact Hnegative_cone.
    + apply (proj1 (cone_qvec_extensional d period
        (zvec_to_qvec value)
        (qvec_scale (-1) (zvec_to_qvec (zvec_opp value)))
        ltac:(intro index; unfold qvec_scale, zvec_to_qvec, zvec_opp;
          rewrite (Vector.nth_map _ _ index index eq_refl), inject_Z_opp;
          ring))).
      exact Hvalue_cone.
Qed.

Lemma zvec_add_opp_cancel_right : forall d
    (left right : ZVec d),
    zvec_add (zvec_add left right) (zvec_opp right) = left.
Proof.
  intros d left right. apply zvec_ext. intro index.
  unfold zvec_add, zvec_opp.
  repeat rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl).
  rewrite (Vector.nth_map _ _ index index eq_refl). lia.
Qed.

Theorem lemma_6_9_minimal_extract : forall d
    (period excluded remaining : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    QCylindric period excluded ->
    QCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    SameSet
      (ExtractFace period
        (ConeLineality (Cone period)) excluded remaining)
      (fun value => remaining value /\ ~ excluded value).
Proof.
  intros d period excluded remaining Hperiodic Hfinitely_generated Hfull
    Hexcluded Hremaining Hsubset.
  assert (Hpolyhedral : RationalPolyhedralCone (Cone period)).
  { now apply finitely_generated_period_cone_polyhedral. }
  assert (Hface : FaceOf (Cone period) (ConeLineality (Cone period))).
  { now apply cone_lineality_face. }
  assert (Hface_periodic :
      Periodic (FacePeriod period (ConeLineality (Cone period)))).
  { now apply face_periodic. }
  intro value. split.
  - now apply (extract_face_subset_difference d period excluded remaining
      (ConeLineality (Cone period)) Hface_periodic value).
  - intros [Hvalue_remaining Hvalue_excluded] increment Hincrement. split.
    + apply Hremaining; [exact Hvalue_remaining|exact (proj1 Hincrement)].
    + intro Hshifted_excluded. apply Hvalue_excluded.
      rewrite <- (zvec_add_opp_cancel_right d value increment).
      apply Hexcluded; [exact Hshifted_excluded|].
      now apply lineality_face_period_inverse.
Qed.

Lemma minimal_cone_face_same_set_lineality : forall d
    (cone face : QSet d),
    RationalPolyhedralCone cone ->
    MinimalConeFace cone face ->
    SameSet face (ConeLineality cone).
Proof.
  intros d cone face Hpolyhedral [Hface Hminimal].
  apply face_subset_antisym_same_set.
  - apply Hminimal. now apply cone_lineality_face.
  - now apply cone_lineality_subset_face.
Qed.

Theorem lemma_6_9_any_minimal_face : forall d
    (period excluded remaining : ZSet d) (face : QSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    QCylindric period excluded ->
    QCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    MinimalConeFace (Cone period) face ->
    SameSet
      (ExtractFace period face excluded remaining)
      (fun value => remaining value /\ ~ excluded value).
Proof.
  intros d period excluded remaining face Hperiodic Hfinitely_generated
    Hfull Hexcluded Hremaining Hsubset Hminimal.
  assert (Hpolyhedral : RationalPolyhedralCone (Cone period)).
  { now apply finitely_generated_period_cone_polyhedral. }
  eapply same_set_trans.
  - apply extract_face_same_set.
    exact (minimal_cone_face_same_set_lineality d (Cone period) face
      Hpolyhedral Hminimal).
  - exact (lemma_6_9_minimal_extract d period excluded remaining
      Hperiodic Hfinitely_generated Hfull Hexcluded Hremaining Hsubset).
Qed.
