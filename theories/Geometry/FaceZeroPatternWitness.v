From Coq Require Import Classical_Prop Fin Lia List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import CenterAbsorption ClosedLinearization
  CommonIntegerFaceNormals Cone FaceStrippingExtract Faces MathCompBridge
  LatticeGordanInterface Periodic QConeCore
  RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Q_scope.

Lemma inactive_supporting_normal_positive_on_face : forall d
    (cone face : QSet d) (normal : ZVec d),
    FaceOf cone face ->
    SupportingNormal cone (zvec_to_qvec normal) ->
    ~ IntegerNormalOrthogonalToFace face normal ->
    exists point : QVec d,
      face point /\ 0 < qinner (zvec_to_qvec normal) point.
Proof.
  intros d cone face normal Hface Hsupport Hnot_orthogonal.
  assert (Hexists : exists point : QVec d,
      face point /\ ~ qinner (zvec_to_qvec normal) point == 0).
  { destruct (classic (exists point : QVec d,
        face point /\ ~ qinner (zvec_to_qvec normal) point == 0))
      as [Hexists | Hnone]; [exact Hexists|].
    exfalso. apply Hnot_orthogonal. intros point Hpoint.
    destruct (classic (qinner (zvec_to_qvec normal) point == 0))
      as [Hzero | Hnonzero]; [exact Hzero|].
    exfalso. apply Hnone. now exists point. }
  destruct Hexists as [point [Hpoint Hnonzero]].
  exists point. split; [exact Hpoint|].
  assert (Hnonnegative : 0 <= qinner (zvec_to_qvec normal) point).
  { apply Hsupport. now apply (face_subset d cone face Hface). }
  destruct (Qle_lt_or_eq _ _ Hnonnegative) as [Hpositive | Hzero].
  - exact Hpositive.
  - exfalso. apply Hnonzero. now symmetry.
Qed.

Lemma inactive_normals_positive_sum : forall d (cone face : QSet d)
    (normals inactive : list (ZVec d)),
    IsCone cone ->
    FaceOf cone face ->
    List.Forall
      (fun normal => SupportingNormal cone (zvec_to_qvec normal))
      normals ->
    (forall normal,
      List.In normal inactive ->
      List.In normal normals /\
      ~ IntegerNormalOrthogonalToFace face normal) ->
    exists sum : QVec d,
      face sum /\
      forall normal,
        List.In normal inactive ->
        0 < qinner (zvec_to_qvec normal) sum.
Proof.
  intros d cone face normals inactive Hcone Hface Hsupport Hinactive.
  pose proof (face_is_cone d cone face Hcone Hface) as Hface_cone.
  induction inactive as [|head tail IH].
  - exists (qvec_zero d). split.
    + exact (cone_contains_zero face Hface_cone).
    + intros normal Hin. inversion Hin.
  - assert (Hhead_data :
        List.In head normals /\
        ~ IntegerNormalOrthogonalToFace face head).
    { apply Hinactive. now left. }
    assert (Hhead_support :
        SupportingNormal cone (zvec_to_qvec head)).
    { exact (proj1 (List.Forall_forall _ _) Hsupport head
        (proj1 Hhead_data)). }
    destruct (inactive_supporting_normal_positive_on_face
      d cone face head Hface Hhead_support (proj2 Hhead_data)) as
      [head_point [Hhead_point Hhead_positive]].
    assert (Htail_data : forall normal,
        List.In normal tail ->
        List.In normal normals /\
        ~ IntegerNormalOrthogonalToFace face normal).
    { intros normal Hin. apply Hinactive. now right. }
    destruct (IH Htail_data) as [tail_sum [Htail_face Htail_positive]].
    exists (qvec_add head_point tail_sum). split.
    + now apply (cone_closed_add face Hface_cone).
    + intros normal [Heq | Hin].
      * subst normal. setoid_rewrite qinner_add_right.
        setoid_replace 0 with (0 + 0) by ring.
        apply Qplus_lt_le_compat; [exact Hhead_positive|].
        apply Hhead_support.
        now apply (face_subset d cone face Hface).
      * setoid_rewrite qinner_add_right.
        setoid_replace
          (qinner (zvec_to_qvec normal) head_point +
           qinner (zvec_to_qvec normal) tail_sum)
          with
          (qinner (zvec_to_qvec normal) tail_sum +
           qinner (zvec_to_qvec normal) head_point) by ring.
        setoid_replace 0 with (0 + 0) by ring.
        apply Qplus_lt_le_compat.
        -- now apply Htail_positive.
        -- assert (Hnormal_data := Htail_data normal Hin).
           assert (Hnormal_support :
               SupportingNormal cone (zvec_to_qvec normal)).
           { exact (proj1 (List.Forall_forall _ _) Hsupport normal
               (proj1 Hnormal_data)). }
           apply Hnormal_support.
           now apply (face_subset d cone face Hface).
Qed.

Lemma face_normals_zero_pattern_sum : forall d (cone face : QSet d)
    (normals : list (ZVec d)),
    IsCone cone ->
    FaceOf cone face ->
    List.Forall
      (fun normal => SupportingNormal cone (zvec_to_qvec normal))
      normals ->
    exists sum : QVec d,
      face sum /\
      forall normal,
        List.In normal normals ->
        (IntegerNormalOrthogonalToFace face normal <->
         qinner (zvec_to_qvec normal) sum == 0).
Proof.
  intros d cone face normals Hcone Hface Hsupport.
  destruct (face_inactive_integer_normals d normals face) as
    [inactive Hinactive].
  assert (Hinactive_data : forall normal,
      List.In normal inactive ->
      List.In normal normals /\
      ~ IntegerNormalOrthogonalToFace face normal).
  { intros normal Hin. now apply Hinactive. }
  destruct (inactive_normals_positive_sum d cone face normals inactive
    Hcone Hface Hsupport Hinactive_data) as
    [sum [Hsum_face Hsum_positive]].
  exists sum. split; [exact Hsum_face|].
  intros normal Hnormal. split.
  - intro Horthogonal. now apply Horthogonal.
  - intro Hzero.
    destruct (classic (IntegerNormalOrthogonalToFace face normal)) as
      [Horthogonal | Hnot_orthogonal]; [exact Horthogonal|].
    exfalso.
    assert (Hin : List.In normal inactive).
    { apply Hinactive. now split. }
    pose proof (Hsum_positive normal Hin) as Hpositive.
    apply (Qlt_not_eq _ _ Hpositive). now symmetry.
Qed.

Lemma face_positive_ray_reflect : forall d (period : ZSet d)
    (face : QSet d) (value : ZVec d) coefficient,
    FaceOf (Cone period) face ->
    period value ->
    face (qvec_scale coefficient (zvec_to_qvec value)) ->
    0 < coefficient ->
    face (zvec_to_qvec value).
Proof.
  intros d period face value coefficient
    [normals [Hsupport Hface]] Hvalue Hscaled Hpositive.
  apply (proj2 (Hface (zvec_to_qvec value))). split.
  - now apply cone_contains_source.
  - intros normal Hnormal.
    assert (Hscaled_zero :
        qinner normal
          (qvec_scale coefficient (zvec_to_qvec value)) == 0).
    { exact (proj2 (proj1 (Hface _) Hscaled) normal Hnormal). }
    assert (Hproduct :
        coefficient * qinner normal (zvec_to_qvec value) == 0).
    { transitivity
        (qinner normal
          (qvec_scale coefficient (zvec_to_qvec value))).
      - symmetry. apply qinner_scale_right.
      - exact Hscaled_zero. }
    destruct (Qmult_integral _ _ Hproduct) as
      [Hcoefficient_zero | Hinner_zero].
    + exfalso. apply (Qlt_not_eq _ _ Hpositive). now symmetry.
    + exact Hinner_zero.
Qed.

Lemma qinner_positive_ray_zero_iff : forall d (normal point : QVec d)
    (value : ZVec d) coefficient,
    QVecEq point
      (qvec_scale coefficient (zvec_to_qvec value)) ->
    0 < coefficient ->
    (qinner normal point == 0 <->
     qinner normal (zvec_to_qvec value) == 0).
Proof.
  intros d normal point value coefficient Hpoint Hpositive.
  assert (Hinner : qinner normal point ==
      coefficient * qinner normal (zvec_to_qvec value)).
  { transitivity
      (qinner normal
        (qvec_scale coefficient (zvec_to_qvec value))).
    - now apply qinner_qvec_ext_right.
    - apply qinner_scale_right. }
  split; intro Hzero.
  - assert (Hproduct :
        coefficient * qinner normal (zvec_to_qvec value) == 0).
    { transitivity (qinner normal point); [symmetry; exact Hinner|exact Hzero]. }
    destruct (Qmult_integral _ _ Hproduct) as
      [Hcoefficient_zero | Hinner_zero].
    + exfalso. apply (Qlt_not_eq _ _ Hpositive). now symmetry.
    + exact Hinner_zero.
  - transitivity
      (coefficient * qinner normal (zvec_to_qvec value)).
    + exact Hinner.
    + setoid_rewrite Hzero. ring.
Qed.

Theorem face_zero_pattern_witness :
    forall (d : nat) (period : ZSet d) (face : QSet d)
      (normals : list (ZVec d)),
    Periodic period ->
    FaceOf (Cone period) face ->
    List.Forall
      (fun normal =>
        SupportingNormal (Cone period) (zvec_to_qvec normal))
      normals ->
    exists witness : ZVec d,
      FacePeriod period face witness /\
      forall normal : ZVec d,
        List.In normal normals ->
        (IntegerNormalOrthogonalToFace face normal <->
         qinner (zvec_to_qvec normal)
           (zvec_to_qvec witness) == 0).
Proof.
  intros d period face normals Hperiodic Hface Hsupport.
  destruct (face_normals_zero_pattern_sum d (Cone period) face normals
    (cone_is_cone d period) Hface Hsupport) as
    [point [Hpoint_face Hpoint_pattern]].
  assert (Hpoint_cone : Cone period point).
  { now apply (face_subset d (Cone period) face Hface). }
  destruct (periodic_cone_positive_ray d period point Hperiodic Hpoint_cone)
    as [witness [coefficient
      [Hwitness [Hcoefficient Hpoint_scale]]]].
  assert (Hscaled_face :
      face (qvec_scale coefficient (zvec_to_qvec witness))).
  { apply (proj1 (face_qvec_ext d (Cone period) face Hface
      (fun left right Heq => cone_qvec_extensional d period left right Heq)
      point (qvec_scale coefficient (zvec_to_qvec witness))
      Hpoint_scale)).
    exact Hpoint_face. }
  assert (Hwitness_face : face (zvec_to_qvec witness)).
  { now apply (face_positive_ray_reflect d period face witness coefficient). }
  exists witness. split.
  - now split.
  - intros normal Hnormal.
    transitivity (qinner (zvec_to_qvec normal) point == 0).
    + exact (Hpoint_pattern normal Hnormal).
    + now apply qinner_positive_ray_zero_iff with
        (coefficient := coefficient).
Qed.

Theorem periodic_polyhedral_common_zero_pattern_normals :
    forall (d : nat) (period : ZSet d),
    Periodic period ->
    RationalPolyhedralCone (Cone period) ->
    exists normals : list (ZVec d),
      (forall point : QVec d,
        Cone period point <->
        forall normal,
          List.In normal normals ->
          0 <= qinner (zvec_to_qvec normal) point) /\
      (forall normal,
        List.In normal normals ->
        SupportingNormal (Cone period) (zvec_to_qvec normal)) /\
      (forall face : QSet d,
        FaceOf (Cone period) face ->
        SameSet face
          (fun point =>
            Cone period point /\
            forall normal,
              List.In normal normals ->
              IntegerNormalOrthogonalToFace face normal ->
              qinner (zvec_to_qvec normal) point == 0)) /\
      (forall face : QSet d,
        FaceOf (Cone period) face ->
        exists witness : ZVec d,
          FacePeriod period face witness /\
          forall normal,
            List.In normal normals ->
            (IntegerNormalOrthogonalToFace face normal <->
             qinner (zvec_to_qvec normal)
               (zvec_to_qvec witness) == 0)).
Proof.
  intros d period Hperiodic Hpolyhedral.
  destruct (polyhedral_common_integer_face_normals
    d (Cone period) Hpolyhedral) as
    [normals [Hrepresentation [Hsupport Hfaces]]].
  exists normals. split; [exact Hrepresentation|].
  split; [exact Hsupport|].
  split; [exact Hfaces|].
  intros face Hface.
  apply face_zero_pattern_witness; try assumption.
  apply List.Forall_forall. exact Hsupport.
Qed.
