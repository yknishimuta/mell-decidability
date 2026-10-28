From Coq Require Import Fin Lia List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import CommonIntegerFaceNormals Cone
  FaceStrippingExtract FaceZeroPatternWitness Faces MathCompBridge Periodic
  QConeCore RationalDefinability RationalHToV.
From Mell.Order Require Import PeriodicOrder.
From Mell.Audit Require Import FaceStrippingExtractExamples.

Import ListNotations.
Open Scope Q_scope.

Check @inactive_supporting_normal_positive_on_face.
Check @inactive_normals_positive_sum.
Check @face_positive_ray_reflect.
Check @face_zero_pattern_witness.
Check @periodic_polyhedral_common_zero_pattern_normals.

Definition b3_zero_period {d} : ZSet d :=
  zvec_generated ([] : list (ZVec d)).

Definition b3_two_nat_period : ZSet 1 :=
  zvec_generated [extract_z1 2].

Definition b3_low_rank_period : ZSet 2 :=
  zvec_generated [extract_z2 1 0].

Example zero_pattern_dimension_zero :
    exists witness : ZVec 0,
      FacePeriod (@b3_zero_period 0) (Cone (@b3_zero_period 0)) witness /\
      forall normal : ZVec 0,
        List.In normal [] ->
        (IntegerNormalOrthogonalToFace (Cone (@b3_zero_period 0)) normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
Proof.
  apply face_zero_pattern_witness.
  - apply generated_periodic.
  - apply face_self.
  - constructor.
Qed.

Example zero_pattern_zero_cone :
    exists witness : ZVec 2,
      FacePeriod (@b3_zero_period 2) (Cone (@b3_zero_period 2)) witness /\
      forall normal : ZVec 2,
        List.In normal [] ->
        (IntegerNormalOrthogonalToFace (Cone (@b3_zero_period 2)) normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
Proof.
  apply face_zero_pattern_witness.
  - apply generated_periodic.
  - apply face_self.
  - constructor.
Qed.

Example zero_pattern_low_rank_period :
    exists witness : ZVec 2,
      FacePeriod b3_low_rank_period (Cone b3_low_rank_period) witness /\
      forall normal : ZVec 2,
        List.In normal [] ->
        (IntegerNormalOrthogonalToFace (Cone b3_low_rank_period) normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
Proof.
  apply face_zero_pattern_witness.
  - apply generated_periodic.
  - apply face_self.
  - constructor.
Qed.

Example zero_pattern_empty_normals : forall d (period : ZSet d)
    (face : QSet d),
    Periodic period ->
    FaceOf (Cone period) face ->
    exists witness : ZVec d,
      FacePeriod period face witness /\
      forall normal : ZVec d,
        List.In normal [] ->
        (IntegerNormalOrthogonalToFace face normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
Proof.
  intros d period face Hperiodic Hface.
  apply face_zero_pattern_witness; try assumption. constructor.
Qed.

Example zero_pattern_nat_contract :
    List.Forall
      (fun normal =>
        SupportingNormal (Cone extract_nat_period) (zvec_to_qvec normal))
      [extract_z1 1] ->
    exists witness : ZVec 1,
      FacePeriod extract_nat_period (Cone extract_nat_period) witness /\
      forall normal : ZVec 1,
        List.In normal [extract_z1 1] ->
        (IntegerNormalOrthogonalToFace
           (Cone extract_nat_period) normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
Proof.
  intro Hsupport. apply face_zero_pattern_witness.
  - apply generated_periodic.
  - apply face_self.
  - exact Hsupport.
Qed.

Example zero_pattern_nat_proper_zero_face :
    exists witness : ZVec 1,
      FacePeriod extract_nat_period extract_nat_zero_face witness /\
      forall normal : ZVec 1,
        List.In normal [extract_z1 1] ->
        (IntegerNormalOrthogonalToFace extract_nat_zero_face normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
Proof.
  apply face_zero_pattern_witness.
  - apply generated_periodic.
  - apply extract_nat_zero_face_is_face.
  - constructor; [|constructor].
    change (SupportingNormal (Cone extract_nat_period) (extract_q1 1)).
    apply extract_nat_supporting_normal.
Qed.

Lemma extract_nat_zero_supporting_normal :
    SupportingNormal (Cone extract_nat_period)
      (zvec_to_qvec (extract_z1 0)).
Proof.
  intros point Hpoint.
  setoid_replace (qinner (zvec_to_qvec (extract_z1 0)) point) with 0.
  - apply Qle_refl.
  - unfold qinner, extract_z1, zvec_to_qvec, qrow_apply,
      qvec_to_vector. cbn. ring.
Qed.

Example duplicate_and_zero_supporting_normals :
    exists witness : ZVec 1,
      FacePeriod extract_nat_period (Cone extract_nat_period) witness /\
      forall normal : ZVec 1,
        List.In normal [extract_z1 1; extract_z1 1; extract_z1 0] ->
        (IntegerNormalOrthogonalToFace (Cone extract_nat_period) normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
Proof.
  apply face_zero_pattern_witness.
  - apply generated_periodic.
  - apply face_self.
  - repeat constructor.
    + change (SupportingNormal (Cone extract_nat_period) (extract_q1 1)).
      apply extract_nat_supporting_normal.
    + change (SupportingNormal (Cone extract_nat_period) (extract_q1 1)).
      apply extract_nat_supporting_normal.
    + apply extract_nat_zero_supporting_normal.
Qed.

Example zero_pattern_two_nat_contract :
    List.Forall
      (fun normal =>
        SupportingNormal (Cone b3_two_nat_period) (zvec_to_qvec normal))
      [extract_z1 1] ->
    exists witness : ZVec 1,
      FacePeriod b3_two_nat_period (Cone b3_two_nat_period) witness /\
      forall normal : ZVec 1,
        List.In normal [extract_z1 1] ->
        (IntegerNormalOrthogonalToFace
           (Cone b3_two_nat_period) normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
Proof.
  intro Hsupport. apply face_zero_pattern_witness.
  - apply generated_periodic.
  - apply face_self.
  - exact Hsupport.
Qed.

Example zero_pattern_quadrant_contract :
    List.Forall
      (fun normal =>
        SupportingNormal (Cone extract_quadrant_period)
          (zvec_to_qvec normal))
      [extract_z2 1 0; extract_z2 0 1] ->
    exists witness : ZVec 2,
      FacePeriod extract_quadrant_period
        (Cone extract_quadrant_period) witness /\
      forall normal : ZVec 2,
        List.In normal [extract_z2 1 0; extract_z2 0 1] ->
        (IntegerNormalOrthogonalToFace
           (Cone extract_quadrant_period) normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
Proof.
  intro Hsupport. apply face_zero_pattern_witness.
  - apply generated_periodic.
  - apply face_self.
  - exact Hsupport.
Qed.

Lemma b3_zero_normal_supporting : forall cone : QSet 1,
    SupportingNormal cone (zvec_to_qvec (extract_z1 0)).
Proof.
  intros cone point Hpoint.
  setoid_replace (qinner (zvec_to_qvec (extract_z1 0)) point) with 0.
  - apply Qle_refl.
  - unfold qinner, extract_z1, zvec_to_qvec, qrow_apply,
      qvec_to_vector. cbn. ring.
Qed.

Example zero_pattern_lineality_contract :
    exists witness : ZVec 1,
      FacePeriod extract_lineality_period
        (Cone extract_lineality_period) witness /\
      forall normal : ZVec 1,
        List.In normal [extract_z1 0; extract_z1 0] ->
        (IntegerNormalOrthogonalToFace
           (Cone extract_lineality_period) normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
Proof.
  apply face_zero_pattern_witness.
  - apply generated_periodic.
  - apply face_self.
  - repeat constructor; apply b3_zero_normal_supporting.
Qed.

Definition b3_q2 (left right : Q) : QVec 2 :=
  fun index => Fin.caseS' index (fun _ => Q) left
    (fun tail => Fin.caseS' tail (fun _ => Q) right
      (fun impossible => Fin.case0 (fun _ => Q) impossible)).

Definition b3_quadrant : QSet 2 :=
  fun point => 0 <= point Fin.F1 /\ 0 <= point (Fin.FS Fin.F1).

Definition b3_axis1 : QSet 2 :=
  fun point => b3_quadrant point /\ point (Fin.FS Fin.F1) == 0.

Definition b3_origin : QSet 2 :=
  fun point =>
    b3_quadrant point /\ point Fin.F1 == 0 /\
    point (Fin.FS Fin.F1) == 0.

Lemma b3_inner_e1 : forall point : QVec 2,
    qinner (zvec_to_qvec (extract_z2 1 0)) point == point Fin.F1.
Proof.
  intro point. unfold qinner, extract_z2, zvec_to_qvec, qrow_apply,
    qvec_to_vector. cbn. ring.
Qed.

Lemma b3_inner_e2 : forall point : QVec 2,
    qinner (zvec_to_qvec (extract_z2 0 1)) point ==
      point (Fin.FS Fin.F1).
Proof.
  intro point. unfold qinner, extract_z2, zvec_to_qvec, qrow_apply,
    qvec_to_vector. cbn. ring.
Qed.

Lemma b3_quadrant_e1 : b3_quadrant (b3_q2 1 0).
Proof. split; unfold b3_q2, Qle; cbn; lia. Qed.

Lemma b3_quadrant_e2 : b3_quadrant (b3_q2 0 1).
Proof. split; unfold b3_q2, Qle; cbn; lia. Qed.

Lemma b3_axis1_e1 : b3_axis1 (b3_q2 1 0).
Proof. split; [apply b3_quadrant_e1|reflexivity]. Qed.

Lemma b3_origin_zero : b3_origin (b3_q2 0 0).
Proof. repeat split; unfold b3_q2; cbn; apply Qle_refl || reflexivity. Qed.

Lemma b3_e1_not_orthogonal_quadrant :
    ~ IntegerNormalOrthogonalToFace b3_quadrant (extract_z2 1 0).
Proof.
  intro Horthogonal.
  specialize (Horthogonal (b3_q2 1 0) b3_quadrant_e1).
  setoid_rewrite b3_inner_e1 in Horthogonal.
  unfold b3_q2 in Horthogonal. cbn in Horthogonal.
  discriminate Horthogonal.
Qed.

Lemma b3_e2_not_orthogonal_quadrant :
    ~ IntegerNormalOrthogonalToFace b3_quadrant (extract_z2 0 1).
Proof.
  intro Horthogonal.
  specialize (Horthogonal (b3_q2 0 1) b3_quadrant_e2).
  setoid_rewrite b3_inner_e2 in Horthogonal.
  unfold b3_q2 in Horthogonal. cbn in Horthogonal.
  discriminate Horthogonal.
Qed.

Lemma b3_e1_not_orthogonal_axis1 :
    ~ IntegerNormalOrthogonalToFace b3_axis1 (extract_z2 1 0).
Proof.
  intro Horthogonal.
  specialize (Horthogonal (b3_q2 1 0) b3_axis1_e1).
  setoid_rewrite b3_inner_e1 in Horthogonal.
  unfold b3_q2 in Horthogonal. cbn in Horthogonal.
  discriminate Horthogonal.
Qed.

Lemma b3_e2_orthogonal_axis1 :
    IntegerNormalOrthogonalToFace b3_axis1 (extract_z2 0 1).
Proof.
  intros point [_ Hzero]. setoid_rewrite b3_inner_e2. exact Hzero.
Qed.

Lemma b3_e1_orthogonal_origin :
    IntegerNormalOrthogonalToFace b3_origin (extract_z2 1 0).
Proof.
  intros point [_ [Hzero _]]. setoid_rewrite b3_inner_e1. exact Hzero.
Qed.

Lemma b3_e2_orthogonal_origin :
    IntegerNormalOrthogonalToFace b3_origin (extract_z2 0 1).
Proof.
  intros point [_ [_ Hzero]]. setoid_rewrite b3_inner_e2. exact Hzero.
Qed.

Lemma b3_quadrant_period_e1 : extract_quadrant_period (extract_z2 1 0).
Proof. apply generated_generator. now left. Qed.

Lemma b3_quadrant_period_e2 : extract_quadrant_period (extract_z2 0 1).
Proof. apply generated_generator. now right; left. Qed.

Lemma b3_quadrant_period_one_one :
    extract_quadrant_period (extract_z2 1 1).
Proof.
  replace (extract_z2 1 1) with
    (zvec_add (extract_z2 1 0) (extract_z2 0 1)) by reflexivity.
  apply (proj2 (generated_periodic 2
    [extract_z2 1 0; extract_z2 0 1]));
    [exact b3_quadrant_period_e1|exact b3_quadrant_period_e2].
Qed.

Example quadrant_maximal_face_specific_witness :
    FacePeriod extract_quadrant_period b3_quadrant (extract_z2 1 1) /\
    forall normal,
      List.In normal [extract_z2 1 0; extract_z2 0 1] ->
      (IntegerNormalOrthogonalToFace b3_quadrant normal <->
       qinner (zvec_to_qvec normal)
         (zvec_to_qvec (extract_z2 1 1)) == 0).
Proof.
  split.
  - split; [exact b3_quadrant_period_one_one|].
    split; unfold zvec_to_qvec, extract_z2, Qle; cbn; lia.
  - intros normal [Heq | [Heq | Hin]]; [subst normal|subst normal|inversion Hin].
    + split; [intro H; contradiction b3_e1_not_orthogonal_quadrant|].
      intro Hzero. exfalso.
      setoid_rewrite b3_inner_e1 in Hzero. cbn in Hzero.
      discriminate Hzero.
    + split; [intro H; contradiction b3_e2_not_orthogonal_quadrant|].
      intro Hzero. exfalso.
      setoid_rewrite b3_inner_e2 in Hzero. cbn in Hzero.
      discriminate Hzero.
Qed.

Example quadrant_axis_face_specific_witness :
    FacePeriod extract_quadrant_period b3_axis1 (extract_z2 1 0) /\
    forall normal,
      List.In normal [extract_z2 1 0; extract_z2 0 1] ->
      (IntegerNormalOrthogonalToFace b3_axis1 normal <->
       qinner (zvec_to_qvec normal)
         (zvec_to_qvec (extract_z2 1 0)) == 0).
Proof.
  split.
  - split; [exact b3_quadrant_period_e1|].
    split; [split; unfold zvec_to_qvec, extract_z2, Qle; cbn; lia|].
    reflexivity.
  - intros normal [Heq | [Heq | Hin]]; [subst normal|subst normal|inversion Hin].
    + split; [intro H; contradiction b3_e1_not_orthogonal_axis1|].
      intro Hzero. exfalso.
      setoid_rewrite b3_inner_e1 in Hzero. cbn in Hzero.
      discriminate Hzero.
    + split; intro H.
      * setoid_rewrite b3_inner_e2. reflexivity.
      * exact b3_e2_orthogonal_axis1.
Qed.

Example quadrant_zero_face_specific_witness :
    FacePeriod extract_quadrant_period b3_origin (extract_z2 0 0) /\
    forall normal,
      List.In normal [extract_z2 1 0; extract_z2 0 1] ->
      (IntegerNormalOrthogonalToFace b3_origin normal <->
       qinner (zvec_to_qvec normal)
         (zvec_to_qvec (extract_z2 0 0)) == 0).
Proof.
  split.
  - split.
    + change (extract_quadrant_period (zvec_zero 2)).
      exact (proj1 (generated_periodic 2
        [extract_z2 1 0; extract_z2 0 1])).
    + repeat split; unfold zvec_to_qvec, extract_z2; cbn;
        apply Qle_refl || reflexivity.
  - intros normal [Heq | [Heq | Hin]]; [subst normal|subst normal|inversion Hin].
    + split; intro H.
      * setoid_rewrite b3_inner_e1. reflexivity.
      * exact b3_e1_orthogonal_origin.
    + split; intro H.
      * setoid_rewrite b3_inner_e2. reflexivity.
      * exact b3_e2_orthogonal_origin.
Qed.

Example positive_rational_scale_preserves_zero_pattern :
    forall normal point : QVec 2,
      (qinner normal (qvec_scale (Qmake 2 4%positive) point) == 0 <->
       qinner normal point == 0).
Proof.
  intros normal point. setoid_rewrite qinner_scale_right. split; intro Hzero.
  - destruct (Qmult_integral _ _ Hzero) as [Hcoefficient | Hinner].
    + discriminate Hcoefficient.
    + exact Hinner.
  - setoid_rewrite Hzero. ring.
Qed.

Print Assumptions inactive_supporting_normal_positive_on_face.
Print Assumptions inactive_normals_positive_sum.
Print Assumptions face_positive_ray_reflect.
Print Assumptions face_zero_pattern_witness.
Print Assumptions periodic_polyhedral_common_zero_pattern_normals.
