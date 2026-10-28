From Coq Require Import Lia List QArith.
From mathcomp Require Import all_ssreflect all_algebra.
From Mell.Geometry Require Import FaceDimension FaceOrder FiniteFaces
  Faces LatticeGordanInterface MathCompBridge QConeCore QcLinearAlgebra
  RationalDefinability.
From Mell.Audit Require Import FacesExamples FiniteFacesExamples.

Import ListNotations QcMathComp.
Local Open Scope nat_scope.
Set Printing Implicit.

Check @QSpanOf.
Check @QConeDifference.
Check @qspan_of_cone_difference.
Check @SpanPresentation.
Check @SpanDimension.
Check @polyhedral_span_dimension_exists.
Check @span_dimension_unique.
Check @span_dimension_le_presentation.
Check @span_dimension_monotone.
Check @span_dimension_same_set.
Check @proper_face_span_strict.
Check @proper_face_dimension_lt.
Check @proper_face_of_cone_dimension_lt.
Check @linearized_proper_faces_index_and_dimension.

Print Assumptions qspan_of_cone_difference.
Print Assumptions polyhedral_span_dimension_exists.
Print Assumptions proper_face_span_strict.
Print Assumptions proper_face_dimension_lt.
Print Assumptions proper_face_of_cone_dimension_lt.
Print Assumptions linearized_proper_faces_index_and_dimension.

Example dimension_zero_cone_has_dimension_zero :
    SpanDimension (qcone_generated ([] : list (QVec 0))) 0.
Proof.
  exists []. split; [apply qcone_span_presentation|].
  rewrite /qrow_generators /= span_nil dimv0. reflexivity.
Qed.

Example quadrant_zero_face_has_dimension_zero :
    SpanDimension finite_faces_zero 0.
Proof.
  exists []. split; [apply qcone_span_presentation|].
  rewrite /qrow_generators /= span_nil dimv0. reflexivity.
Qed.

Lemma zero_face_subset_axis1 :
    FaceSubset finite_faces_zero finite_faces_axis1.
Proof.
  intros point [generated [Hgenerated Hpoint]].
  exists generated. split.
  - apply qcone_combination_weaken with (source := []).
    + intros generator Hin. contradiction.
    + exact Hgenerated.
  - exact Hpoint.
Qed.

Lemma quadrant_and_axis1_exact_dimensions :
    SpanDimension finite_faces_quadrant 2 /\
    SpanDimension finite_faces_axis1 1.
Proof.
  destruct (polyhedral_span_dimension_exists 2 finite_faces_quadrant
    (qcone_generated_is_rational_polyhedral_cone 2 [face_e1; face_e2]))
    as [quadrant_dimension Hquadrant].
  destruct (polyhedral_span_dimension_exists 2 finite_faces_axis1
    (qcone_generated_is_rational_polyhedral_cone 2 [face_e1]))
    as [axis_dimension Haxis].
  assert (Haxis_quadrant : (axis_dimension < quadrant_dimension)%coq_nat).
  { apply (proper_face_dimension_lt 2 finite_faces_quadrant
      finite_faces_axis1 finite_faces_quadrant
      axis_dimension quadrant_dimension).
    - apply qcone_generated_is_rational_polyhedral_cone.
    - apply finite_faces_axis1_face.
    - apply face_self.
    - split.
      + exact (face_subset 2 finite_faces_quadrant finite_faces_axis1
          finite_faces_axis1_face).
      + intro Hsame.
        apply (proj1 quadrant_standard_faces_pairwise_distinct).
        now apply same_set_sym.
    - exact Haxis.
    - exact Hquadrant. }
  assert (Hzero_axis : (0 < axis_dimension)%coq_nat).
  { apply (proper_face_dimension_lt 2 finite_faces_quadrant
      finite_faces_zero finite_faces_axis1 0 axis_dimension).
    - apply qcone_generated_is_rational_polyhedral_cone.
    - apply finite_faces_zero_face.
    - apply finite_faces_axis1_face.
    - split; [apply zero_face_subset_axis1|].
      intro Hsame. apply (proj1 (proj2 (proj2 (proj2 (proj2
        quadrant_standard_faces_pairwise_distinct))))).
      now apply same_set_sym.
    - apply quadrant_zero_face_has_dimension_zero.
    - exact Haxis. }
  pose proof (span_dimension_le_presentation 2 finite_faces_quadrant
    [face_e1; face_e2] quadrant_dimension
    (qcone_span_presentation 2 [face_e1; face_e2]) Hquadrant) as Hbound.
  cbn in Hbound.
  assert (Haxis_value : axis_dimension = 1) by lia.
  assert (Hquadrant_value : quadrant_dimension = 2) by lia.
  subst axis_dimension quadrant_dimension. now split.
Qed.

Example quadrant_has_dimension_two :
    SpanDimension finite_faces_quadrant 2.
Proof. exact (proj1 quadrant_and_axis1_exact_dimensions). Qed.

Example quadrant_axis1_has_dimension_one :
    SpanDimension finite_faces_axis1 1.
Proof. exact (proj2 quadrant_and_axis1_exact_dimensions). Qed.

Example quadrant_axis1_dimension_strict : (1 < 2)%coq_nat.
Proof.
  apply (proper_face_dimension_lt 2 finite_faces_quadrant
    finite_faces_axis1 finite_faces_quadrant 1 2).
  - apply qcone_generated_is_rational_polyhedral_cone.
  - apply finite_faces_axis1_face.
  - apply face_self.
  - split.
    + exact (face_subset 2 finite_faces_quadrant finite_faces_axis1
        finite_faces_axis1_face).
    + intro Heq. apply face_e2_not_in_axis1.
      apply (proj2 (Heq face_e2)).
      apply qcone_generated_generator. now right; left.
  - apply quadrant_axis1_has_dimension_one.
  - apply quadrant_has_dimension_two.
Qed.

Example redundant_generators_preserve_dimension :
    forall redundant_dimension,
      SpanDimension
        (qcone_generated [face_e1; face_e2; face_diag])
        redundant_dimension ->
      redundant_dimension = 2.
Proof.
  intros redundant_dimension Hdimension.
  eapply span_dimension_same_set.
  - apply redundant_diagonal_preserves_quadrant.
  - exact Hdimension.
  - apply quadrant_has_dimension_two.
Qed.

Example duplicate_generators_preserve_dimension :
    forall duplicate_dimension,
      SpanDimension
        (qcone_generated [face_e1; face_e2; face_e1])
        duplicate_dimension ->
      duplicate_dimension = 2.
Proof.
  intros duplicate_dimension Hdimension.
  assert (Hsame : SameSet
      (qcone_generated [face_e1; face_e2; face_e1])
      finite_faces_quadrant).
  { intro point. split.
    - intros [generated [Hgenerated Hpoint]].
      apply (proj2 (qcone_generated_qvec_ext 2 [face_e1; face_e2]
        point generated Hpoint)).
      apply face_combination_substitute with
        (source := [face_e1; face_e2; face_e1]); [|exact Hgenerated].
      intros generator [->|[->|[->|[]]]];
        apply qcone_generated_generator; cbn; tauto.
    - intros [generated [Hgenerated Hpoint]]. exists generated. split.
      + apply qcone_combination_weaken with (source := [face_e1; face_e2]).
        * intros generator [->|[->|[]]]; cbn; tauto.
        * exact Hgenerated.
      + exact Hpoint. }
  eapply span_dimension_same_set.
  - exact Hsame.
  - exact Hdimension.
  - apply quadrant_has_dimension_two.
Qed.

Example nonpointed_lineality_has_a_well_defined_dimension :
    exists dimension,
      SpanDimension
        (qcone_generated [face_e1; face_minus_e1]) dimension.
Proof.
  apply polyhedral_span_dimension_exists,
    qcone_generated_is_rational_polyhedral_cone.
Qed.

Definition dimension_halfspace : QSet 2 :=
  qcone_generated [face_e1; face_minus_e1; face_e2].

Definition dimension_lineality : QSet 2 :=
  qcone_generated [face_e1; face_minus_e1].

Lemma face_e2_supports_dimension_halfspace :
    SupportingNormal dimension_halfspace face_e2.
Proof.
  unfold dimension_halfspace.
  apply supporting_normal_of_generators.
  intros generator Hin. cbn in Hin.
  destruct Hin as [Heq|[Heq|[Heq|Hfalse]]].
  - subst generator. unfold qinner, face_e1, face_e2, face_q2.
    cbn. unfold Qle. cbn. lia.
  - subst generator. unfold qinner, face_minus_e1, face_e2, face_q2.
    cbn. unfold Qle. cbn. lia.
  - subst generator. unfold qinner, face_e2, face_q2.
    cbn. unfold Qle. cbn. lia.
  - contradiction.
Qed.

Lemma dimension_lineality_face :
    FaceOf dimension_halfspace dimension_lineality.
Proof.
  exists [face_e2]. split.
  - constructor; [apply face_e2_supports_dimension_halfspace|constructor].
  - change (SameSet
      (qcone_generated
        (face_generators [face_e2]
          [face_e1; face_minus_e1; face_e2]))
      (fun point =>
        dimension_halfspace point /\
        NormalOrthogonal [face_e2] point)).
    apply face_generator_filter. constructor;
      [apply face_e2_supports_dimension_halfspace|constructor].
Qed.

Lemma dimension_lineality_proper :
    ProperFaceSubset dimension_lineality dimension_halfspace.
Proof.
  split.
  - exact (face_subset 2 dimension_halfspace dimension_lineality
      dimension_lineality_face).
  - intro Hsame.
    assert (He2_lineality : dimension_lineality face_e2).
    { apply (proj2 (Hsame face_e2)), qcone_generated_generator.
      cbn. tauto. }
    assert (Hsupport : List.Forall
        (SupportingNormal dimension_halfspace) [face_e2]).
    { constructor; [apply face_e2_supports_dimension_halfspace|constructor]. }
    pose proof (proj1 (face_generator_filter 2
      [face_e1; face_minus_e1; face_e2] [face_e2]
      Hsupport face_e2) He2_lineality) as [_ Horthogonal].
    specialize (Horthogonal face_e2
      (or_introl (@Logic.eq_refl (QVec 2) face_e2))).
    unfold qinner, face_e2, face_q2 in Horthogonal.
    cbn in Horthogonal. discriminate.
Qed.

Example lineality_halfspace_dimension_strict :
    exists lineality_dimension halfspace_dimension,
      SpanDimension dimension_lineality lineality_dimension /\
      SpanDimension dimension_halfspace halfspace_dimension /\
      (lineality_dimension < halfspace_dimension)%coq_nat.
Proof.
  destruct (polyhedral_span_dimension_exists 2 dimension_lineality
    (qcone_generated_is_rational_polyhedral_cone 2
      [face_e1; face_minus_e1])) as [lineality_dimension Hlineality].
  destruct (polyhedral_span_dimension_exists 2 dimension_halfspace
    (qcone_generated_is_rational_polyhedral_cone 2
      [face_e1; face_minus_e1; face_e2])) as
      [halfspace_dimension Hhalfspace].
  exists lineality_dimension, halfspace_dimension.
  repeat split; try assumption.
  apply (proper_face_dimension_lt 2 dimension_halfspace
    dimension_lineality dimension_halfspace
    lineality_dimension halfspace_dimension).
  - apply qcone_generated_is_rational_polyhedral_cone.
  - apply dimension_lineality_face.
  - apply face_self.
  - apply dimension_lineality_proper.
  - exact Hlineality.
  - exact Hhalfspace.
Qed.

Lemma quadrant_not_subset_axis1 :
    ~ FaceSubset finite_faces_quadrant finite_faces_axis1.
Proof.
  intro Hsubset. apply face_e2_not_in_axis1, Hsubset.
  apply qcone_generated_generator. cbn. tauto.
Qed.

Lemma quadrant_axis_linearized_order :
    forall i j face_i face_j,
      nth_error [finite_faces_quadrant; finite_faces_axis1] i = Some face_i ->
      nth_error [finite_faces_quadrant; finite_faces_axis1] j = Some face_j ->
      FaceSubset face_j face_i ->
      (i <= j)%coq_nat.
Proof.
  intros i j face_i face_j Hi Hj Hsubset.
  destruct i as [|[|i]]; destruct j as [|[|j]]; cbn in Hi, Hj.
  - lia.
  - lia.
  - destruct j; discriminate Hj.
  - inversion Hi; inversion Hj; subst.
    exfalso. now apply quadrant_not_subset_axis1.
  - lia.
  - destruct j; discriminate Hj.
  - destruct i; discriminate Hi.
  - destruct i; discriminate Hi.
  - destruct i; discriminate Hi.
Qed.

Lemma quadrant_axis_linearized_distinct :
    forall i j face_i face_j,
      nth_error [finite_faces_quadrant; finite_faces_axis1] i = Some face_i ->
      nth_error [finite_faces_quadrant; finite_faces_axis1] j = Some face_j ->
      i <> j ->
      ~ SameSet face_i face_j.
Proof.
  intros i j face_i face_j Hi Hj Hneq.
  destruct i as [|[|i]]; destruct j as [|[|j]]; cbn in Hi, Hj.
  - contradiction.
  - inversion Hi; inversion Hj; subst.
    exact (proj1 quadrant_standard_faces_pairwise_distinct).
  - destruct j; discriminate Hj.
  - inversion Hi; inversion Hj; subst. intro Hsame.
    apply (proj1 quadrant_standard_faces_pairwise_distinct).
    exact (same_set_sym _ _ _ Hsame).
  - contradiction.
  - destruct j; discriminate Hj.
  - destruct i; discriminate Hi.
  - destruct i; discriminate Hi.
  - destruct i; discriminate Hi.
Qed.

Lemma quadrant_axis_linearized_faces :
    forall face,
      List.In face [finite_faces_quadrant; finite_faces_axis1] ->
      FaceOf finite_faces_quadrant face.
Proof.
  intros face Hin. cbn in Hin.
  destruct Hin as [Heq|[Heq|Hfalse]].
  - subst face. apply face_self.
  - subst face. apply finite_faces_axis1_face.
  - contradiction.
Qed.

Example ordered_quadrant_axis_index_and_dimension :
    (0 < 1)%coq_nat /\ (1 < 2)%coq_nat.
Proof.
  apply (linearized_proper_faces_index_and_dimension
    2 finite_faces_quadrant
    [finite_faces_quadrant; finite_faces_axis1]
    quadrant_axis_linearized_order
    quadrant_axis_linearized_distinct
    quadrant_axis_linearized_faces
    (qcone_generated_is_rational_polyhedral_cone 2 [face_e1; face_e2])
    0 1 finite_faces_quadrant finite_faces_axis1 2 1);
    cbn; try reflexivity.
  - split.
    + exact (face_subset 2 finite_faces_quadrant finite_faces_axis1
        finite_faces_axis1_face).
    + intro Hsame. apply (proj1 quadrant_standard_faces_pairwise_distinct).
      now apply same_set_sym.
  - apply quadrant_has_dimension_two.
  - apply quadrant_axis1_has_dimension_one.
Qed.
