From Coq Require Import Fin Lia List QArith Vector.
From Mell.Geometry Require Import FiniteFaces Faces LatticeGordanInterface
  MathCompBridge QConeCore RationalDefinability.
From Mell.Audit Require Import FacesExamples RationalConeAssemblyExamples.

Import ListNotations.
Set Printing Implicit.

Check @all_sublists.
Check @all_sublists_complete.
Check @all_sublists_contains_source.
Check @all_sublists_contains_nil.
Check @all_sublists_length.
Check @face_has_sublist_generators.
Check @polyhedral_faces_finite_bounded.
Check @polyhedral_faces_finite.

Example all_sublists_empty :
    @all_sublists nat [] = [[]].
Proof. reflexivity. Qed.

Example all_sublists_duplicate_positions :
    all_sublists [1%nat; 1%nat] =
      [[]; [1%nat]; [1%nat]; [1%nat; 1%nat]].
Proof. reflexivity. Qed.

Example all_sublists_three_length :
    length (all_sublists [1%nat; 2%nat; 3%nat]) = 8%nat.
Proof. reflexivity. Qed.

Definition finite_faces_quadrant : QSet 2 :=
  qcone_generated [face_e1; face_e2].
Definition finite_faces_axis1 : QSet 2 := qcone_generated [face_e1].
Definition finite_faces_axis2 : QSet 2 := qcone_generated [face_e2].
Definition finite_faces_zero : QSet 2 := qcone_generated [].

Lemma face_e1_supports_quadrant :
    SupportingNormal finite_faces_quadrant face_e1.
Proof.
  apply supporting_normal_of_generators.
  intros generator Hin. cbn in Hin.
  destruct Hin as [Heq|[Heq|Hfalse]].
  - subst generator. unfold qinner, face_e1, face_e2, face_q2.
    cbn. unfold Qle. cbn. lia.
  - subst generator. unfold qinner, face_e1, face_e2, face_q2.
    cbn. unfold Qle. cbn. lia.
  - contradiction.
Qed.

Lemma face_e2_supports_quadrant :
    SupportingNormal finite_faces_quadrant face_e2.
Proof.
  apply supporting_normal_of_generators.
  intros generator Hin. cbn in Hin.
  destruct Hin as [Heq|[Heq|Hfalse]].
  - subst generator. unfold qinner, face_e1, face_e2, face_q2.
    cbn. unfold Qle. cbn. lia.
  - subst generator. unfold qinner, face_e1, face_e2, face_q2.
    cbn. unfold Qle. cbn. lia.
  - contradiction.
Qed.

Lemma finite_faces_axis1_face :
    FaceOf finite_faces_quadrant finite_faces_axis1.
Proof.
  exists [face_e2]. split.
  - constructor; [apply face_e2_supports_quadrant|constructor].
  - change (SameSet
      (qcone_generated (face_generators [face_e2] [face_e1; face_e2]))
      (fun point =>
        qcone_generated [face_e1; face_e2] point /\
        NormalOrthogonal [face_e2] point)).
    apply face_generator_filter. constructor;
      [apply face_e2_supports_quadrant|constructor].
Qed.

Lemma finite_faces_axis2_face :
    FaceOf finite_faces_quadrant finite_faces_axis2.
Proof.
  exists [face_e1]. split.
  - constructor; [apply face_e1_supports_quadrant|constructor].
  - change (SameSet
      (qcone_generated (face_generators [face_e1] [face_e1; face_e2]))
      (fun point =>
        qcone_generated [face_e1; face_e2] point /\
        NormalOrthogonal [face_e1] point)).
    apply face_generator_filter. constructor;
      [apply face_e1_supports_quadrant|constructor].
Qed.

Lemma finite_faces_zero_face :
    FaceOf finite_faces_quadrant finite_faces_zero.
Proof.
  exists [face_e1; face_e2]. split.
  - repeat constructor; [apply face_e1_supports_quadrant|
      apply face_e2_supports_quadrant].
  - change (SameSet
      (qcone_generated
        (face_generators [face_e1; face_e2] [face_e1; face_e2]))
      (fun point =>
        qcone_generated [face_e1; face_e2] point /\
        NormalOrthogonal [face_e1; face_e2] point)).
    apply face_generator_filter. repeat constructor;
      [apply face_e1_supports_quadrant|apply face_e2_supports_quadrant].
Qed.

Example quadrant_has_four_standard_faces :
    FaceOf finite_faces_quadrant finite_faces_quadrant /\
    FaceOf finite_faces_quadrant finite_faces_axis1 /\
    FaceOf finite_faces_quadrant finite_faces_axis2 /\
    FaceOf finite_faces_quadrant finite_faces_zero.
Proof.
  repeat split.
  - apply face_self.
  - apply finite_faces_axis1_face.
  - apply finite_faces_axis2_face.
  - apply finite_faces_zero_face.
Qed.

Theorem quadrant_faces_are_exactly_standard : forall face,
    FaceOf finite_faces_quadrant face ->
    SameSet face finite_faces_quadrant \/
    SameSet face finite_faces_axis1 \/
    SameSet face finite_faces_axis2 \/
    SameSet face finite_faces_zero.
Proof.
  intros face Hface.
  destruct (face_has_sublist_generators 2 [face_e1; face_e2] face Hface)
    as [selected [Hselected Hsame]].
  cbn in Hselected.
  destruct Hselected as [Heq|[Heq|[Heq|[Heq|Hfalse]]]].
  - subst selected. now right; right; right.
  - subst selected. now right; right; left.
  - subst selected. now right; left.
  - subst selected. now left.
  - contradiction.
Qed.

Lemma redundant_diagonal_preserves_quadrant :
    SameSet (qcone_generated [face_e1; face_e2; face_diag])
      finite_faces_quadrant.
Proof.
  intro point. split.
  - intros [generated [Hgenerated Hpoint]].
    apply (proj2 (qcone_generated_qvec_ext 2 [face_e1; face_e2]
      point generated Hpoint)).
    apply face_combination_substitute with
      (source := [face_e1; face_e2; face_diag]).
    + intros generator Hin. cbn in Hin.
      destruct Hin as [Heq|[Heq|[Heq|Hfalse]]].
      * subst generator. apply qcone_generated_generator. now left.
      * subst generator. apply qcone_generated_generator. now right; left.
      * subst generator.
        apply (proj2 (qcone_generated_qvec_ext 2 [face_e1; face_e2]
          face_diag (qvec_add face_e1 face_e2) face_diag_add_axes)).
        apply qcone_generated_add;
          apply qcone_generated_generator; [now left|now right; left].
      * contradiction.
    + exact Hgenerated.
  - intros [generated [Hgenerated Hpoint]]. exists generated. split.
    + apply qcone_combination_weaken with (source := [face_e1; face_e2]).
      * intros generator Hin. cbn in Hin.
        destruct Hin as [->|[->|[]]]; cbn; tauto.
      * exact Hgenerated.
    + exact Hpoint.
Qed.

Example redundant_diagonal_creates_no_new_face : forall face,
    FaceOf (qcone_generated [face_e1; face_e2; face_diag]) face ->
    SameSet face finite_faces_quadrant \/
    SameSet face finite_faces_axis1 \/
    SameSet face finite_faces_axis2 \/
    SameSet face finite_faces_zero.
Proof.
  intros face Hface. apply quadrant_faces_are_exactly_standard.
  apply face_of_cone_ext with
    (left := qcone_generated [face_e1; face_e2; face_diag]).
  - apply redundant_diagonal_preserves_quadrant.
  - exact Hface.
Qed.

Example finite_faces_dimension_zero :
    exists faces : list (QSet 0),
      (forall face, List.In face faces ->
        FaceOf (qcone_generated []) face) /\
      (forall face, FaceOf (qcone_generated []) face ->
        exists representative,
          List.In representative faces /\ SameSet face representative).
Proof.
  apply polyhedral_faces_finite,
    qcone_generated_is_rational_polyhedral_cone.
Qed.

Example finite_faces_zero_cone :
    exists faces : list (QSet 2),
      (forall face, List.In face faces ->
        FaceOf (qcone_generated [face_zero2]) face) /\
      (forall face, FaceOf (qcone_generated [face_zero2]) face ->
        exists representative,
          List.In representative faces /\ SameSet face representative).
Proof.
  apply polyhedral_faces_finite,
    qcone_generated_is_rational_polyhedral_cone.
Qed.

Example finite_faces_nonpointed_lineality :
    exists faces : list (QSet 2),
      (forall face, List.In face faces ->
        FaceOf (qcone_generated [face_e1; face_minus_e1]) face) /\
      (forall face, FaceOf (qcone_generated [face_e1; face_minus_e1]) face ->
        exists representative,
          List.In representative faces /\ SameSet face representative).
Proof.
  apply polyhedral_faces_finite,
    qcone_generated_is_rational_polyhedral_cone.
Qed.

Example finite_faces_full_space :
    exists faces : list (QSet 2),
      (forall face, List.In face faces -> FaceOf assembly_all face) /\
      (forall face, FaceOf assembly_all face ->
        exists representative,
          List.In representative faces /\ SameSet face representative).
Proof. apply polyhedral_faces_finite, assembly_full_space. Qed.

Lemma face_e1_not_in_zero_cone :
    ~ finite_faces_zero face_e1.
Proof.
  intros [generated [Hgenerated Heq]]. inversion Hgenerated; subst.
  - specialize (Heq Fin.F1).
    unfold face_e1, face_q2, qvec_zero in Heq. cbn in Heq.
    discriminate Heq.
  - contradiction.
Qed.

Lemma face_e2_not_in_zero_cone :
    ~ finite_faces_zero face_e2.
Proof.
  intros [generated [Hgenerated Heq]]. inversion Hgenerated; subst.
  - specialize (Heq (Fin.FS Fin.F1)).
    unfold face_e2, face_q2, qvec_zero in Heq. cbn in Heq.
    discriminate Heq.
  - contradiction.
Qed.

Lemma axis1_combination_second_zero : forall generated,
    QConeCombination [face_e1] generated ->
    generated (Fin.FS Fin.F1) == 0.
Proof.
  intros generated Hgenerated. induction Hgenerated.
  - reflexivity.
  - destruct H0 as [Heq|Hfalse]; [subst generator|contradiction].
    unfold qvec_add, qvec_scale, face_e1, face_q2 in *. cbn.
    setoid_rewrite IHHgenerated. ring.
Qed.

Lemma axis2_combination_first_zero : forall generated,
    QConeCombination [face_e2] generated ->
    generated Fin.F1 == 0.
Proof.
  intros generated Hgenerated. induction Hgenerated.
  - reflexivity.
  - destruct H0 as [Heq|Hfalse]; [subst generator|contradiction].
    unfold qvec_add, qvec_scale, face_e2, face_q2 in *. cbn.
    setoid_rewrite IHHgenerated. ring.
Qed.

Lemma face_e2_not_in_axis1 :
    ~ finite_faces_axis1 face_e2.
Proof.
  intros [generated [Hgenerated Heq]].
  pose proof (axis1_combination_second_zero generated Hgenerated) as Hz.
  specialize (Heq (Fin.FS Fin.F1)).
  unfold face_e2, face_q2 in Heq. cbn in Heq.
  assert (Hbad : 1 == 0).
  { transitivity (generated (Fin.FS Fin.F1)); assumption. }
  discriminate Hbad.
Qed.

Lemma face_e1_not_in_axis2 :
    ~ finite_faces_axis2 face_e1.
Proof.
  intros [generated [Hgenerated Heq]].
  pose proof (axis2_combination_first_zero generated Hgenerated) as Hz.
  specialize (Heq Fin.F1).
  unfold face_e1, face_q2 in Heq. cbn in Heq.
  assert (Hbad : 1 == 0).
  { transitivity (generated Fin.F1); assumption. }
  discriminate Hbad.
Qed.

Lemma same_set_separated_by : forall A (left right : A -> Prop) witness,
    left witness -> ~ right witness -> ~ SameSet left right.
Proof.
  intros A left right witness Hleft Hnotright Hsame.
  apply Hnotright, (proj1 (Hsame witness)), Hleft.
Qed.

Theorem quadrant_standard_faces_pairwise_distinct :
    ~ SameSet finite_faces_quadrant finite_faces_axis1 /\
    ~ SameSet finite_faces_quadrant finite_faces_axis2 /\
    ~ SameSet finite_faces_quadrant finite_faces_zero /\
    ~ SameSet finite_faces_axis1 finite_faces_axis2 /\
    ~ SameSet finite_faces_axis1 finite_faces_zero /\
    ~ SameSet finite_faces_axis2 finite_faces_zero.
Proof.
  repeat split.
  - apply same_set_separated_by with (witness := face_e2).
    + apply qcone_generated_generator. now right; left.
    + apply face_e2_not_in_axis1.
  - apply same_set_separated_by with (witness := face_e1).
    + apply qcone_generated_generator. now left.
    + apply face_e1_not_in_axis2.
  - apply same_set_separated_by with (witness := face_e1).
    + apply qcone_generated_generator. now left.
    + apply face_e1_not_in_zero_cone.
  - apply same_set_separated_by with (witness := face_e1).
    + apply qcone_generated_generator. now left.
    + apply face_e1_not_in_axis2.
  - apply same_set_separated_by with (witness := face_e1).
    + apply qcone_generated_generator. now left.
    + apply face_e1_not_in_zero_cone.
  - apply same_set_separated_by with (witness := face_e2).
    + apply qcone_generated_generator. now left.
    + apply face_e2_not_in_zero_cone.
Qed.

Check quadrant_standard_faces_pairwise_distinct.

Example zero_cone_is_not_a_face_of_full_space :
    ~ FaceOf (@assembly_all 2) finite_faces_zero.
Proof.
  intros [normals [Hsupport Hface]]. apply face_e1_not_in_zero_cone.
  apply (proj2 (Hface face_e1)). split; [exact I|].
  intros normal Hnormal.
  assert (Hnormal_support : SupportingNormal (@assembly_all 2) normal).
  { exact (proj1 (List.Forall_forall _ _) Hsupport normal Hnormal). }
  assert (Hpositive : 0 <= qinner normal face_e1).
  { apply Hnormal_support. exact I. }
  assert (Hnegative : 0 <= qinner normal (qvec_scale (-1) face_e1)).
  { apply Hnormal_support. exact I. }
  setoid_rewrite qinner_scale_right in Hnegative.
  setoid_replace ((-1) * qinner normal face_e1)
    with (- qinner normal face_e1) in Hnegative by ring.
  apply qnonnegative_sum_zero_left with
    (right := - qinner normal face_e1); try assumption. ring.
Qed.

Print Assumptions all_sublists_complete.
Print Assumptions all_sublists_length.
Print Assumptions face_has_sublist_generators.
Print Assumptions polyhedral_faces_finite_bounded.
Print Assumptions polyhedral_faces_finite.
