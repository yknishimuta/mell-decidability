From Coq Require Import Fin Lia List QArith Qring Vector.
From Mell.Geometry Require Import Faces LatticeGordanInterface MathCompBridge
  QConeCore RationalDefinability RationalHToV.
From Mell.Audit Require Import RationalConeAssemblyExamples.

Import ListNotations.
Open Scope Q_scope.
Set Printing Implicit.

Check @SupportingNormal.
Check @NormalOrthogonal.
Check @FaceOf.
Check @face_generator_filter.
Check @face_self.
Check @face_subset.
Check @face_contains_zero.
Check @face_is_cone.
Check @polyhedral_face_finitely_generated.

Definition face_q2 (left right : Q) : QVec 2 :=
  fun index => Fin.caseS' index (fun _ => Q) left (fun _ => right).

Definition face_e1 : QVec 2 := face_q2 1 0.
Definition face_e2 : QVec 2 := face_q2 0 1.
Definition face_diag : QVec 2 := face_q2 1 1.
Definition face_minus_e1 : QVec 2 := face_q2 (-1) 0.
Definition face_zero2 : QVec 2 := face_q2 0 0.

Lemma generated_cone_self_face_polyhedral : forall d
    (generators : list (QVec d)),
    RationalPolyhedralCone (qcone_generated generators) /\
    FaceOf (qcone_generated generators) (qcone_generated generators).
Proof.
  intros. split.
  - apply qcone_generated_is_rational_polyhedral_cone.
  - apply face_self.
Qed.

Example face_dimension_zero :
    RationalPolyhedralCone (@qcone_generated 0 []).
Proof. apply qcone_generated_is_rational_polyhedral_cone. Qed.

Example face_zero_cone :
    FaceOf (qcone_generated [face_zero2])
      (qcone_generated [face_zero2]).
Proof. apply face_self. Qed.

Example face_nonpointed_lineality :
    FaceOf (qcone_generated [face_e1; face_minus_e1])
      (qcone_generated [face_e1; face_minus_e1]).
Proof. apply face_self. Qed.

Example face_full_space :
    FaceOf (@assembly_all 2) assembly_all /\
    RationalPolyhedralCone (@assembly_all 2).
Proof. split; [apply face_self|apply assembly_full_space]. Qed.

Example face_duplicate_zero_dependent_and_redundant_generators :
    RationalPolyhedralCone
      (qcone_generated [face_e1; face_e1; face_zero2; face_e2;
        face_diag]).
Proof. apply qcone_generated_is_rational_polyhedral_cone. Qed.

Lemma face_combination_substitute : forall d
    (source target : list (QVec d)) generated,
    (forall generator, List.In generator source ->
      qcone_generated target generator) ->
    QConeCombination source generated ->
    qcone_generated target generated.
Proof.
  intros d source target generated Hsubstitute Hgenerated.
  induction Hgenerated.
  - apply qcone_generated_zero.
  - apply qcone_generated_add.
    + apply qcone_generated_scale; [exact H|now apply Hsubstitute].
    + exact IHHgenerated.
Qed.

Lemma face_e2_supports_quadrant_with_redundant_diagonal :
    SupportingNormal
      (qcone_generated [face_e1; face_e2; face_diag]) face_e2.
Proof.
  apply supporting_normal_of_generators.
  intros generator Hin. cbn in Hin.
  destruct Hin as [Heq|[Heq|[Heq|Hfalse]]].
  - subst generator.
    unfold qinner, face_e1, face_e2, face_diag, face_q2;
    cbn; unfold Qle; cbn; lia.
  - subst generator.
    unfold qinner, face_e1, face_e2, face_diag, face_q2;
    cbn; unfold Qle; cbn; lia.
  - subst generator.
    unfold qinner, face_e1, face_e2, face_diag, face_q2;
    cbn; unfold Qle; cbn; lia.
  - contradiction.
Qed.

Example face_filter_keeps_exactly_exposed_generators :
    face_generators [face_e2] [face_e1; face_e2; face_diag] = [face_e1].
Proof. reflexivity. Qed.

Example quadrant_axis_is_filtered_face :
    SameSet
      (qcone_generated
        (face_generators [face_e2] [face_e1; face_e2; face_diag]))
      (fun point =>
        qcone_generated [face_e1; face_e2; face_diag] point /\
        NormalOrthogonal [face_e2] point).
Proof.
  apply face_generator_filter. constructor.
  - apply face_e2_supports_quadrant_with_redundant_diagonal.
  - constructor.
Qed.

Example empty_support_list_exposes_whole_cone :
    SameSet
      (qcone_generated (face_generators [] [face_e1; face_e2]))
      (fun point =>
        qcone_generated [face_e1; face_e2] point /\
        NormalOrthogonal [] point).
Proof. apply face_generator_filter. constructor. Qed.

Lemma face_diag_coordinates_equal : forall generated,
    QConeCombination [face_diag] generated ->
    generated Fin.F1 == generated (Fin.FS Fin.F1).
Proof.
  intros generated Hgenerated. induction Hgenerated.
  - reflexivity.
  - destruct H0 as [Heq|Hfalse]; [subst generator|contradiction].
    unfold qvec_add, qvec_scale, face_diag, face_q2 in *. cbn.
    now apply Qplus_comp.
Qed.

Lemma face_e1_not_in_diagonal_ray :
    ~ qcone_generated [face_diag] face_e1.
Proof.
  intros [generated [Hgenerated Heq]].
  pose proof (face_diag_coordinates_equal generated Hgenerated) as Hcoordinates.
  specialize (Heq Fin.F1) as Hfirst.
  specialize (Heq (Fin.FS Fin.F1)) as Hsecond.
  unfold face_e1, face_q2 in Hfirst, Hsecond. cbn in Hfirst, Hsecond.
  assert (Hbad : 1 == 0).
  { transitivity (generated Fin.F1); [exact Hfirst|].
    transitivity (generated (Fin.FS Fin.F1)); [exact Hcoordinates|].
    symmetry. exact Hsecond. }
  discriminate Hbad.
Qed.

Lemma face_diag_add_axes :
    QVecEq face_diag (qvec_add face_e1 face_e2).
Proof.
  intro index. refine (Fin.caseS' index
    (fun index => face_diag index == qvec_add face_e1 face_e2 index) _ _).
  - unfold face_diag, face_e1, face_e2, face_q2, qvec_add. cbn. ring.
  - intro tail. refine (Fin.caseS' tail
      (fun index => face_diag (Fin.FS index) ==
        qvec_add face_e1 face_e2 (Fin.FS index)) _ _).
    + unfold face_diag, face_e1, face_e2, face_q2, qvec_add. cbn. ring.
    + intro impossible. exact (Fin.case0
        (fun index => face_diag (Fin.FS (Fin.FS index)) ==
          qvec_add face_e1 face_e2 (Fin.FS (Fin.FS index))) impossible).
Qed.

Example redundant_generators_preserve_quadrant :
    SameSet
      (qcone_generated [face_e1; face_e1; face_zero2; face_e2; face_diag])
      (qcone_generated [face_e1; face_e2]).
Proof.
  intro point. split.
  - intros [generated [Hgenerated Hpoint]].
    apply (proj2 (qcone_generated_qvec_ext 2 [face_e1; face_e2]
      point generated Hpoint)).
    apply face_combination_substitute with
      (source := [face_e1; face_e1; face_zero2; face_e2; face_diag]).
    + intros generator Hin. cbn in Hin.
      destruct Hin as [Heq|[Heq|[Heq|[Heq|[Heq|Hfalse]]]]].
      * subst generator. apply qcone_generated_generator. now left.
      * subst generator. apply qcone_generated_generator. now left.
      * subst generator.
        assert (Hzero : QVecEq face_zero2 (qvec_zero 2)).
        { intro index. refine (Fin.caseS' index
             (fun index => face_zero2 index == qvec_zero 2 index) _ _).
          - reflexivity.
          - intro tail. refine (Fin.caseS' tail
                (fun index => face_zero2 (Fin.FS index) ==
                  qvec_zero 2 (Fin.FS index)) _ _); [reflexivity|].
            intro impossible. exact (Fin.case0
                (fun index => face_zero2 (Fin.FS (Fin.FS index)) ==
                  qvec_zero 2 (Fin.FS (Fin.FS index))) impossible). }
        apply (proj2 (qcone_generated_qvec_ext 2
          [face_e1; face_e2] face_zero2 (qvec_zero 2) Hzero)).
        apply qcone_generated_zero.
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

Example diagonal_subcone_is_not_a_quadrant_face :
    ~ FaceOf (qcone_generated [face_e1; face_e2])
        (qcone_generated [face_diag]).
Proof.
  intros [normals [Hsupport Hface]].
  assert (Hdiag_face : qcone_generated [face_diag] face_diag).
  { apply qcone_generated_generator. now left. }
  apply (proj1 (Hface face_diag)) in Hdiag_face as [_ Hdiag_orthogonal].
  assert (He1_orthogonal : NormalOrthogonal normals face_e1).
  { intros normal Hnormal.
    assert (Hnormal_support :
        SupportingNormal (qcone_generated [face_e1; face_e2]) normal).
    { exact (proj1 (List.Forall_forall _ _) Hsupport normal Hnormal). }
    assert (He1_nonnegative : 0 <= qinner normal face_e1).
    { apply Hnormal_support, qcone_generated_generator. now left. }
    assert (He2_nonnegative : 0 <= qinner normal face_e2).
    { apply Hnormal_support, qcone_generated_generator. now right; left. }
    assert (Hsum : qinner normal face_e1 + qinner normal face_e2 == 0).
    { transitivity (qinner normal (qvec_add face_e1 face_e2)).
      - symmetry. apply qinner_add_right.
      - transitivity (qinner normal face_diag).
        + apply qinner_qvec_ext_right. apply qvec_eq_sym, face_diag_add_axes.
        + apply Hdiag_orthogonal. exact Hnormal. }
    now apply qnonnegative_sum_zero_left with
      (right := qinner normal face_e2).
  }
  apply face_e1_not_in_diagonal_ray.
  apply (proj2 (Hface face_e1)). split.
  - apply qcone_generated_generator. now left.
  - exact He1_orthogonal.
Qed.

Example every_exposed_face_remains_polyhedral :
    forall face,
      FaceOf (qcone_generated [face_e1; face_e2; face_diag]) face ->
      RationalPolyhedralCone face.
Proof.
  intros face Hface. apply polyhedral_face_finitely_generated with
    (cone := qcone_generated [face_e1; face_e2; face_diag]); [|exact Hface].
  apply qcone_generated_is_rational_polyhedral_cone.
Qed.

Print Assumptions face_generator_filter.
Print Assumptions face_self.
Print Assumptions face_subset.
Print Assumptions face_contains_zero.
Print Assumptions face_is_cone.
Print Assumptions polyhedral_face_finitely_generated.
