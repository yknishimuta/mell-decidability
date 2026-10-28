From Coq Require Import Fin Lia List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import CommonIntegerFaceNormals Faces FiniteFaces
  LatticeGordanInterface MathCompBridge QConeCore RationalDefinability.
From Mell.Audit Require Import FiniteFacesExamples FacesExamples
  QIntegerHRepExamples RationalConeAssemblyExamples.

Import ListNotations.
Open Scope Q_scope.

Check @IntegerNormalOrthogonalToFace.
Check @qnormal_integer_supporting.
Check @qnormal_integer_zero_iff.
Check @integer_face_witness.
Check @face_active_integer_normals.
Check @face_inactive_integer_normals.
Check @polyhedral_common_integer_face_normals.

Definition b2_generated_common_normals {d}
    (generators : list (QVec d)) :=
  polyhedral_common_integer_face_normals d (qcone_generated generators)
    (qcone_generated_is_rational_polyhedral_cone d generators).

Example common_normals_dimension_zero :=
  b2_generated_common_normals ([] : list (QVec 0)).

Example common_normals_zero_cone :=
  b2_generated_common_normals [face_zero2].

Example common_normals_low_rank_ray :=
  b2_generated_common_normals [face_e1].

Example common_normals_nonpointed_lineality :=
  b2_generated_common_normals [face_e1; face_minus_e1].

Example common_normals_redundant_generators :=
  b2_generated_common_normals
    [face_e1; face_e1; face_zero2; face_e2; face_diag].

Example common_normals_full_space :
    exists normals : list (ZVec 2),
      (forall point : QVec 2,
        assembly_all point <->
        forall normal,
          List.In normal normals ->
          0 <= qinner (zvec_to_qvec normal) point) /\
      (forall normal,
        List.In normal normals ->
        SupportingNormal assembly_all (zvec_to_qvec normal)) /\
      (forall face : QSet 2,
        FaceOf assembly_all face ->
        SameSet face
          (fun point =>
            assembly_all point /\
            forall normal,
              List.In normal normals ->
              IntegerNormalOrthogonalToFace face normal ->
              qinner (zvec_to_qvec normal) point == 0)).
Proof.
  apply polyhedral_common_integer_face_normals, assembly_full_space.
Qed.

Definition b2_reconstructed_by (normals : list (ZVec 2))
    (face : QSet 2) : QSet 2 :=
  fun point =>
    finite_faces_quadrant point /\
    forall normal,
      List.In normal normals ->
      IntegerNormalOrthogonalToFace face normal ->
      qinner (zvec_to_qvec normal) point == 0.

Example quadrant_one_common_list_reconstructs_all_four_faces :
    exists normals : list (ZVec 2),
      SameSet finite_faces_quadrant
        (b2_reconstructed_by normals finite_faces_quadrant) /\
      SameSet finite_faces_axis1
        (b2_reconstructed_by normals finite_faces_axis1) /\
      SameSet finite_faces_axis2
        (b2_reconstructed_by normals finite_faces_axis2) /\
      SameSet finite_faces_zero
        (b2_reconstructed_by normals finite_faces_zero).
Proof.
  destruct (polyhedral_common_integer_face_normals 2 finite_faces_quadrant
    (qcone_generated_is_rational_polyhedral_cone 2 [face_e1; face_e2])) as
    [normals [_ [_ Hfaces]]].
  exists normals. split.
  - apply Hfaces, face_self.
  - split.
    + apply Hfaces, finite_faces_axis1_face.
    + split.
      * apply Hfaces, finite_faces_axis2_face.
      * apply Hfaces, finite_faces_zero_face.
Qed.

Definition b2_axis1_alias : QSet 2 :=
  fun point => finite_faces_axis1 point.

Lemma b2_axis1_alias_same : SameSet finite_faces_axis1 b2_axis1_alias.
Proof. intro point. reflexivity. Qed.

Example extensionally_equal_face_representative_supported :
    FaceOf finite_faces_quadrant b2_axis1_alias.
Proof.
  apply face_of_face_ext with (left := finite_faces_axis1).
  - exact b2_axis1_alias_same.
  - apply finite_faces_axis1_face.
Qed.

Example one_common_list_reconstructs_extensionally_equal_faces :
    exists normals : list (ZVec 2),
      SameSet finite_faces_axis1
        (b2_reconstructed_by normals finite_faces_axis1) /\
      SameSet b2_axis1_alias
        (b2_reconstructed_by normals b2_axis1_alias).
Proof.
  destruct (polyhedral_common_integer_face_normals 2 finite_faces_quadrant
    (qcone_generated_is_rational_polyhedral_cone 2 [face_e1; face_e2])) as
    [normals [_ [_ Hfaces]]].
  exists normals. split.
  - apply Hfaces, finite_faces_axis1_face.
  - apply Hfaces, extensionally_equal_face_representative_supported.
Qed.

Example empty_normal_list_has_empty_active_sublist :
    exists active : list (ZVec 2),
      forall normal,
        List.In normal active <->
        List.In normal [] /\
        IntegerNormalOrthogonalToFace finite_faces_quadrant normal.
Proof. apply face_active_integer_normals. Qed.

Definition b2_zero_integer_normal : ZVec 2 :=
  @Vector.cons Z 0%Z 1 (@Vector.cons Z 0%Z 0 (@Vector.nil Z)).

Example duplicate_and_zero_normals_have_active_and_inactive_sublists :
    (exists active : list (ZVec 2),
      forall normal,
        List.In normal active <->
        List.In normal
          [b2_zero_integer_normal; d_integer_pair; d_integer_pair] /\
        IntegerNormalOrthogonalToFace finite_faces_axis1 normal) /\
    (exists inactive : list (ZVec 2),
      forall normal,
        List.In normal inactive <->
        List.In normal
          [b2_zero_integer_normal; d_integer_pair; d_integer_pair] /\
        ~ IntegerNormalOrthogonalToFace finite_faces_axis1 normal).
Proof.
  split; [apply face_active_integer_normals|apply face_inactive_integer_normals].
Qed.

Example concrete_integerization_preserves_zero : forall point : QVec 2,
    (qinner d_half_minus_three_fourths point == 0 <->
     qinner (zvec_to_qvec d_integer_pair) point == 0).
Proof.
  apply (qnormal_integer_zero_iff 2 d_half_minus_three_fourths
    d_integer_pair 4%positive d_pair_cleared_by_four).
Qed.

Example concrete_integerization_preserves_support :
    SupportingNormal (fun _ : QVec 2 => True)
      d_half_minus_three_fourths ->
    SupportingNormal (fun _ : QVec 2 => True)
      (zvec_to_qvec d_integer_pair).
Proof.
  apply qnormal_integer_supporting with
    (normal := d_half_minus_three_fourths) (multiplier := 4%positive).
  exact d_pair_cleared_by_four.
Qed.

Example nonnormalized_standard_q_values_are_numerically_equal :
    Qmake 1 2%positive == Qmake 2 4%positive.
Proof. reflexivity. Qed.

Definition b2_half_point : QVec 1 := fun _ => Qmake 1 2%positive.
Definition b2_two_fourths_point : QVec 1 :=
  fun _ => Qmake 2 4%positive.

Example nonnormalized_qvectors_are_numerically_equal :
    QVecEq b2_half_point b2_two_fourths_point.
Proof.
  intro index. refine (Fin.caseS' index (fun index =>
    b2_half_point index == b2_two_fourths_point index) _ _).
  - reflexivity.
  - intro impossible. inversion impossible.
Qed.

Example integer_face_witness_for_maximal_face :
    exists normals : list (ZVec 2),
      (forall normal,
        List.In normal normals ->
        SupportingNormal finite_faces_quadrant
          (zvec_to_qvec normal)) /\
      SameSet finite_faces_quadrant
        (fun point =>
          finite_faces_quadrant point /\
          forall normal,
            List.In normal normals ->
            qinner (zvec_to_qvec normal) point == 0).
Proof. apply integer_face_witness, face_self. Qed.

Example integer_face_witness_for_minimal_face :
    exists normals : list (ZVec 2),
      (forall normal,
        List.In normal normals ->
        SupportingNormal finite_faces_quadrant
          (zvec_to_qvec normal)) /\
      SameSet finite_faces_zero
        (fun point =>
          finite_faces_quadrant point /\
          forall normal,
            List.In normal normals ->
            qinner (zvec_to_qvec normal) point == 0).
Proof. apply integer_face_witness, finite_faces_zero_face. Qed.

Print Assumptions qnormal_integer_supporting.
Print Assumptions qnormal_integer_zero_iff.
Print Assumptions integer_face_witness.
Print Assumptions face_active_integer_normals.
Print Assumptions face_inactive_integer_normals.
Print Assumptions polyhedral_common_integer_face_normals.
