From Coq Require Import List.
From Mell.Geometry Require Import FaceOrder FiniteFaces Faces
  LatticeGordanInterface MathCompBridge QConeCore RationalDefinability.
From Mell.Audit Require Import FiniteFacesExamples.

Import ListNotations.
Set Printing Implicit.

Check @FaceSubset.
Check @ProperFaceSubset.
Check @ExtensionalNoDup.
Check @deduplicate_same_set.
Check @polyhedral_faces_linearized.

Print Assumptions face_subset_antisym_same_set.
Print Assumptions proper_face_subset_trans.
Print Assumptions deduplicate_same_set.
Print Assumptions polyhedral_faces_linearized.

Example deduplicate_repeated_quadrant :
    exists representatives,
      ListSubsequence representatives
        [finite_faces_quadrant; finite_faces_quadrant] /\
      ExtensionalNoDup representatives /\
      (forall face,
        List.In face [finite_faces_quadrant; finite_faces_quadrant] ->
        exists representative,
          List.In representative representatives /\
          SameSet face representative).
Proof. apply deduplicate_same_set. Qed.

Example quadrant_faces_linearized :
    exists faces : list (QSet 2),
      (exists tail, faces = finite_faces_quadrant :: tail) /\
      (forall face,
        List.In face faces -> FaceOf finite_faces_quadrant face) /\
      (forall face,
        FaceOf finite_faces_quadrant face ->
        exists representative,
          List.In representative faces /\
          SameSet face representative) /\
      (forall i j face_i face_j,
        nth_error faces i = Some face_i ->
        nth_error faces j = Some face_j ->
        i <> j -> ~ SameSet face_i face_j) /\
      (forall i j face_i face_j,
        nth_error faces i = Some face_i ->
        nth_error faces j = Some face_j ->
        FaceSubset face_j face_i -> i <= j).
Proof.
  apply polyhedral_faces_linearized,
    qcone_generated_is_rational_polyhedral_cone.
Qed.

Example dimension_zero_faces_linearized :
    exists faces : list (QSet 0),
      (exists tail, faces = qcone_generated [] :: tail) /\
      (forall face,
        List.In face faces -> FaceOf (qcone_generated []) face) /\
      (forall face,
        FaceOf (qcone_generated []) face ->
        exists representative,
          List.In representative faces /\ SameSet face representative) /\
      (forall i j face_i face_j,
        nth_error faces i = Some face_i ->
        nth_error faces j = Some face_j ->
        i <> j -> ~ SameSet face_i face_j) /\
      (forall i j face_i face_j,
        nth_error faces i = Some face_i ->
        nth_error faces j = Some face_j ->
        FaceSubset face_j face_i -> i <= j).
Proof.
  apply polyhedral_faces_linearized,
    qcone_generated_is_rational_polyhedral_cone.
Qed.
