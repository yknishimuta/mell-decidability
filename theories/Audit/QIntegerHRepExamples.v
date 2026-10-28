From Coq Require Import Fin Lia List QArith Vector.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Faces LatticeGordanInterface LatticeGordanV
  MathCompBridge QConeCore QIntegerHRep.

Import ListNotations.
Open Scope Q_scope.

Check @qnormal_clear_denominators.
Check @qnormal_integer_inner.
Check @qnormal_integer_nonnegative_iff.
Check @qnormal_list_integer_hrep.
Check @polyhedral_cone_integer_hrep.

Definition d_pair (left right : Q) : QVec 2 :=
  fun index => Fin.caseS' index (fun _ => Q) left (fun _ => right).

Definition d_half_minus_three_fourths : QVec 2 :=
  d_pair (Qmake 1 2%positive) (Qmake (-3) 4%positive).

Definition d_integer_pair : ZVec 2 :=
  @Vector.cons Z 2%Z 1
    (@Vector.cons Z (-3)%Z 0 (@Vector.nil Z)).

Lemma d_pair_cleared_by_four : forall index : Fin.t 2,
    zvec_to_qvec d_integer_pair index ==
      inject_Z (Z.pos 4%positive) * d_half_minus_three_fourths index.
Proof.
  intro index. refine (Fin.caseS' index (fun index =>
    zvec_to_qvec d_integer_pair index ==
      inject_Z (Z.pos 4%positive) * d_half_minus_three_fourths index) _ _).
  - reflexivity.
  - intro tail. refine (Fin.caseS' tail (fun tail =>
      zvec_to_qvec d_integer_pair (Fin.FS tail) ==
        inject_Z (Z.pos 4%positive) *
          d_half_minus_three_fourths (Fin.FS tail)) _ _).
    + reflexivity.
    + intro impossible. inversion impossible.
Qed.

Lemma integer_normal_uses_multiplier_one : forall index : Fin.t 2,
    zvec_to_qvec d_integer_pair index ==
      inject_Z (Z.pos 1%positive) *
        zvec_to_qvec d_integer_pair index.
Proof. intro index. ring. Qed.

Example concrete_inner_nonnegative_preserved : forall value : QVec 2,
    0 <= qinner d_half_minus_three_fourths value <->
    0 <= qinner (zvec_to_qvec d_integer_pair) value.
Proof.
  apply (qnormal_integer_nonnegative_iff 2 d_half_minus_three_fourths
    d_integer_pair 4%positive d_pair_cleared_by_four).
Qed.

Example dimension_zero_normal_clearing : forall normal : QVec 0,
    exists (multiplier : positive) (integer_normal : ZVec 0),
      forall index : Fin.t 0,
        zvec_to_qvec integer_normal index ==
          inject_Z (Z.pos multiplier) * normal index.
Proof. apply qnormal_clear_denominators. Qed.

Example mixed_denominators_and_signs :
    exists (multiplier : positive) (integer_normal : ZVec 2),
      forall index : Fin.t 2,
        zvec_to_qvec integer_normal index ==
          inject_Z (Z.pos multiplier) *
            d_pair (Qmake (-5) 3%positive) (Qmake 7 2%positive) index.
Proof. apply qnormal_clear_denominators. Qed.

Definition d_denominators_two_three_four : QVec 3 :=
  fun index => Fin.caseS' index (fun _ => Q) (Qmake 1 2%positive)
    (fun tail => Fin.caseS' tail (fun _ => Q) (Qmake (-2) 3%positive)
      (fun _ => Qmake 2 4%positive)).

Example denominators_two_three_four_and_nonnormalized :
    exists (multiplier : positive) (integer_normal : ZVec 3),
      forall index : Fin.t 3,
        zvec_to_qvec integer_normal index ==
          inject_Z (Z.pos multiplier) *
            d_denominators_two_three_four index.
Proof. apply qnormal_clear_denominators. Qed.

Example empty_normal_list_is_full_space :
    exists integer_normals : list (ZVec 2),
      forall value : QVec 2,
        (forall normal, List.In normal [] -> 0 <= qinner normal value) <->
        (forall normal, List.In normal integer_normals ->
          0 <= qinner (zvec_to_qvec normal) value).
Proof. apply qnormal_list_integer_hrep. Qed.

Example zero_and_duplicate_normals :
    exists integer_normals : list (ZVec 2),
      forall value : QVec 2,
        (forall normal,
          List.In normal [d_pair 0 0; d_half_minus_three_fourths;
            d_half_minus_three_fourths] ->
          0 <= qinner normal value) <->
        (forall normal, List.In normal integer_normals ->
          0 <= qinner (zvec_to_qvec normal) value).
Proof. apply qnormal_list_integer_hrep. Qed.

Lemma generated_cone_integer_hrep : forall d (generators : list (QVec d)),
    exists normals : list (ZVec d),
      forall value : QVec d,
        qcone_generated generators value <->
        forall normal, List.In normal normals ->
          0 <= qinner (zvec_to_qvec normal) value.
Proof.
  intros d generators. apply polyhedral_cone_integer_hrep.
  apply qcone_generated_is_rational_polyhedral_cone.
Qed.

Example zero_dimensional_cone_integer_hrep :=
  generated_cone_integer_hrep 0 ([] : list (QVec 0)).

Example empty_generators_zero_cone_integer_hrep :=
  generated_cone_integer_hrep 2 ([] : list (QVec 2)).

Example positive_ray_integer_hrep :=
  generated_cone_integer_hrep 1
    [fun _ => (1 : Q)].

Example negative_ray_integer_hrep :=
  generated_cone_integer_hrep 1
    [fun _ => (-1 : Q)].

Example lineality_integer_hrep :=
  generated_cone_integer_hrep 1
    [fun _ => (1 : Q); fun _ => (-1 : Q)].

Example low_rank_redundant_integer_hrep :=
  generated_cone_integer_hrep 2
    [d_pair 1 0; d_pair 2 0; d_pair 1 0].

Lemma low_rank_ray_excludes_transverse :
    ~ qcone_generated [d_pair 1 0] (d_pair 0 1).
Proof.
  intro Hcone.
  apply qcone_generated_aligned_coefficients in Hcone as
    [coefficients [Hlength [_ Hvalue]]].
  destruct coefficients as [|coefficient [|extra coefficients]];
    simpl in Hlength; try discriminate.
  specialize (Hvalue (Fin.FS Fin.F1)).
  unfold d_pair, qlinear_combination, qvec_add, qvec_scale, qvec_zero
    in Hvalue.
  unfold Qeq in Hvalue. cbn in Hvalue. lia.
Qed.

Example low_rank_integer_hrep_excludes_transverse :
    exists normals : list (ZVec 2),
      (forall value : QVec 2,
        qcone_generated [d_pair 1 0] value <->
        forall normal, List.In normal normals ->
          0 <= qinner (zvec_to_qvec normal) value) /\
      ~ (forall normal, List.In normal normals ->
          0 <= qinner (zvec_to_qvec normal) (d_pair 0 1)).
Proof.
  destruct (generated_cone_integer_hrep 2 [d_pair 1 0]) as
    [normals Hnormals].
  exists normals. split; [exact Hnormals|].
  intro Hall. apply low_rank_ray_excludes_transverse.
  apply (proj2 (Hnormals (d_pair 0 1))). exact Hall.
Qed.

Example nonnegative_orthant_integer_hrep :=
  generated_cone_integer_hrep 2
    [d_pair 1 0; d_pair 0 1].

Print Assumptions qnormal_clear_denominators.
Print Assumptions qnormal_integer_inner.
Print Assumptions qnormal_integer_nonnegative_iff.
Print Assumptions qnormal_list_integer_hrep.
Print Assumptions polyhedral_cone_integer_hrep.
