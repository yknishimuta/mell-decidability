From Coq Require Import Fin Lia List QArith Permutation.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From Polyhedra Require Import polyhedron barycenter.
From Mell.Geometry Require Import MathCompBridge QConeCore LatticeGordanV
  QratVectorAdapter QratConeAdapter.

Import GRing.Theory ListNotations.
Set Printing Implicit.
Open Scope ring_scope.

Check @rat_fset_of_columns.
Check @rat_fset_of_generators.
Check @rat_fset_of_generators_member.
Check @rat_fset_of_generators_member_inv.
Check @rat_fset_of_generators_nil.
Check @rat_fset_of_generators_permutation.
Check @rat_fset_of_generators_duplicate.
Check @rat_fset_of_generators_qveceq_duplicate.

Check @rat_weight_of_lists.
Check @combine_rat_weight_of_lists.
Check @rat_coefficients_of_weight.
Check @rat_coefficients_of_weight_nonnegative.
Check @rat_linear_combination_coefficients_of_weight.
Check @rat_columns_polyhedra_cone.
Check @rat_to_q_coefficients_nonnegative.
Check @qcone_generated_polyhedra_cone.

Definition b_vec1 (value : Q) : QVec 1 := fun _ => value.
Definition b_one := b_vec1 (1 : Q).
Definition b_two := b_vec1 (2 : Q).
Definition b_minus_one := b_vec1 (-1 : Q).
Definition b_half := b_vec1 (Qmake 1 2%positive).
Definition b_two_fourths := b_vec1 (Qmake 2 4%positive).

Example finite_set_member :
    qvec_to_rat_col b_one \in rat_fset_of_generators [b_one; b_minus_one].
Proof. apply rat_fset_of_generators_member. now left. Qed.

Example finite_set_member_has_source : forall column,
    column \in rat_fset_of_generators [b_one; b_minus_one] ->
    exists source, List.In source [b_one; b_minus_one] /\
      column = qvec_to_rat_col source.
Proof. intros column. apply rat_fset_of_generators_member_inv. Qed.

Example empty_generators_are_empty :
    @rat_fset_of_generators 1 [] = fset0.
Proof. apply rat_fset_of_generators_nil. Qed.

Example duplicate_generators_collapse :
    rat_fset_of_generators [b_one; b_one] =
      rat_fset_of_generators [b_one].
Proof. apply rat_fset_of_generators_duplicate. Qed.

Example nonnormalized_generators_collapse :
    rat_fset_of_generators [b_half; b_two_fourths] =
      rat_fset_of_generators [b_half].
Proof.
  apply rat_fset_of_generators_qveceq_duplicate.
  intro index. unfold b_half, b_two_fourths, b_vec1. reflexivity.
Qed.

Example generator_order_irrelevant :
    rat_fset_of_generators [b_one; b_minus_one] =
      rat_fset_of_generators [b_minus_one; b_one].
Proof.
  apply rat_fset_of_generators_permutation.
  apply perm_swap.
Qed.

Example duplicate_coefficients_are_added :
    rat_weight_of_lists
      [qvec_to_rat_col b_one; qvec_to_rat_col b_one]
      [(1 : rat); (2 : rat)] (qvec_to_rat_col b_one) = (3 : rat).
Proof.
  cbn. rewrite !fsaddE !rat_single_weightE !eqxx !fs0E.
  by rewrite addr0.
Qed.

Example empty_cone_contains_zero :
    qvec_to_rat_col (qvec_zero 1) \in
      polyhedron.cone (rat_fset_of_generators []).
Proof.
  apply (proj1 (qcone_generated_polyhedra_cone [] (qvec_zero 1))).
  apply qcone_generated_zero.
Qed.

Example empty_cone_dimension_zero : forall value : QVec 0,
    qcone_generated [] value <->
    qvec_to_rat_col value \in
      polyhedron.cone (rat_fset_of_generators []).
Proof. apply qcone_generated_polyhedra_cone. Qed.

Example positive_ray_contains_one :
    qvec_to_rat_col b_one \in
      polyhedron.cone (rat_fset_of_generators [b_one]).
Proof.
  apply (proj1 (qcone_generated_polyhedra_cone [b_one] b_one)).
  apply qcone_generated_generator. now left.
Qed.

Example scaled_ray_contains_one :
    qvec_to_rat_col b_one \in
      polyhedron.cone (rat_fset_of_generators [b_two]).
Proof.
  apply (proj1 (qcone_generated_polyhedra_cone [b_two] b_one)).
  apply qcone_generated_aligned_coefficients.
  exists [Qmake 1 2%positive]. split; [reflexivity|]. split.
  - constructor; [unfold Qle; cbn; lia|constructor].
  - intro index. unfold b_one, b_two, b_vec1, qlinear_combination,
      qvec_add, qvec_scale, qvec_zero. cbn. ring.
Qed.

Example two_sided_ray_contains_negative :
    qvec_to_rat_col b_minus_one \in
      polyhedron.cone (rat_fset_of_generators [b_one; b_minus_one]).
Proof.
  apply (proj1 (qcone_generated_polyhedra_cone
    [b_one; b_minus_one] b_minus_one)).
  apply qcone_generated_generator. now right; left.
Qed.

Example positive_ray_excludes_negative :
    ~ qvec_to_rat_col b_minus_one \in
      polyhedron.cone (rat_fset_of_generators [b_one]).
Proof.
  intro Hmember.
  apply (proj2 (qcone_generated_polyhedra_cone [b_one] b_minus_one)) in Hmember.
  apply qcone_generated_aligned_coefficients in Hmember as
    [coefficients [Hlength [Hnonnegative Hvalue]]].
  destruct coefficients as [|coefficient [|extra coefficients]];
    simpl in Hlength; try discriminate.
  inversion Hnonnegative as [|? ? Hcoefficient _]; subst.
  specialize (Hvalue Fin.F1).
  unfold b_minus_one, b_one, b_vec1, qlinear_combination,
    qvec_add, qvec_scale, qvec_zero in Hvalue.
  unfold Qle in Hcoefficient. unfold Qeq in Hvalue.
  cbn in Hcoefficient, Hvalue.
  pose proof (Pos2Z.is_pos (Qden coefficient)). lia.
Qed.

Example lineality_membership_equivalence : forall value : QVec 1,
    qcone_generated [b_one; b_minus_one] value <->
    qvec_to_rat_col value \in
      polyhedron.cone (rat_fset_of_generators [b_one; b_minus_one]).
Proof. apply qcone_generated_polyhedra_cone. Qed.

Example dependent_redundant_membership_equivalence : forall value : QVec 1,
    qcone_generated [b_one; b_two; b_one] value <->
    qvec_to_rat_col value \in
      polyhedron.cone (rat_fset_of_generators [b_one; b_two; b_one]).
Proof. apply qcone_generated_polyhedra_cone. Qed.

Print Assumptions rat_fset_of_generators_member.
Print Assumptions rat_fset_of_generators_member_inv.
Print Assumptions rat_fset_of_generators_permutation.
Print Assumptions rat_fset_of_generators_duplicate.
Print Assumptions rat_fset_of_generators_qveceq_duplicate.
Print Assumptions combine_fsfun_add.
Print Assumptions rat_weight_of_lists_conic.
Print Assumptions rat_weight_of_lists_support.
Print Assumptions combine_rat_weight_of_lists.
Print Assumptions rat_coefficients_of_weight_nonnegative.
Print Assumptions rat_linear_combination_coefficients_of_weight.
Print Assumptions rat_columns_polyhedra_cone.
Print Assumptions rat_to_q_coefficients_nonnegative.
Print Assumptions q_to_rat_after_rat_to_q_list.
Print Assumptions qcone_generated_polyhedra_cone.
