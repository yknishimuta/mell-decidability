From Coq Require Import List Vector ZArith Lia.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.Order Require Import FiniteBasis.

Import ListNotations.

Set Printing Implicit.

Check homogeneous_solutions_finitely_generated.
Check linear_solutions_finite_basis.
Check linear_solution_decomposition.
Check linear_equations_semicode.

Definition a0l_nv1 (x : nat) : NVec 1 := Vector.of_list [x].
Definition a0l_nv2 (x y : nat) : NVec 2 := Vector.of_list [x; y].
Definition a0l_nv3 (x y z : nat) : NVec 3 := Vector.of_list [x; y; z].
Definition a0l_zv1 (x : Z) : ZVec 1 := Vector.of_list [x].

Definition a0l_matrix_1_1 (coefficient : Z) : ZMatrix 1 1 :=
  Vector.of_list [a0l_zv1 coefficient].

Definition a0l_zero_matrix_1_1 : ZMatrix 1 1 := a0l_matrix_1_1 0.
Definition a0l_identity_matrix_1_1 : ZMatrix 1 1 := a0l_matrix_1_1 1.
Definition a0l_negative_matrix_1_1 : ZMatrix 1 1 := a0l_matrix_1_1 (-1).

Example a0l_empty_solution_set : forall value,
    ~ LinearSolution a0l_zero_matrix_1_1 (a0l_zv1 1) value.
Proof.
  intros value Hsolution.
  apply (f_equal (fun vector => Vector.nth vector Fin.F1)) in Hsolution.
  vm_compute in Hsolution. discriminate.
Qed.

Example a0l_homogeneous_zero_only : forall value,
    HomogeneousSolution a0l_identity_matrix_1_1 value -> value = a0l_nv1 0.
Proof.
  intros value Hsolution.
  apply (f_equal (@Vector.hd Z 0)) in Hsolution.
  unfold HomogeneousSolution, LinearSolution, a0l_identity_matrix_1_1,
    a0l_matrix_1_1, matrix_apply, a0l_zv1, zvec_zero in Hsolution.
  cbn in Hsolution.
  assert (Hidentity : forall z : Z,
      (match z with 0%Z => 0%Z | Z.pos p => Z.pos p
       | Z.neg p => Z.neg p end) = z) by (intros []; reflexivity).
  rewrite Hidentity in Hsolution.
  assert (Hhead : Vector.hd value = 0) by lia.
  change (value = (@Vector.cons nat 0 0 (@Vector.nil nat))).
  rewrite (Vector.eta value), Hhead.
  f_equal.
  exact (Vector.case0 (fun tail => tail = @Vector.nil nat)
    eq_refl (Vector.tl value)).
Qed.

Definition a0l_matrix_1_0 : ZMatrix 1 0 :=
  Vector.of_list [@Vector.nil Z].

Example a0l_zero_dimension_solution :
    LinearSolution a0l_matrix_1_0 (a0l_zv1 0) (@Vector.nil nat).
Proof. reflexivity. Qed.

Definition a0l_matrix_0_2 : ZMatrix 0 2 := @Vector.nil (ZVec 2).

Example a0l_zero_equations_accept_all : forall value : NVec 2,
    LinearSolution a0l_matrix_0_2 (@Vector.nil Z) value.
Proof. reflexivity. Qed.

Example a0l_negative_coefficient_solution :
    LinearSolution a0l_negative_matrix_1_1 (a0l_zv1 (-2)) (a0l_nv1 2).
Proof. reflexivity. Qed.

Definition a0l_sum_matrix : ZMatrix 1 2 :=
  Vector.of_list [Vector.of_list [1%Z; 1%Z]].

Example a0l_multiple_inhomogeneous_candidates :
    LinearSolution a0l_sum_matrix (a0l_zv1 1) (a0l_nv2 1 0) /\
    LinearSolution a0l_sum_matrix (a0l_zv1 1) (a0l_nv2 0 1) /\
    ~ nvec_le (a0l_nv2 1 0) (a0l_nv2 0 1) /\
    ~ nvec_le (a0l_nv2 0 1) (a0l_nv2 1 0).
Proof.
  repeat split; try reflexivity.
  - intro Hle. specialize (Hle Fin.F1). vm_compute in Hle. lia.
  - intro Hle. specialize (Hle (Fin.FS Fin.F1)). vm_compute in Hle. lia.
Qed.

Definition a0l_two_generator_matrix : ZMatrix 1 3 :=
  Vector.of_list [Vector.of_list [1%Z; 1%Z; (-1)%Z]].

Example a0l_multiple_homogeneous_candidates :
    HomogeneousSolution a0l_two_generator_matrix (a0l_nv3 1 0 1) /\
    HomogeneousSolution a0l_two_generator_matrix (a0l_nv3 0 1 1) /\
    ~ nvec_le (a0l_nv3 1 0 1) (a0l_nv3 0 1 1) /\
    ~ nvec_le (a0l_nv3 0 1 1) (a0l_nv3 1 0 1).
Proof.
  repeat split; try reflexivity.
  - intro Hle. specialize (Hle Fin.F1). vm_compute in Hle. lia.
  - intro Hle. specialize (Hle (Fin.FS Fin.F1)). vm_compute in Hle. lia.
Qed.

Lemma a0l_generated_by_singleton : forall d (generator value : NVec d),
    GeneratedBy [generator] value ->
    exists coefficient, value = nvec_scale coefficient generator.
Proof.
  intros d generator value [coefficients Hsum].
  destruct coefficients as [|coefficient coefficients]; try discriminate.
  destruct coefficients; try discriminate. cbn in Hsum.
  inversion Hsum; subst value.
  exists coefficient. rewrite nvec_add_zero_right_local. reflexivity.
Qed.

Example a0l_two_generators_are_needed : forall generator : NVec 3,
    ~ (GeneratedBy [generator] (a0l_nv3 1 0 1) /\
       GeneratedBy [generator] (a0l_nv3 0 1 1)).
Proof.
  intros generator [Hleft Hright].
  destruct (a0l_generated_by_singleton 3 generator _ Hleft) as
    [left_coefficient Hleft_form].
  destruct (a0l_generated_by_singleton 3 generator _ Hright) as
    [right_coefficient Hright_form].
  pose proof (f_equal (fun value => Vector.nth value Fin.F1)
    Hleft_form) as Hleft_first.
  pose proof (f_equal (fun value => Vector.nth value (Fin.FS Fin.F1))
    Hleft_form) as Hleft_second.
  pose proof (f_equal (fun value => Vector.nth value Fin.F1)
    Hright_form) as Hright_first.
  pose proof (f_equal (fun value => Vector.nth value (Fin.FS Fin.F1))
    Hright_form) as Hright_second.
  unfold a0l_nv3, nvec_scale in
    Hleft_first, Hleft_second, Hright_first, Hright_second.
  rewrite (nth_map _ _ Fin.F1 Fin.F1 eq_refl) in Hleft_first.
  rewrite (nth_map _ _ Fin.F1 Fin.F1 eq_refl) in Hright_first.
  rewrite (nth_map _ _ (Fin.FS Fin.F1) (Fin.FS Fin.F1) eq_refl) in
    Hleft_second.
  rewrite (nth_map _ _ (Fin.FS Fin.F1) (Fin.FS Fin.F1) eq_refl) in
    Hright_second.
  cbn in Hleft_first, Hleft_second, Hright_first, Hright_second.
  nia.
Qed.

Example a0l_empty_solution_semicode_exists :
    exists code : SemiCode 1, forall value,
      LinearSolution a0l_zero_matrix_1_1 (a0l_zv1 1) value <->
      denote code value.
Proof. apply linear_equations_semicode. Qed.

Example a0l_zero_dimension_semicode_exists :
    exists code : SemiCode 0, forall value,
      LinearSolution a0l_matrix_1_0 (a0l_zv1 0) value <-> denote code value.
Proof. apply linear_equations_semicode. Qed.

Print Assumptions homogeneous_solutions_finitely_generated.
Print Assumptions linear_solutions_finite_basis.
Print Assumptions linear_solution_decomposition.
Print Assumptions linear_equations_semicode.
Print Assumptions homogeneous_difference.
Print Assumptions nvec_le_restricted_afs.
Print Assumptions a0l_homogeneous_zero_only.

Print Assumptions irun_le_finite_cover.
Print Assumptions context_order_finite_cover.
