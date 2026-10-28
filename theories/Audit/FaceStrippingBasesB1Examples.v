From Coq Require Import Fin Lia List Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import FaceStrippingBases FaceStrippingExtract
  LatticeGordanH LatticeGordanInterface MathCompBridge Periodic QConeCore.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.

Check @zinner.
Check @AffineSolutions.
Check @HomogeneousSolutions.
Check @AffineGroupSolutions.
Check @HomogeneousGroupSolutions.
Check @affine_homogenized_solution_exact.
Check @linear_solution_projects_affine.
Check @homogeneous_solution_projects.
Check @affine_solution_lift.
Check @integer_affine_inequalities_finitary.
Check @pull_integer_normal.
Check @zinner_pull_integer_normal.
Check @affine_solutions_pull_iff.
Check @homogeneous_solutions_pull_iff.
Check @homogeneous_solutions_periodic.
Check @homogeneous_group_solutions_periodic.
Check @affine_group_inequalities_finitary.

Definition b1_zv1 (value : Z) : ZVec 1 := Vector.of_list [value].
Definition b1_zv2 (left right : Z) : ZVec 2 :=
  Vector.of_list [left; right].

Definition b1_ge_one : list (ZVec 1 * Z) := [(b1_zv1 1, 1)].
Definition b1_signed : list (ZVec 1 * Z) := [(b1_zv1 1, -2)].
Definition b1_equal_two : list (ZVec 1 * Z) :=
  [(b1_zv1 1, 2); (b1_zv1 (-1), -2)].
Definition b1_impossible : list (ZVec 1 * Z) := [(b1_zv1 0, 1)].
Definition b1_always : list (ZVec 1 * Z) := [(b1_zv1 0, -1)].
Definition b1_homogeneous_zero : list (ZVec 1 * Z) :=
  [(b1_zv1 1, 0); (b1_zv1 (-1), 0)].

Example dimension_zero_affine_basis :
    exists bases : list (ZVec 0),
      List.Forall (AffineSolutions ([] : list (ZVec 0 * Z))) bases /\
      SameSet (AffineSolutions [])
        (fun value => exists base homogeneous,
          List.In base bases /\ HomogeneousSolutions [] homogeneous /\
          value = zvec_add base homogeneous).
Proof. apply integer_affine_inequalities_finitary. Qed.

Example empty_constraints_affine_basis :=
  integer_affine_inequalities_finitary 1
    ([] : list (ZVec 1 * Z)).

Example signed_integer_solutions_affine_basis :=
  integer_affine_inequalities_finitary 1 b1_signed.

Example equality_as_two_inequalities_affine_basis :=
  integer_affine_inequalities_finitary 1 b1_equal_two.

Example zero_normal_always_affine_basis :=
  integer_affine_inequalities_finitary 1 b1_always.

Lemma negative_threshold_accepts_signed_value :
    AffineSolutions b1_signed (b1_zv1 (-1)).
Proof.
  intros constraint [Heq | Hin]; [subst constraint|inversion Hin].
  unfold b1_signed, b1_zv1, zinner. cbn. lia.
Qed.

Lemma positive_threshold_accepts_two :
    AffineSolutions b1_ge_one (b1_zv1 2).
Proof.
  intros constraint [Heq | Hin]; [subst constraint|inversion Hin].
  unfold b1_ge_one, b1_zv1, zinner. cbn. lia.
Qed.

Lemma empty_affine_constraints_accept_all : forall value : ZVec 2,
    AffineSolutions ([] : list (ZVec 2 * Z)) value.
Proof. intros value constraint Hin. inversion Hin. Qed.

Lemma zero_normal_negative_threshold_accepts_all : forall value : ZVec 1,
    AffineSolutions b1_always value.
Proof.
  intros value constraint [Heq | Hin]; [subst constraint|inversion Hin].
  unfold b1_always, b1_zv1, zinner. cbn. lia.
Qed.

Lemma paired_inequalities_accept_equality :
    AffineSolutions b1_equal_two (b1_zv1 2).
Proof.
  intros constraint [Heq | [Heq | Hin]].
  - subst constraint. unfold b1_equal_two, b1_zv1, zinner. cbn. lia.
  - subst constraint. unfold b1_equal_two, b1_zv1, zinner. cbn. lia.
  - inversion Hin.
Qed.

Example homogeneous_zero_is_periodic :
    Periodic (HomogeneousSolutions b1_homogeneous_zero).
Proof. apply homogeneous_solutions_periodic. Qed.

Example homogeneous_full_lattice_is_periodic :
    Periodic (HomogeneousSolutions ([] : list (ZVec 2 * Z))).
Proof. apply homogeneous_solutions_periodic. Qed.

Lemma homogeneous_zero_is_only_zero : forall value : ZVec 1,
    HomogeneousSolutions b1_homogeneous_zero value ->
    value = b1_zv1 0.
Proof.
  intro value. refine (Vector.caseS' value (fun value =>
    HomogeneousSolutions b1_homogeneous_zero value ->
      value = b1_zv1 0) _).
  intros head tail.
  refine (Vector.case0 (fun tail =>
    HomogeneousSolutions b1_homogeneous_zero
        (@Vector.cons Z head 0 tail) ->
      @Vector.cons Z head 0 tail = b1_zv1 0) _ tail).
  intro H.
  specialize (H (b1_zv1 1, 0) ltac:(now left)) as Hpositive.
  specialize (H (b1_zv1 (-1), 0) ltac:(now right; left)) as Hnegative.
  unfold b1_zv1, zinner in Hpositive, Hnegative |- *. cbn in *.
  f_equal. destruct head; cbn in *; try reflexivity; lia.
Qed.

Lemma empty_homogeneous_constraints_accept_all : forall value : ZVec 2,
    HomogeneousSolutions ([] : list (ZVec 2 * Z)) value.
Proof. intros value constraint Hin. inversion Hin. Qed.

Lemma impossible_has_no_solution : forall value : ZVec 1,
    ~ AffineSolutions b1_impossible value.
Proof.
  intros value H.
  specialize (H (b1_zv1 0, 1) ltac:(now left)).
  unfold b1_zv1, zinner in H. cbn in H. lia.
Qed.

Example contradictory_constraints_have_empty_basis :
    exists bases : list (ZVec 1),
      bases = [] /\
      SameSet (AffineSolutions b1_impossible)
        (fun value => exists base homogeneous,
          List.In base bases /\
          HomogeneousSolutions b1_impossible homogeneous /\
          value = zvec_add base homogeneous).
Proof.
  destruct (integer_affine_inequalities_finitary 1 b1_impossible) as
    [bases [Hbases Hcover]].
  destruct bases as [|base bases].
  - exists []. split; [reflexivity|exact Hcover].
  - inversion Hbases as [|base' bases' Hbase Htail]; subst.
    exfalso. exact (impossible_has_no_solution base Hbase).
Qed.

Definition b1_zero_group : ZSet 1 := ZGroupGenerated ([] : list (ZVec 1)).
Definition b1_all_group : ZSet 1 := ZGroupGenerated [b1_zv1 1].
Definition b1_even_group : ZSet 1 := ZGroupGenerated [b1_zv1 2].
Definition b1_low_rank_group : ZSet 2 := ZGroupGenerated [b1_zv2 1 0].
Definition b1_duplicate_group : ZSet 2 :=
  ZGroupGenerated [b1_zv2 1 0; b1_zv2 0 1; b1_zv2 1 0].

Example zero_group_affine_basis :
    FinitaryQCylindric
      (HomogeneousGroupSolutions b1_zero_group b1_ge_one)
      (AffineGroupSolutions b1_zero_group b1_ge_one).
Proof.
  apply affine_group_inequalities_finitary.
  apply zgroup_generated_is_finitely_generated_group.
Qed.

Example full_group_affine_basis :
    FinitaryQCylindric
      (HomogeneousGroupSolutions b1_all_group b1_ge_one)
      (AffineGroupSolutions b1_all_group b1_ge_one).
Proof.
  apply affine_group_inequalities_finitary.
  apply zgroup_generated_is_finitely_generated_group.
Qed.

Example even_group_affine_basis :
    FinitaryQCylindric
      (HomogeneousGroupSolutions b1_even_group b1_ge_one)
      (AffineGroupSolutions b1_even_group b1_ge_one).
Proof.
  apply affine_group_inequalities_finitary.
  apply zgroup_generated_is_finitely_generated_group.
Qed.

Lemma one_not_in_even_group : ~ b1_even_group (b1_zv1 1).
Proof.
  intros [coefficients Hcoefficients].
  refine (Vector.caseS' coefficients (fun coefficients =>
    zgroup_combination [b1_zv1 2] coefficients = b1_zv1 1 -> False) _
    Hcoefficients).
  intros coefficient tail.
  refine (Vector.case0 (fun tail =>
    zgroup_combination [b1_zv1 2] (@Vector.cons Z coefficient 0 tail) =
      b1_zv1 1 -> False) _ tail).
  intro Heq.
  pose proof (f_equal (fun value => Vector.nth value Fin.F1) Heq) as Hnth.
  unfold b1_zv1, zgroup_combination, zvec_add, zvec_zsmul, zvec_zero in Hnth.
  cbn in Hnth. lia.
Qed.

Lemma one_satisfies_unrestricted_inequality :
    AffineSolutions b1_ge_one (b1_zv1 1).
Proof.
  intros constraint [Heq | Hin]; [subst constraint|inversion Hin].
  unfold b1_ge_one, b1_zv1, zinner. cbn. lia.
Qed.

Example even_group_does_not_reuse_unrestricted_point :
    ~ AffineGroupSolutions b1_even_group b1_ge_one (b1_zv1 1).
Proof. intros [Hgroup _]. exact (one_not_in_even_group Hgroup). Qed.

Lemma two_is_an_even_group_affine_solution :
    AffineGroupSolutions b1_even_group b1_ge_one (b1_zv1 2).
Proof.
  split.
  - exists (Vector.of_list [1%Z]). reflexivity.
  - apply positive_threshold_accepts_two.
Qed.

Example low_rank_group_affine_basis :
    FinitaryQCylindric
      (HomogeneousGroupSolutions b1_low_rank_group
        ([] : list (ZVec 2 * Z)))
      (AffineGroupSolutions b1_low_rank_group []).
Proof.
  apply affine_group_inequalities_finitary.
  apply zgroup_generated_is_finitely_generated_group.
Qed.

Example duplicate_generators_group_affine_basis :
    FinitaryQCylindric
      (HomogeneousGroupSolutions b1_duplicate_group
        ([] : list (ZVec 2 * Z)))
      (AffineGroupSolutions b1_duplicate_group []).
Proof.
  apply affine_group_inequalities_finitary.
  apply zgroup_generated_is_finitely_generated_group.
Qed.

Print Assumptions integer_affine_inequalities_finitary.
Print Assumptions affine_group_inequalities_finitary.
Print Assumptions homogeneous_solutions_periodic.
Print Assumptions homogeneous_group_solutions_periodic.
