From Coq Require Import List Vector ZArith QArith Lia.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge Periodic RationalHToV.
From Mell.Order Require Import PeriodicOrder.
From Mell.Geometry Require Import LatticeGordanH.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Set Printing Implicit.
Check @ZGroupGenerated.
Check @pulled_constraints_iff.
Check @project_group_solution_constraints.
Check @weighted_sum_project_group_generated.
Check @lattice_gordan_hmatrix.

Definition zvector0 : ZVec 0 := @Vector.nil Z.
Definition qmatrix0 : QMatrix 0 0 := @Vector.nil (Vector.t Q 0).

Example lattice_gordan_dimension_zero :
  FinitelyGeneratedPeriodic
    (fun value : ZVec 0 =>
      ZGroupGenerated [] value /\
      HConicalConstraints qmatrix0 (zvec_to_qvec value)).
Proof. apply lattice_gordan_hmatrix. Qed.

Definition zvector1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition qrow1 (coefficient : Q) : Vector.t Q 1 :=
  @Vector.cons Q coefficient 0 (@Vector.nil Q).

Definition qmatrix1 (coefficient : Q) : QMatrix 1 1 :=
  @Vector.cons (Vector.t Q 1) (qrow1 coefficient) 0
    (@Vector.nil (Vector.t Q 1)).

Example lattice_gordan_integers_nonnegative :
  FinitelyGeneratedPeriodic
    (fun value : ZVec 1 =>
      ZGroupGenerated [zvector1 1] value /\
      HConicalConstraints (qmatrix1 1) (zvec_to_qvec value)).
Proof. apply lattice_gordan_hmatrix. Qed.

Example lattice_gordan_even_nonnegative :
  FinitelyGeneratedPeriodic
    (fun value : ZVec 1 =>
      ZGroupGenerated [zvector1 2] value /\
      HConicalConstraints (qmatrix1 1) (zvec_to_qvec value)).
Proof. apply lattice_gordan_hmatrix. Qed.

Example lattice_gordan_integers_nonpositive :
  FinitelyGeneratedPeriodic
    (fun value : ZVec 1 =>
      ZGroupGenerated [zvector1 1] value /\
      HConicalConstraints (qmatrix1 (-1)) (zvec_to_qvec value)).
Proof. apply lattice_gordan_hmatrix. Qed.

Definition zvector2 (left right : Z) : ZVec 2 :=
  @Vector.cons Z left 1
    (@Vector.cons Z right 0 (@Vector.nil Z)).

Definition qrow2 (left right : Q) : Vector.t Q 2 :=
  @Vector.cons Q left 1
    (@Vector.cons Q right 0 (@Vector.nil Q)).

Definition orthant_matrix : QMatrix 2 2 :=
  @Vector.cons (Vector.t Q 2) (qrow2 1 0) 1
    (@Vector.cons (Vector.t Q 2) (qrow2 0 1) 0
      (@Vector.nil (Vector.t Q 2))).

Example lattice_gordan_low_rank_diagonal :
  FinitelyGeneratedPeriodic
    (fun value : ZVec 2 =>
      ZGroupGenerated [zvector2 1 1] value /\
      HConicalConstraints orthant_matrix (zvec_to_qvec value)).
Proof. apply lattice_gordan_hmatrix. Qed.

Definition lineality_matrix : QMatrix 1 2 :=
  @Vector.cons (Vector.t Q 2) (qrow2 0 1) 0
    (@Vector.nil (Vector.t Q 2)).

Example lattice_gordan_lineality :
  FinitelyGeneratedPeriodic
    (fun value : ZVec 2 =>
      ZGroupGenerated [zvector2 1 0; zvector2 0 1] value /\
      HConicalConstraints lineality_matrix (zvec_to_qvec value)).
Proof. apply lattice_gordan_hmatrix. Qed.

Definition redundant_matrix : QMatrix 3 1 :=
  @Vector.cons (Vector.t Q 1) (qrow1 1) 2
    (@Vector.cons (Vector.t Q 1) (qrow1 1) 1
      (@Vector.cons (Vector.t Q 1) (qrow1 0) 0
        (@Vector.nil (Vector.t Q 1)))).

Example lattice_gordan_redundant_data :
  FinitelyGeneratedPeriodic
    (fun value : ZVec 1 =>
      ZGroupGenerated [zvector1 1; zvector1 1; zvector1 0] value /\
      HConicalConstraints redundant_matrix (zvec_to_qvec value)).
Proof. apply lattice_gordan_hmatrix. Qed.

Definition nonnormalized_one : Q := Qmake 2 2%positive.

Example lattice_gordan_nonnormalized_rational :
  FinitelyGeneratedPeriodic
    (fun value : ZVec 1 =>
      ZGroupGenerated [zvector1 1] value /\
      HConicalConstraints (qmatrix1 nonnormalized_one)
        (zvec_to_qvec value)).
Proof. apply lattice_gordan_hmatrix. Qed.

Example signed_group_contains_negative_generator :
  ZGroupGenerated [zvector1 1] (zvector1 (-1)).
Proof.
  exists (@Vector.cons Z (-1)%Z 0 (@Vector.nil Z)).
  reflexivity.
Qed.

Example natural_monoid_does_not_contain_negative_generator :
  ~ zvec_generated [zvector1 1] (zvector1 (-1)).
Proof.
  intros [coefficients Hgenerated].
  refine (Vector.caseS' coefficients (fun coefficients =>
    zvec_linear_combination [zvector1 1] (Vector.to_list coefficients) =
      zvector1 (-1) -> False) _ Hgenerated).
  intros coefficient tail.
  refine (Vector.case0 (fun tail =>
    zvec_linear_combination [zvector1 1]
      (Vector.to_list (@Vector.cons nat coefficient 0 tail)) =
      zvector1 (-1) -> False) _ tail).
  intro Heq.
  change (zvec_add (zvec_nsmul coefficient (zvector1 1))
    (zvec_zero 1) = zvector1 (-1)) in Heq.
  rewrite zvec_add_zero_right in Heq.
  pose proof ((proj2 (Vector.eq_nth_iff Z 1 _ _) Heq)
    Fin.F1 Fin.F1 eq_refl) as Hcoordinate.
  rewrite nth_zvec_nsmul in Hcoordinate. cbn in Hcoordinate. lia.
Qed.

Check @lattice_gordan_hmatrix.
Print Assumptions pulled_constraints_iff.
Print Assumptions project_group_solution_constraints.
Print Assumptions weighted_sum_project_group_generated.
Print Assumptions lattice_gordan_hmatrix.
