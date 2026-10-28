From Coq Require Import List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore LatticeGordanH
  RationalHToV LatticeGordanInterface LatticeGordanMain.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.
Set Printing Implicit.

Check @F_Z_zero.
Check @F_Z_nsmul.
Check @F_Z_linear_combination_nat.
Check @zvec_generated_map_F_Z.
Check @finitely_generated_group_periodic.
Check @rational_polyhedral_integer_points_periodic.
Check @finitely_generated_group_cone_intersection_periodic.
Check @lattice_gordan.
Check lattice_gordan : lattice_gordan_contract.
Check @lattice_gordan_hmatrix.

Definition main_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition main_q1 (value : Q) : QVec 1 := fun _ => value.

Definition main_z2 (left right : Z) : ZVec 2 :=
  @Vector.cons Z left 1 (@Vector.cons Z right 0 (@Vector.nil Z)).

Definition main_q2 (left right : Q) : QVec 2 :=
  fun index => Fin.caseS' index (fun _ => Q) left (fun _ => right).

Example lattice_gordan_dimension_zero :
    FinitelyGeneratedPeriodic
      (fun value : ZVec 0 =>
        ZGroupGenerated [] value /\
        qcone_generated [] (zvec_to_qvec value)).
Proof.
  apply lattice_gordan.
  - apply zgroup_generated_is_finitely_generated_group.
  - apply qcone_generated_is_rational_polyhedral_cone.
Qed.

Example lattice_gordan_twoZ_nonnegative_ray :
    FinitelyGeneratedPeriodic
      (fun value : ZVec 1 =>
        ZGroupGenerated [main_z1 2] value /\
        qcone_generated [main_q1 1] (zvec_to_qvec value)).
Proof.
  apply lattice_gordan.
  - apply zgroup_generated_is_finitely_generated_group.
  - apply qcone_generated_is_rational_polyhedral_cone.
Qed.

Example lattice_gordan_Z2_nonnegative_orthant :
    FinitelyGeneratedPeriodic
      (fun value : ZVec 2 =>
        ZGroupGenerated [main_z2 1 0; main_z2 0 1] value /\
        qcone_generated [main_q2 1 0; main_q2 0 1]
          (zvec_to_qvec value)).
Proof.
  apply lattice_gordan.
  - apply zgroup_generated_is_finitely_generated_group.
  - apply qcone_generated_is_rational_polyhedral_cone.
Qed.

Example lattice_gordan_Z_full_lineality :
    FinitelyGeneratedPeriodic
      (fun value : ZVec 1 =>
        ZGroupGenerated [main_z1 1] value /\
        qcone_generated [main_q1 1; main_q1 (-1)]
          (zvec_to_qvec value)).
Proof.
  apply lattice_gordan.
  - apply zgroup_generated_is_finitely_generated_group.
  - apply qcone_generated_is_rational_polyhedral_cone.
Qed.

Example lattice_gordan_empty_cone_is_zero_cone :
    FinitelyGeneratedPeriodic
      (fun value : ZVec 1 =>
        ZGroupGenerated [main_z1 1] value /\
        qcone_generated [] (zvec_to_qvec value)).
Proof.
  apply lattice_gordan.
  - apply zgroup_generated_is_finitely_generated_group.
  - apply qcone_generated_is_rational_polyhedral_cone.
Qed.

Example lattice_gordan_low_rank_duplicate_group :
    FinitelyGeneratedPeriodic
      (fun value : ZVec 2 =>
        ZGroupGenerated [main_z2 1 0; main_z2 1 0] value /\
        qcone_generated [main_q2 1 0; main_q2 (-1) 0]
          (zvec_to_qvec value)).
Proof.
  apply lattice_gordan.
  - apply zgroup_generated_is_finitely_generated_group.
  - apply qcone_generated_is_rational_polyhedral_cone.
Qed.

Example lattice_gordan_zero_group :
    FinitelyGeneratedPeriodic
      (fun value : ZVec 1 =>
        ZGroupGenerated [] value /\
        qcone_generated [main_q1 1; main_q1 (-1)]
          (zvec_to_qvec value)).
Proof.
  apply lattice_gordan.
  - apply zgroup_generated_is_finitely_generated_group.
  - apply qcone_generated_is_rational_polyhedral_cone.
Qed.

Example lattice_gordan_hmatrix_regression : forall rows d
    (matrix : QMatrix rows d) (groups : list (ZVec d)),
    FinitelyGeneratedPeriodic
      (fun value : ZVec d =>
        ZGroupGenerated groups value /\
        HConicalConstraints matrix (zvec_to_qvec value)).
Proof.
  intros rows d matrix groups.
  apply (lattice_gordan_hmatrix d rows matrix groups).
Qed.

Example lattice_gordan_hmatrix_via_public_contract : forall rows d
    (matrix : QMatrix rows d) (groups : list (ZVec d)),
    FinitelyGeneratedPeriodic
      (fun value : ZVec d =>
        ZGroupGenerated groups value /\
        HConicalConstraints matrix (zvec_to_qvec value)).
Proof.
  intros rows d matrix groups. apply lattice_gordan.
  - apply zgroup_generated_is_finitely_generated_group.
  - apply rational_hcone_is_polyhedral.
Qed.

Print Assumptions lattice_gordan.
