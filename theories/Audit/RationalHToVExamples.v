From Coq Require Import Lia QArith Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore RationalHToV.

Open Scope Q_scope.

Definition qrow0 : Vector.t Q 0 := @Vector.nil Q.
Definition qmatrix_rows0_d0 : QMatrix 0 0 := @Vector.nil (Vector.t Q 0).

Definition qrow1 (coefficient : Q) : Vector.t Q 1 :=
  @Vector.cons Q coefficient 0 (@Vector.nil Q).

Definition qmatrix1 (coefficient : Q) : QMatrix 1 1 :=
  @Vector.cons (Vector.t Q 1) (qrow1 coefficient) 0
    (@Vector.nil (Vector.t Q 1)).

Definition qmatrix_rows0_d1 : QMatrix 0 1 :=
  @Vector.nil (Vector.t Q 1).

Definition qmatrix_zero_row : QMatrix 1 1 := qmatrix1 0.

Definition qmatrix_zero_cone : QMatrix 2 1 :=
  @Vector.cons (Vector.t Q 1) (qrow1 1) 1
    (@Vector.cons (Vector.t Q 1) (qrow1 (-1)) 0
      (@Vector.nil (Vector.t Q 1))).

Definition qrow2 (left right : Q) : Vector.t Q 2 :=
  @Vector.cons Q left 1 (@Vector.cons Q right 0 (@Vector.nil Q)).

Definition qmatrix_lineality : QMatrix 1 2 :=
  @Vector.cons (Vector.t Q 2) (qrow2 0 1) 0
    (@Vector.nil (Vector.t Q 2)).

Example c1_hl_dimension_zero :
  exists generators : list (QVec 0),
    forall point, HConicalConstraints qmatrix_rows0_d0 point <->
      qcone_generated generators point.
Proof. apply rational_hcone_finitely_generated. Qed.

Example c1_hl_empty_rows_are_unconstrained (point : QVec 1) :
  HConicalConstraints qmatrix_rows0_d1 point.
Proof. intros row. inversion row. Qed.

Example c1_hl_zero_row_accepts_every_point (point : QVec 1) :
  HConicalConstraints qmatrix_zero_row point.
Proof.
  intros row. refine (Fin.caseS' row (fun row =>
    0 <= qrow_apply (Vector.nth qmatrix_zero_row row) point) _ _).
  - cbn. unfold Qle. cbn. lia.
  - intro impossible. inversion impossible.
Qed.

Example c1_hl_nonnegative_ray :
  exists generators : list (QVec 1),
    forall point, HConicalConstraints (qmatrix1 1) point <->
      qcone_generated generators point.
Proof. apply rational_hcone_finitely_generated. Qed.

Example c1_hl_nonpositive_ray_negative_coefficient :
  exists generators : list (QVec 1),
    forall point, HConicalConstraints (qmatrix1 (-1)) point <->
      qcone_generated generators point.
Proof. apply rational_hcone_finitely_generated. Qed.

Example c1_hl_zero_cone_opposite_constraints :
  exists generators : list (QVec 1),
    forall point, HConicalConstraints qmatrix_zero_cone point <->
      qcone_generated generators point.
Proof. apply rational_hcone_finitely_generated. Qed.

Example c1_hl_lineality_halfspace :
  exists generators : list (QVec 2),
    forall point, HConicalConstraints qmatrix_lineality point <->
      qcone_generated generators point.
Proof. apply rational_hcone_finitely_generated. Qed.

Definition qmatrix_redundant : QMatrix 2 1 :=
  @Vector.cons (Vector.t Q 1) (qrow1 (2#2)) 1
    (@Vector.cons (Vector.t Q 1) (qrow1 1) 0
      (@Vector.nil (Vector.t Q 1))).

Example c1_hl_redundant_noncanonical_coefficients :
  exists generators : list (QVec 1),
    forall point, HConicalConstraints qmatrix_redundant point <->
      qcone_generated generators point.
Proof. apply rational_hcone_finitely_generated. Qed.

Check QVecEq.
Check qcone_generated.
Check IsCone.
Check QClosure.
Check TopologicallyClosed.
Check qmatrix_clear_denominators.
Check homogenized_solution_exact.
Check homogeneous_project_nonnegative.
Check rational_hcone_finitely_generated.

Set Printing Implicit.
Check @rational_hcone_finitely_generated.
Print Assumptions qdefinable_qvec_extensional.
Print Assumptions qmatrix_clear_denominators.
Print Assumptions homogenized_solution_exact.
Print Assumptions rational_hcone_finitely_generated.
