From Coq Require Import List Vector ZArith Lia.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation Formula LinearEquations QuantifierFree.
From MiniCooper Require Import Theory.

Import ListNotations.
Open Scope Z_scope.

Module MC := MiniCooper.Theory.

Set Printing Implicit.

Check qf_semicode.
Check branch_semicode.
Check project_semicode_correct.
Check branch_equations_correct.
Check signed_dnf_correct.

Definition qf_zero : NVec 0 := @Vector.nil nat.

Example qf_true_dnf :
    dnf_semantics (fun _ => 0) (nat_environment qf_zero)
      (formula_dnf MC.FTrue).
Proof.
  unfold formula_dnf, dnf_semantics, branch_semantics. cbn [positive_dnf].
  exists []. split; [now left|constructor].
Qed.

Example qf_false_dnf :
    ~ dnf_semantics (fun _ => 0) (nat_environment qf_zero)
      (formula_dnf MC.FFalse).
Proof.
  unfold formula_dnf, dnf_semantics. cbn [positive_dnf].
  intros [branch [Hin _]]. inversion Hin.
Qed.

Example qf_zero_divisor_negative :
    dnf_semantics (fun _ => 0) (nat_environment qf_zero)
      (negative_atom_dnf (MC.Dv 0) (MC.TConstant (MiniCooper.Constant.CGround 3))).
Proof.
  apply (proj2 (primitive_neg_div_correct (fun _ => 0)
    (nat_environment qf_zero) 0
    (MC.TConstant (MiniCooper.Constant.CGround 3)))).
  cbn. intros [quotient Heq]. lia.
Qed.

Example qf_negative_divisor_remainder :
    dnf_semantics (fun _ => 0) (nat_environment qf_zero)
      (negative_atom_dnf (MC.Dv (-3))
        (MC.TConstant (MiniCooper.Constant.CGround 5))).
Proof.
  apply (proj2 (primitive_neg_div_correct (fun _ => 0)
    (nat_environment qf_zero) (-3)
    (MC.TConstant (MiniCooper.Constant.CGround 5)))).
  cbn. intros [quotient Heq]. lia.
Qed.

Definition qf_repeated_negative_term : MC.term :=
  MC.TSummand (-2) 0
    (MC.TSummand 3 0 (MC.TConstant (MiniCooper.Constant.CGround (-1)))).

Definition qf_zero_value : NVec 1 :=
  @Vector.cons nat 0%nat 0 (@Vector.nil nat).

Example qf_repeated_term_is_negative :
    MC.interpret_term (fun _ => 0) (nat_environment qf_zero_value)
      qf_repeated_negative_term = -1.
Proof. reflexivity. Qed.

Example qf_negative_term_divisible_by_one :
    primitive_semantics (fun _ => 0) (nat_environment qf_zero_value)
      (PrimDiv 1 qf_repeated_negative_term).
Proof. cbn [primitive_semantics qf_repeated_negative_term nat_environment].
  exists (-1). reflexivity.
Qed.

Example qf_negative_term_divisible_by_minus_one :
    primitive_semantics (fun _ => 0) (nat_environment qf_zero_value)
      (PrimDiv (-1) qf_repeated_negative_term).
Proof. cbn [primitive_semantics qf_repeated_negative_term nat_environment].
  exists 1. reflexivity.
Qed.

Definition qf_abstract_environment : MC.environment :=
  fun index => if Nat.eqb index 4 then 7 else 0.

Definition qf_abstract_formula : MC.formula :=
  MC.FAtom MC.Lt
    (MC.TConstant (MiniCooper.Constant.CAbstract 4)).

Example qf_abstract_constant_nonzero :
    MC.interpret_formula qf_abstract_environment (nat_environment qf_zero)
      qf_abstract_formula.
Proof. reflexivity. Qed.

Example qf_abstract_constant_semicode :
    exists code : SemiCode 0,
      forall value : NVec 0,
        MC.interpret_formula qf_abstract_environment (nat_environment value)
          qf_abstract_formula <-> denote code value.
Proof.
  apply qf_semicode. unfold qf_abstract_formula, qf_well_scoped.
  repeat constructor.
Qed.

Definition qf_edge_formula : MC.formula :=
  MC.FAnd
    (MC.FNot (MC.FAtom MC.Eq qf_repeated_negative_term))
    (MC.FAnd
      (MC.FNot (MC.FAtom MC.Lt qf_repeated_negative_term))
      (MC.FAnd
        (MC.FAtom (MC.Dv 0) qf_repeated_negative_term)
        (MC.FNot (MC.FAtom (MC.Dv (-3)) qf_repeated_negative_term)))).

Example qf_edge_formula_scoped : qf_well_scoped 1 qf_edge_formula.
Proof.
  unfold qf_edge_formula, qf_well_scoped, qf_repeated_negative_term.
  repeat constructor; lia.
Qed.

Example qf_edge_formula_semicode :
    exists code : SemiCode 1,
      forall value : NVec 1,
        MC.interpret_formula (fun _ => 0) (nat_environment value) qf_edge_formula
        <-> denote code value.
Proof. apply qf_semicode. exact qf_edge_formula_scoped. Qed.

Definition qf_dimension_zero_formula : MC.formula :=
  MC.FOr MC.FFalse
    (MC.FAnd MC.FTrue
      (MC.FNot (MC.FAtom (MC.Dv 2)
        (MC.TConstant (MiniCooper.Constant.CGround 1))))).

Example qf_dimension_zero_semicode :
    exists code : SemiCode 0,
      forall value : NVec 0,
        MC.interpret_formula (fun _ => 0) (nat_environment value)
          qf_dimension_zero_formula <-> denote code value.
Proof.
  apply qf_semicode. unfold qf_dimension_zero_formula, qf_well_scoped.
  repeat constructor.
Qed.

Example qf_empty_branch_semicode :
    exists code : SemiCode 0,
      forall value : NVec 0,
        branch_semantics (fun _ => 0) (nat_environment value) [] <->
        denote code value.
Proof. apply branch_semicode. constructor. Qed.

Definition qf_divisor_signs_formula : MC.formula :=
  MC.FOr
    (MC.FAtom (MC.Dv 2) (MC.TConstant (MiniCooper.Constant.CGround 6)))
    (MC.FOr
      (MC.FAtom (MC.Dv (-3)) (MC.TConstant (MiniCooper.Constant.CGround 6)))
      (MC.FAtom (MC.Dv 0) (MC.TConstant (MiniCooper.Constant.CGround 0)))).

Example qf_divisor_signs_semicode :
    exists code : SemiCode 0,
      forall value : NVec 0,
        MC.interpret_formula (fun _ => 0) (nat_environment value)
          qf_divisor_signs_formula <-> denote code value.
Proof.
  apply qf_semicode. unfold qf_divisor_signs_formula, qf_well_scoped.
  repeat constructor.
Qed.

Print Assumptions qf_semicode.
Print Assumptions branch_semicode.
Print Assumptions project_semicode_correct.
Print Assumptions branch_equations_correct.
Print Assumptions signed_dnf_correct.
Print Assumptions linear_solutions_finite_basis.
Print Assumptions homogeneous_solutions_finitely_generated.
