From Coq Require Import Vector ZArith Lia.
From MiniCooper Require Import Constant Theory.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation QuantifierFree.
From Mell.Presburger Require Import Syntax Semantics QE NatSemilinear.

Open Scope Z_scope.

Module MC := MiniCooper.Theory.

Set Printing Implicit.

Check eliminate.
Check eliminate_correct.
Check eliminate_well_formed.
Check MC.qf_wff.
Check nat_environment_outside_zero.
Check zero_outside_term_scoped.
Check zero_outside_term_correct_on_nat_env.
Check zero_outside_scoped.
Check zero_outside_correct_on_nat_env.
Check eliminate_is_qf.
Check presburger_nat_semilinear.

Print eliminate.
Print nat_environment.
Print MC.extend.

Definition qe_zero : NVec 0 := @Vector.nil nat.

Definition qe_one (x : nat) : NVec 1 :=
  @Vector.cons nat x 0 (@Vector.nil nat).

Definition qe_two (x y : nat) : NVec 2 :=
  @Vector.cons nat x 1 (@Vector.cons nat y 0 (@Vector.nil nat)).

Example qe_nat_environment_dimension_zero : forall variable,
    nat_environment qe_zero variable = 0.
Proof. intros. apply nat_environment_outside_zero. lia. Qed.

Definition qe_raw_outside : MC.formula :=
  MC.FAtom MC.Eq
    (MC.TSummand (-3) 4 (MC.TConstant (CGround 0))).

Example qe_raw_outside_is_zeroed :
    zero_outside 2 qe_raw_outside =
      MC.FAtom MC.Eq (MC.TConstant (CGround 0)).
Proof. reflexivity. Qed.

Example qe_raw_outside_semantics_preserved : forall x y,
    MC.interpret_formula (fun _ => 0) (nat_environment (qe_two x y))
      qe_raw_outside <->
    MC.interpret_formula (fun _ => 0) (nat_environment (qe_two x y))
      (zero_outside 2 qe_raw_outside).
Proof.
  intros. apply zero_outside_correct_on_nat_env. repeat constructor.
Qed.

Definition qe_abstract_environment : MC.environment :=
  fun index => if Nat.eqb index 3 then 7 else 0.

Definition qe_raw_abstract : MC.formula :=
  MC.FAtom MC.Eq
    (MC.TSummand (-5) 6 (MC.TConstant (CAbstract 3))).

Example qe_abstract_constant_is_not_zeroed :
    zero_outside 2 qe_raw_abstract =
      MC.FAtom MC.Eq (MC.TConstant (CAbstract 3)).
Proof. reflexivity. Qed.

Example qe_abstract_constant_semantics_preserved : forall x y,
    MC.interpret_formula qe_abstract_environment (nat_environment (qe_two x y))
      qe_raw_abstract <->
    MC.interpret_formula qe_abstract_environment (nat_environment (qe_two x y))
      (zero_outside 2 qe_raw_abstract).
Proof.
  intros. apply zero_outside_correct_on_nat_env. repeat constructor.
Qed.

Definition qe_ordered_free_formula : Syntax.formula :=
  Syntax.Eq (Syntax.Plus (Syntax.Scale (-2) (Syntax.Var 0))
    (Syntax.Var 1)) (Syntax.Num 3).

Example qe_ordered_free_semantics : forall x y,
    formula_semantics (nat_environment (qe_two x y))
      qe_ordered_free_formula <->
    (-2) * Z.of_nat x + Z.of_nat y = 3.
Proof. intros; reflexivity. Qed.

Example qe_ordered_free_semicode :
    exists code : SemiCode 2,
      forall value : NVec 2,
        formula_semantics (nat_environment value) qe_ordered_free_formula <->
        denote code value.
Proof.
  exact (presburger_nat_semilinear 2 (fun _ => 0)
    qe_ordered_free_formula eq_refl).
Qed.

Definition qe_odd_formula : Syntax.formula :=
  Syntax.Exists
    (Syntax.Eq (Syntax.Var 1)
      (Syntax.Plus (Syntax.Scale 2 (Syntax.Var 0)) (Syntax.Num 1))).

Definition qe_even_formula : Syntax.formula :=
  Syntax.Exists
    (Syntax.Eq (Syntax.Var 1) (Syntax.Scale 2 (Syntax.Var 0))).

Example qe_odd_semantics : forall x,
    formula_semantics (nat_environment (qe_one x)) qe_odd_formula <->
    exists z : Z, Z.of_nat x = 2 * z + 1.
Proof. intros; reflexivity. Qed.

Example qe_even_semantics : forall x,
    formula_semantics (nat_environment (qe_one x)) qe_even_formula <->
    exists z : Z, Z.of_nat x = 2 * z.
Proof. intros; reflexivity. Qed.

Example qe_odd_semicode :
    exists code : SemiCode 1,
      forall value : NVec 1,
        formula_semantics (nat_environment value) qe_odd_formula <->
        denote code value.
Proof.
  exact (presburger_nat_semilinear 1 (fun _ => 0) qe_odd_formula eq_refl).
Qed.

Example qe_even_semicode :
    exists code : SemiCode 1,
      forall value : NVec 1,
        formula_semantics (nat_environment value) qe_even_formula <->
        denote code value.
Proof.
  exact (presburger_nat_semilinear 1 (fun _ => 0) qe_even_formula eq_refl).
Qed.

Definition qe_empty_formula : Syntax.formula :=
  Syntax.Exists
    (Syntax.ANd
      (Syntax.Eq (Syntax.Var 1) (Syntax.Scale 2 (Syntax.Var 0)))
      (Syntax.Lt (Syntax.Var 0) (Syntax.Num 0))).

Example qe_empty_semantics : forall x,
    ~ formula_semantics (nat_environment (qe_one x)) qe_empty_formula.
Proof.
  intro x.
  change (not (exists z : Z, Z.of_nat x = 2 * z /\ z < 0)).
  intros [z [Heq Hnegative]]. lia.
Qed.

Example qe_empty_semicode :
    exists code : SemiCode 1,
      forall value : NVec 1,
        formula_semantics (nat_environment value) qe_empty_formula <->
        denote code value.
Proof.
  exact (presburger_nat_semilinear 1 (fun _ => 0) qe_empty_formula eq_refl).
Qed.

Definition qe_nested_shadow_formula : Syntax.formula :=
  Syntax.Exists (Syntax.Exists
    (Syntax.Eq (Syntax.Var 2)
      (Syntax.Plus (Syntax.Var 1) (Syntax.Var 0)))).

Example qe_nested_shadow_semantics : forall x,
    formula_semantics (nat_environment (qe_one x)) qe_nested_shadow_formula <->
    exists outer inner : Z, Z.of_nat x = outer + inner.
Proof. intros; reflexivity. Qed.

Example qe_nested_shadow_semicode :
    exists code : SemiCode 1,
      forall value : NVec 1,
        formula_semantics (nat_environment value) qe_nested_shadow_formula <->
        denote code value.
Proof.
  exact (presburger_nat_semilinear 1 (fun _ => 0)
    qe_nested_shadow_formula eq_refl).
Qed.

Definition qe_closed_nested_formula : Syntax.formula :=
  Syntax.Exists (Syntax.Forall
    (Syntax.Exists (Syntax.Eq (Syntax.Var 0)
      (Syntax.Plus (Syntax.Var 1) (Syntax.Var 2))))).

Example qe_closed_nested_semicode :
    exists code : SemiCode 0,
      forall value : NVec 0,
        formula_semantics (nat_environment value) qe_closed_nested_formula <->
        denote code value.
Proof.
  exact (presburger_nat_semilinear 0 (fun _ => 0)
    qe_closed_nested_formula eq_refl).
Qed.

Print Assumptions presburger_nat_semilinear.
Print Assumptions nat_environment_outside_zero.
Print Assumptions zero_outside_term_scoped.
Print Assumptions zero_outside_term_correct_on_nat_env.
Print Assumptions zero_outside_scoped.
Print Assumptions zero_outside_correct_on_nat_env.
Print Assumptions eliminate_is_qf.
Print Assumptions eliminate_correct.
Print Assumptions eliminate_well_formed.
Print Assumptions qf_semicode.
