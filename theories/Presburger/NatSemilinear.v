From Coq Require Import List Vector VectorSpec ZArith Bool Lia.
From MiniCooper Require Import Constant Theory.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation Formula QuantifierFree.
From Mell.Presburger Require Import Syntax Semantics QE.

Import ListNotations.
Open Scope Z_scope.

Module MC := MiniCooper.Theory.

Lemma nat_environment_outside_zero : forall d (value : NVec d) variable,
    (d <= variable)%nat -> nat_environment value variable = 0%Z.
Proof.
  intros d value variable Houtside.
  unfold nat_environment, vector_entry.
  rewrite List.nth_overflow.
  - reflexivity.
  - rewrite VectorSpec.length_to_list. exact Houtside.
Qed.

Fixpoint zero_outside_term (bound : nat) (term : MC.term) : MC.term :=
  match term with
  | MC.TSummand coefficient variable tail =>
      if Nat.ltb variable bound then
        MC.TSummand coefficient variable (zero_outside_term bound tail)
      else zero_outside_term bound tail
  | MC.TConstant constant => MC.TConstant constant
  end.

Fixpoint zero_outside (bound : nat) (formula : MC.formula) : MC.formula :=
  match formula with
  | MC.FAtom predicate term =>
      MC.FAtom predicate (zero_outside_term bound term)
  | MC.FFalse => MC.FFalse
  | MC.FTrue => MC.FTrue
  | MC.FAnd lhs rhs =>
      MC.FAnd (zero_outside bound lhs) (zero_outside bound rhs)
  | MC.FOr lhs rhs =>
      MC.FOr (zero_outside bound lhs) (zero_outside bound rhs)
  | MC.FNot body => MC.FNot (zero_outside bound body)
  | MC.FExists body => MC.FExists body
  end.

Lemma zero_outside_term_scoped : forall bound term,
    mc_term_scoped bound (zero_outside_term bound term).
Proof.
  intros bound term. induction term as [coefficient variable tail IH|constant].
  - cbn [zero_outside_term]. destruct (Nat.ltb variable bound) eqn:Hvariable.
    + split; [now apply Nat.ltb_lt|exact IH].
    + exact IH.
  - constructor.
Qed.

Lemma zero_outside_term_correct_on_nat_env :
  forall d cenv (value : NVec d) term,
    MC.interpret_term cenv (nat_environment value)
      (zero_outside_term d term) =
    MC.interpret_term cenv (nat_environment value) term.
Proof.
  intros d cenv value term.
  induction term as [coefficient variable tail IH|constant].
  - cbn [zero_outside_term].
    destruct (Nat.ltb variable d) eqn:Hvariable; cbn.
    + f_equal. exact IH.
    + apply Nat.ltb_ge in Hvariable.
      rewrite (nat_environment_outside_zero d value variable Hvariable).
      rewrite <- IH. ring.
  - reflexivity.
Qed.

Lemma zero_outside_scoped : forall d formula,
    MC.qf formula -> qf_well_scoped d (zero_outside d formula).
Proof.
  intros d formula Hqf. induction Hqf; cbn [zero_outside qf_well_scoped].
  - constructor. apply zero_outside_term_scoped.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma zero_outside_correct_on_nat_env : forall d cenv formula,
    MC.qf formula ->
    forall value : NVec d,
      (MC.interpret_formula cenv (nat_environment value) formula <->
       MC.interpret_formula cenv (nat_environment value)
         (zero_outside d formula)).
Proof.
  intros d cenv formula Hqf. induction Hqf; intro value;
    cbn [zero_outside MC.interpret_formula] in *.
  - now rewrite zero_outside_term_correct_on_nat_env.
  - tauto.
  - tauto.
  - rewrite IHHqf1, IHHqf2. reflexivity.
  - rewrite IHHqf1, IHHqf2. reflexivity.
  - rewrite IHHqf. reflexivity.
Qed.

Lemma eliminate_is_qf : forall formula, MC.qf (eliminate formula).
Proof.
  intro formula. apply MC.qf_wff, eliminate_well_formed.
Qed.

Theorem presburger_nat_semilinear :
  forall d (cenv : MC.environment) (formula : Syntax.formula),
    Syntax.formula_closed d formula = true ->
    exists code : SemiCode d,
      forall value : NVec d,
        formula_semantics (nat_environment value) formula <->
        denote code value.
Proof.
  intros d cenv formula _.
  pose proof (eliminate_is_qf formula) as Hqf.
  destruct (qf_semicode d cenv (zero_outside d (eliminate formula))
    (zero_outside_scoped d (eliminate formula) Hqf)) as [code Hcode].
  exists code. intro value.
  split.
  - intro Hformula. apply (proj1 (Hcode value)).
    apply (proj1 (zero_outside_correct_on_nat_env d cenv
      (eliminate formula) Hqf value)).
    apply (proj2 (eliminate_correct formula (nat_environment value) cenv)).
    exact Hformula.
  - intro Hdenote.
    apply (proj1 (eliminate_correct formula (nat_environment value) cenv)).
    apply (proj2 (zero_outside_correct_on_nat_env d cenv
      (eliminate formula) Hqf value)).
    apply (proj2 (Hcode value)). exact Hdenote.
Qed.
