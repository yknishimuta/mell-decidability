From Mell.Presburger Require Import Syntax.
From Coq Require Import ZArith Bool Lia.

Open Scope Z_scope.

Definition environment := nat -> Z.

Definition empty_environment : environment := fun _ => 0.

Definition extend (env : environment) (value : Z) : environment :=
  fun x => match x with 0%nat => value | S x' => env x' end.

Fixpoint term_semantics (env : environment) (t : term) : Z :=
  match t with
  | Num value => value
  | Var x => env x
  | Plus lhs rhs => term_semantics env lhs + term_semantics env rhs
  | Neg body => - term_semantics env body
  | Scale coefficient body => coefficient * term_semantics env body
  end.

Fixpoint formula_semantics (env : environment) (f : formula) : Prop :=
  match f with
  | Bot => False
  | Top => True
  | Eq lhs rhs => term_semantics env lhs = term_semantics env rhs
  | Lt lhs rhs => term_semantics env lhs < term_semantics env rhs
  | Le lhs rhs => term_semantics env lhs <= term_semantics env rhs
  | ANd lhs rhs => formula_semantics env lhs /\ formula_semantics env rhs
  | Or lhs rhs => formula_semantics env lhs \/ formula_semantics env rhs
  | Not body => ~ formula_semantics env body
  | Exists body => exists value, formula_semantics (extend env value) body
  | Forall body => forall value, formula_semantics (extend env value) body
  end.

Definition sentence_semantics (s : sentence) : Prop :=
  formula_semantics empty_environment (sentence_formula s).

Definition agree_below
    (bound : nat) (left_env right_env : environment) : Prop :=
  forall x, (x < bound)%nat -> left_env x = right_env x.

Lemma term_closed_environment_independent :
  forall t bound left_env right_env,
    term_closed bound t = true ->
    agree_below bound left_env right_env ->
    term_semantics left_env t = term_semantics right_env t.
Proof.
  induction t; intros bound left_env right_env Hclosed Hagree; simpl in *.
  - reflexivity.
  - apply Nat.ltb_lt in Hclosed. apply Hagree. exact Hclosed.
  - apply Bool.andb_true_iff in Hclosed as [Hleft Hright].
    rewrite (IHt1 bound left_env right_env Hleft Hagree).
    rewrite (IHt2 bound left_env right_env Hright Hagree). reflexivity.
  - rewrite (IHt bound left_env right_env Hclosed Hagree). reflexivity.
  - rewrite (IHt bound left_env right_env Hclosed Hagree). reflexivity.
Qed.

Lemma extend_agree_below :
  forall bound left_env right_env value,
    agree_below bound left_env right_env ->
    agree_below (S bound) (extend left_env value) (extend right_env value).
Proof.
  intros bound left_env right_env value Hagree [|x] Hlt; simpl.
  - reflexivity.
  - apply Hagree. lia.
Qed.

Lemma formula_closed_environment_independent :
  forall f bound left_env right_env,
    formula_closed bound f = true ->
    agree_below bound left_env right_env ->
    (formula_semantics left_env f <-> formula_semantics right_env f).
Proof.
  induction f; intros bound left_env right_env Hclosed Hagree; simpl in *;
    try tauto.
  - apply Bool.andb_true_iff in Hclosed as [Hleft Hright].
    rewrite (term_closed_environment_independent t bound left_env right_env
      Hleft Hagree).
    rewrite (term_closed_environment_independent t0 bound left_env right_env
      Hright Hagree). reflexivity.
  - apply Bool.andb_true_iff in Hclosed as [Hleft Hright].
    rewrite (term_closed_environment_independent t bound left_env right_env
      Hleft Hagree).
    rewrite (term_closed_environment_independent t0 bound left_env right_env
      Hright Hagree). reflexivity.
  - apply Bool.andb_true_iff in Hclosed as [Hleft Hright].
    rewrite (term_closed_environment_independent t bound left_env right_env
      Hleft Hagree).
    rewrite (term_closed_environment_independent t0 bound left_env right_env
      Hright Hagree). reflexivity.
  - apply Bool.andb_true_iff in Hclosed as [Hleft Hright].
    rewrite (IHf1 bound left_env right_env Hleft Hagree).
    rewrite (IHf2 bound left_env right_env Hright Hagree). tauto.
  - apply Bool.andb_true_iff in Hclosed as [Hleft Hright].
    rewrite (IHf1 bound left_env right_env Hleft Hagree).
    rewrite (IHf2 bound left_env right_env Hright Hagree). tauto.
  - rewrite (IHf bound left_env right_env Hclosed Hagree). tauto.
  - split; intros [value Hvalue]; exists value.
    + pose proof (extend_agree_below bound left_env right_env value Hagree)
        as Hextended.
      apply (proj1 (IHf (S bound) (extend left_env value)
        (extend right_env value) Hclosed Hextended)). exact Hvalue.
    + pose proof (extend_agree_below bound left_env right_env value Hagree)
        as Hextended.
      apply (proj2 (IHf (S bound) (extend left_env value)
        (extend right_env value) Hclosed Hextended)). exact Hvalue.
  - split; intros Hall value.
    + pose proof (extend_agree_below bound left_env right_env value Hagree)
        as Hextended.
      apply (proj1 (IHf (S bound) (extend left_env value)
        (extend right_env value) Hclosed Hextended)). apply Hall.
    + pose proof (extend_agree_below bound left_env right_env value Hagree)
        as Hextended.
      apply (proj2 (IHf (S bound) (extend left_env value)
        (extend right_env value) Hclosed Hextended)). apply Hall.
Qed.

Theorem sentence_environment_independent :
  forall s env,
    formula_semantics env (sentence_formula s) <-> sentence_semantics s.
Proof.
  intros [f Hclosed] env. unfold sentence_semantics; simpl.
  apply formula_closed_environment_independent with (bound := 0%nat).
  - exact Hclosed.
  - intros x Hlt. lia.
Qed.
