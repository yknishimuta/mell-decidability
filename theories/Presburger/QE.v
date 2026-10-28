From Mell.Presburger Require Import Syntax Semantics.
From MiniCooper Require Import Constant Theory.
From Coq Require Import ZArith Lia Classical_Prop.

Open Scope Z_scope.

Module MC := MiniCooper.Theory.

Definition backend_zero : MC.term := MC.TConstant (CGround 0).

Fixpoint compile_term (t : Syntax.term) : MC.term :=
  match t with
  | Syntax.Num value => MC.TConstant (CGround value)
  | Syntax.Var x => MC.TSummand 1 x backend_zero
  | Syntax.Plus lhs rhs => MC.add (compile_term lhs) (compile_term rhs)
  | Syntax.Neg body => MC.neg (compile_term body)
  | Syntax.Scale coefficient body => MC.mul coefficient (compile_term body)
  end.

Definition backend_eq (lhs rhs : MC.term) : MC.formula :=
  MC.FAtom MC.Eq (MC.sub rhs lhs).

Definition backend_lt (lhs rhs : MC.term) : MC.formula :=
  MC.FAtom MC.Lt (MC.sub rhs lhs).

Definition backend_le (lhs rhs : MC.term) : MC.formula :=
  MC.FNot (backend_lt rhs lhs).

Fixpoint compile_formula (f : Syntax.formula) : MC.formula :=
  match f with
  | Syntax.Bot => MC.FFalse
  | Syntax.Top => MC.FTrue
  | Syntax.Eq lhs rhs => backend_eq (compile_term lhs) (compile_term rhs)
  | Syntax.Lt lhs rhs => backend_lt (compile_term lhs) (compile_term rhs)
  | Syntax.Le lhs rhs => backend_le (compile_term lhs) (compile_term rhs)
  | Syntax.ANd lhs rhs => MC.FAnd (compile_formula lhs) (compile_formula rhs)
  | Syntax.Or lhs rhs => MC.FOr (compile_formula lhs) (compile_formula rhs)
  | Syntax.Not body => MC.FNot (compile_formula body)
  | Syntax.Exists body => MC.FExists (compile_formula body)
  | Syntax.Forall body => MC.FNot (MC.FExists (MC.FNot (compile_formula body)))
  end.

Lemma compile_term_well_formed :
  forall t, MC.wft 0 (compile_term t).
Proof.
  induction t; simpl.
  - constructor.
  - constructor; [lia | lia | constructor].
  - apply MC.wf_add; auto.
  - apply MC.wf_neg; auto.
  - apply MC.wf_mul; auto.
Qed.

Lemma compile_formula_well_formed :
  forall f, MC.wff_ue (compile_formula f).
Proof.
  induction f; simpl.
  - constructor.
  - constructor.
  - unfold backend_eq. constructor. split.
    + apply MC.wf_sub; apply compile_term_well_formed.
    + constructor.
  - unfold backend_lt. constructor. split.
    + apply MC.wf_sub; apply compile_term_well_formed.
    + constructor.
  - unfold backend_le, backend_lt. constructor. constructor. split.
    + apply MC.wf_sub; apply compile_term_well_formed.
    + constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor. constructor. constructor. assumption.
Qed.

Lemma compile_term_correct :
  forall t env cenv,
    MC.interpret_term cenv env (compile_term t) = term_semantics env t.
Proof.
  induction t; intros env cenv; simpl.
  - reflexivity.
  - unfold backend_zero. cbn. destruct (env n); reflexivity.
  - rewrite MC.interpret_add, IHt1, IHt2. reflexivity.
  - rewrite MC.interpret_neg, IHt. reflexivity.
  - rewrite MC.interpret_mul, IHt. reflexivity.
Qed.

Lemma compile_formula_correct :
  forall f env cenv,
    MC.interpret_formula cenv env (compile_formula f) <->
    formula_semantics env f.
Proof.
  induction f; intros env cenv; simpl; try tauto.
  - rewrite MC.interpret_sub, !compile_term_correct. lia.
  - rewrite MC.interpret_sub, !compile_term_correct. lia.
  - rewrite MC.interpret_sub, !compile_term_correct. lia.
  - rewrite IHf1, IHf2. tauto.
  - rewrite IHf1, IHf2. tauto.
  - rewrite IHf. tauto.
  - split.
    + intros [value Hvalue]. exists value.
      apply (proj1 (IHf (MC.extend env value) cenv)); exact Hvalue.
    + intros [value Hvalue]. exists value.
      apply (proj2 (IHf (MC.extend env value) cenv)); exact Hvalue.
  - split.
    + intros H value. apply (proj1 (IHf (MC.extend env value) cenv)).
      apply NNPP. intro Hnot. apply H. exists value. exact Hnot.
    + intros H [value Hnot]. apply Hnot.
      apply (proj2 (IHf (MC.extend env value) cenv)). apply H.
Qed.

Definition eliminate (f : Syntax.formula) : MC.formula := MC.qe (compile_formula f).

Theorem eliminate_well_formed : forall f, MC.wff (eliminate f).
Proof. intro f. apply MC.wf_qe, compile_formula_well_formed. Qed.

Theorem eliminate_correct :
  forall f env cenv,
    MC.interpret_formula cenv env (eliminate f) <-> formula_semantics env f.
Proof.
  intros f env cenv. unfold eliminate.
  rewrite MC.interpret_qe by apply compile_formula_well_formed.
  apply compile_formula_correct.
Qed.
