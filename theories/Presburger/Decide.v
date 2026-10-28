From Mell.Presburger Require Import Syntax Semantics QE.
From MiniCooper Require Import Constant Theory.
From Coq Require Import ZArith Znumtheory Bool Lia Extraction.

Open Scope Z_scope.

Module MC := MiniCooper.Theory.

Definition backend_empty_environment : MC.environment := fun _ => 0.

Fixpoint eval_qf (f : MC.formula) : bool :=
  match f with
  | MC.FAtom MC.Eq t =>
      Z.eqb (MC.interpret_term backend_empty_environment
        backend_empty_environment t) 0
  | MC.FAtom MC.Lt t =>
      Z.ltb 0 (MC.interpret_term backend_empty_environment
        backend_empty_environment t)
  | MC.FAtom (MC.Dv divisor) t =>
      MC.Zdivideb divisor (MC.interpret_term backend_empty_environment
        backend_empty_environment t)
  | MC.FFalse => false
  | MC.FTrue => true
  | MC.FAnd lhs rhs => eval_qf lhs && eval_qf rhs
  | MC.FOr lhs rhs => eval_qf lhs || eval_qf rhs
  | MC.FNot body => negb (eval_qf body)
  | MC.FExists _ => false
  end.

Lemma Zdivideb_true_iff :
  forall divisor value, MC.Zdivideb divisor value = true <-> (divisor | value).
Proof.
  intros divisor value. unfold MC.Zdivideb.
  destruct (Zdivide_dec divisor value); split; intro H; try discriminate; auto.
Qed.

Lemma eval_qf_correct :
  forall f,
    MC.wff f ->
    eval_qf f = true <->
    MC.interpret_formula backend_empty_environment
      backend_empty_environment f.
Proof.
  intros f Hwf. induction Hwf; simpl.
  - destruct p; simpl.
    + rewrite Z.eqb_eq. lia.
    + rewrite Z.ltb_lt. tauto.
    + apply Zdivideb_true_iff.
  - split; [discriminate | contradiction].
  - tauto.
  - rewrite Bool.andb_true_iff, IHHwf1, IHHwf2. tauto.
  - rewrite Bool.orb_true_iff, IHHwf1, IHHwf2. tauto.
  - rewrite Bool.negb_true_iff. destruct (eval_qf f) eqn:Heval.
    + split.
      * discriminate.
      * intro Hnot. exfalso. apply Hnot. apply IHHwf. reflexivity.
    + split.
      * intro Hfalse. intro Hinterp. apply IHHwf in Hinterp. discriminate.
      * intro Hnot. reflexivity.
Qed.

Definition presburger_decide (s : sentence) : bool :=
  if formula_closed 0 (sentence_formula s)
  then eval_qf (eliminate (sentence_formula s))
  else false.

Theorem presburger_decide_correct :
  forall s, presburger_decide s = true <-> sentence_semantics s.
Proof.
  intros [f Hclosed]. unfold presburger_decide, sentence_semantics; simpl.
  rewrite Hclosed. simpl.
  rewrite eval_qf_correct by apply eliminate_well_formed.
  apply eliminate_correct.
Qed.
