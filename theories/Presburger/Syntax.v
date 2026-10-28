From Coq Require Import ZArith Bool.

Open Scope Z_scope.

Inductive term : Type :=
| Num : Z -> term
| Var : nat -> term
| Plus : term -> term -> term
| Neg : term -> term
| Scale : Z -> term -> term.

Inductive formula : Type :=
| Bot : formula
| Top : formula
| Eq : term -> term -> formula
| Lt : term -> term -> formula
| Le : term -> term -> formula
| ANd : formula -> formula -> formula
| Or : formula -> formula -> formula
| Not : formula -> formula
| Exists : formula -> formula
| Forall : formula -> formula.

Fixpoint term_closed (bound : nat) (t : term) : bool :=
  match t with
  | Num _ => true
  | Var x => Nat.ltb x bound
  | Plus lhs rhs => term_closed bound lhs && term_closed bound rhs
  | Neg body => term_closed bound body
  | Scale _ body => term_closed bound body
  end.

Fixpoint formula_closed (bound : nat) (f : formula) : bool :=
  match f with
  | Bot | Top => true
  | Eq lhs rhs | Lt lhs rhs | Le lhs rhs =>
      term_closed bound lhs && term_closed bound rhs
  | ANd lhs rhs | Or lhs rhs =>
      formula_closed bound lhs && formula_closed bound rhs
  | Not body => formula_closed bound body
  | Exists body | Forall body => formula_closed (S bound) body
  end.

Record sentence : Type := {
  sentence_formula : formula;
  sentence_closed : formula_closed 0 sentence_formula = true
}.

Definition close_sentence
    (f : formula) (closed : formula_closed 0 f = true) : sentence :=
  {| sentence_formula := f; sentence_closed := closed |}.
