From Coq Require Import Bool List.
From Mell.Logic Require Import Syntax Calculus.

Import ListNotations.

(** A small executable positive-unit fragment.  Every accepted formula has a
    closed cut-free derivation; rejected formulas are left to the complete
    decision procedure. *)
Fixpoint unit_formula_provableb (formula : formula) : bool :=
  match formula with
  | One => true
  | Tensor lhs rhs =>
      unit_formula_provableb lhs && unit_formula_provableb rhs
  | Bang body => unit_formula_provableb body
  | _ => false
  end.

Theorem unit_formula_provableb_sound : forall formula,
  unit_formula_provableb formula = true -> Derivation [formula].
Proof.
  induction formula; cbn; try discriminate.
  - intros Htrue. exact one_rule.
  - destruct (unit_formula_provableb formula1) eqn:Hleft;
      destruct (unit_formula_provableb formula2) eqn:Hright;
      cbn; try discriminate; intros Htrue.
    change (Derivation (Tensor formula1 formula2 :: [] ++ [])).
    apply tensor_rule.
    + now apply IHformula1.
    + now apply IHformula2.
  - intro Hbody.
    change (Derivation (Bang formula :: map WhyNot [])).
    apply promotion_rule. now apply IHformula.
Qed.

Definition unit_sequent_provableb (Gamma : sequent) : bool :=
  match Gamma with
  | [formula] => unit_formula_provableb formula
  | _ => false
  end.

Theorem unit_sequent_provableb_sound : forall Gamma,
  unit_sequent_provableb Gamma = true -> Provable Gamma.
Proof.
  intros [|formula [|next rest]] Haccept; cbn in Haccept; try discriminate.
  constructor. now apply unit_formula_provableb_sound.
Qed.
