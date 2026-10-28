From Coq Require Import List Arith.PeanoNat.

Import ListNotations.

Inductive formula : Set :=
| Atom : nat -> formula
| CoAtom : nat -> formula
| One : formula
| Bottom : formula
| Tensor : formula -> formula -> formula
| Par : formula -> formula -> formula
| Bang : formula -> formula
| WhyNot : formula -> formula.

Definition sequent := list formula.

Fixpoint dual (A : formula) : formula :=
  match A with
  | Atom p => CoAtom p
  | CoAtom p => Atom p
  | One => Bottom
  | Bottom => One
  | Tensor A B => Par (dual B) (dual A)
  | Par A B => Tensor (dual B) (dual A)
  | Bang A => WhyNot (dual A)
  | WhyNot A => Bang (dual A)
  end.

Lemma dual_involutive : forall A, dual (dual A) = A.
Proof.
  induction A; simpl; congruence.
Qed.

Lemma formula_eq_dec : forall A B : formula, {A = B} + {A <> B}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.
