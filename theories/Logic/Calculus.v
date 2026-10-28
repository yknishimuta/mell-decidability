From Coq Require Import List.
From Yalla.OLlibs Require Import Permutation_Type.
From Mell.Logic Require Import Syntax.

Import ListNotations.

Inductive Derivation : sequent -> Type :=
| identity_rule : forall p, Derivation [CoAtom p; Atom p]
| one_rule : Derivation [One]
| bottom_rule : forall Gamma, Derivation Gamma -> Derivation (Bottom :: Gamma)
| tensor_rule : forall A B Gamma Delta,
    Derivation (A :: Gamma) ->
    Derivation (B :: Delta) ->
    Derivation (Tensor A B :: Gamma ++ Delta)
| par_rule : forall A B Gamma,
    Derivation (A :: B :: Gamma) ->
    Derivation (Par A B :: Gamma)
| promotion_rule : forall A Gamma,
    Derivation (A :: map WhyNot Gamma) ->
    Derivation (Bang A :: map WhyNot Gamma)
| dereliction_rule : forall A Gamma,
    Derivation (A :: Gamma) ->
    Derivation (WhyNot A :: Gamma)
| weakening_rule : forall A Gamma,
    Derivation Gamma ->
    Derivation (WhyNot A :: Gamma)
| contraction_rule : forall A Gamma,
    Derivation (WhyNot A :: WhyNot A :: Gamma) ->
    Derivation (WhyNot A :: Gamma)
| exchange_rule : forall Gamma Delta,
    Derivation Gamma ->
    Permutation_Type Gamma Delta ->
    Derivation Delta.

Definition Provable (Gamma : sequent) : Prop := inhabited (Derivation Gamma).

Inductive DerivationWithCut : sequent -> Type :=
| cut_identity_rule : forall p, DerivationWithCut [CoAtom p; Atom p]
| cut_one_rule : DerivationWithCut [One]
| cut_bottom_rule : forall Gamma,
    DerivationWithCut Gamma -> DerivationWithCut (Bottom :: Gamma)
| cut_tensor_rule : forall A B Gamma Delta,
    DerivationWithCut (A :: Gamma) ->
    DerivationWithCut (B :: Delta) ->
    DerivationWithCut (Tensor A B :: Gamma ++ Delta)
| cut_par_rule : forall A B Gamma,
    DerivationWithCut (A :: B :: Gamma) ->
    DerivationWithCut (Par A B :: Gamma)
| cut_promotion_rule : forall A Gamma,
    DerivationWithCut (A :: map WhyNot Gamma) ->
    DerivationWithCut (Bang A :: map WhyNot Gamma)
| cut_dereliction_rule : forall A Gamma,
    DerivationWithCut (A :: Gamma) ->
    DerivationWithCut (WhyNot A :: Gamma)
| cut_weakening_rule : forall A Gamma,
    DerivationWithCut Gamma ->
    DerivationWithCut (WhyNot A :: Gamma)
| cut_contraction_rule : forall A Gamma,
    DerivationWithCut (WhyNot A :: WhyNot A :: Gamma) ->
    DerivationWithCut (WhyNot A :: Gamma)
| cut_exchange_rule : forall Gamma Delta,
    DerivationWithCut Gamma ->
    Permutation_Type Gamma Delta ->
    DerivationWithCut Delta
| cut_rule : forall A Gamma Delta,
    DerivationWithCut (A :: Gamma) ->
    DerivationWithCut (dual A :: Delta) ->
    DerivationWithCut (Gamma ++ Delta).

Definition ProvableWithCut (Gamma : sequent) : Prop :=
  inhabited (DerivationWithCut Gamma).

Fixpoint include_cut_free {Gamma} (pi : Derivation Gamma) :
    DerivationWithCut Gamma :=
  match pi with
  | identity_rule p => cut_identity_rule p
  | one_rule => cut_one_rule
  | bottom_rule Gamma pi => cut_bottom_rule Gamma (include_cut_free pi)
  | tensor_rule A B Gamma Delta pi1 pi2 =>
      cut_tensor_rule A B Gamma Delta
        (include_cut_free pi1) (include_cut_free pi2)
  | par_rule A B Gamma pi => cut_par_rule A B Gamma (include_cut_free pi)
  | promotion_rule A Gamma pi =>
      cut_promotion_rule A Gamma (include_cut_free pi)
  | dereliction_rule A Gamma pi =>
      cut_dereliction_rule A Gamma (include_cut_free pi)
  | weakening_rule A Gamma pi =>
      cut_weakening_rule A Gamma (include_cut_free pi)
  | contraction_rule A Gamma pi =>
      cut_contraction_rule A Gamma (include_cut_free pi)
  | exchange_rule Gamma Delta pi perm =>
      cut_exchange_rule Gamma Delta (include_cut_free pi) perm
  end.

Lemma provable_implies_with_cut : forall Gamma,
    Provable Gamma -> ProvableWithCut Gamma.
Proof.
  intros Gamma [pi].
  constructor; exact (include_cut_free pi).
Qed.

Lemma provable_atom_identity : forall p, Provable [CoAtom p; Atom p].
Proof. intro p; constructor; apply identity_rule. Qed.

Lemma provable_atom_identity_swapped : forall p, Provable [Atom p; CoAtom p].
Proof.
  intro p; constructor.
  apply exchange_rule with (Gamma := [CoAtom p; Atom p]).
  - apply identity_rule.
  - apply Permutation_Type_swap.
Qed.

Lemma provable_one : Provable [One].
Proof. constructor; apply one_rule. Qed.

Lemma provable_one_bot : Provable [One; Bottom].
Proof.
  constructor.
  apply exchange_rule with (Gamma := [Bottom; One]).
  - apply bottom_rule, one_rule.
  - apply Permutation_Type_swap.
Qed.

Lemma provable_exchange_iff : forall Gamma Delta,
    Permutation_Type Gamma Delta -> (Provable Gamma <-> Provable Delta).
Proof.
  intros Gamma Delta perm; split; intros [pi]; constructor.
  - exact (exchange_rule Gamma Delta pi perm).
  - exact (exchange_rule Delta Gamma pi (Permutation_Type_sym perm)).
Qed.
