From Coq Require Import List Arith.PeanoNat.
From Mell.Core Require Import FiniteTree Code.
From Mell.Logic Require Import Syntax.

Import ListNotations.

Fixpoint formula_to_tree (A : formula) : FiniteTree nat nat :=
  match A with
  | Atom p => tree_leaf (2 * p)
  | CoAtom p => tree_leaf (S (2 * p))
  | One => tree_node 0 forest_nil
  | Bottom => tree_node 1 forest_nil
  | Tensor A B => tree_node 2
      (forest_cons (formula_to_tree A)
        (forest_cons (formula_to_tree B) forest_nil))
  | Par A B => tree_node 3
      (forest_cons (formula_to_tree A)
        (forest_cons (formula_to_tree B) forest_nil))
  | Bang A => tree_node 4 (forest_cons (formula_to_tree A) forest_nil)
  | WhyNot A => tree_node 5 (forest_cons (formula_to_tree A) forest_nil)
  end.

Fixpoint tree_to_formula (tree : FiniteTree nat nat) : option formula :=
  match tree with
  | tree_leaf label =>
      if Nat.even label
      then Some (Atom (Nat.div2 label))
      else Some (CoAtom (Nat.div2 label))
  | tree_node label children =>
      match forest_to_formulas children with
      | Some nil =>
          match label with 0 => Some One | 1 => Some Bottom | _ => None end
      | Some (A :: nil) =>
          match label with 4 => Some (Bang A) | 5 => Some (WhyNot A) | _ => None end
      | Some (A :: B :: nil) =>
          match label with 2 => Some (Tensor A B) | 3 => Some (Par A B) | _ => None end
      | _ => None
      end
  end
with forest_to_formulas (forest : FiniteForest nat nat) : option (list formula) :=
  match forest with
  | forest_nil => Some nil
  | forest_cons tree forest' =>
      match tree_to_formula tree, forest_to_formulas forest' with
      | Some A, Some As => Some (A :: As)
      | _, _ => None
      end
  end.

Lemma tree_to_formula_formula_to_tree : forall A,
    tree_to_formula (formula_to_tree A) = Some A.
Proof.
  induction A as [p | p | | | A IHA B IHB | A IHA B IHB | A IHA | A IHA].
  - change ((if Nat.even (2 * p) then Some (Atom (Nat.div2 (2 * p)))
      else Some (CoAtom (Nat.div2 (2 * p)))) = Some (Atom p)).
    rewrite Nat.even_mul, Nat.div2_double; reflexivity.
  - change ((if Nat.even (S (2 * p))
      then Some (Atom (Nat.div2 (S (2 * p))))
      else Some (CoAtom (Nat.div2 (S (2 * p))))) = Some (CoAtom p)).
    rewrite Nat.even_succ, Nat.odd_mul, Nat.odd_2, Nat.div2_succ_double.
    reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn; rewrite IHA, IHB; reflexivity.
  - cbn; rewrite IHA, IHB; reflexivity.
  - cbn; rewrite IHA; reflexivity.
  - cbn; rewrite IHA; reflexivity.
Qed.

Definition encode_formula (A : formula) : nat :=
  tree_encode (formula_to_tree A).

Definition decode_formula (code : nat) : option formula :=
  match tree_decode code with
  | Some tree => tree_to_formula tree
  | None => None
  end.

Lemma decode_formula_encode : forall A,
    decode_formula (encode_formula A) = Some A.
Proof.
  intro A. unfold decode_formula, encode_formula.
  rewrite tree_decode_encode.
  apply tree_to_formula_formula_to_tree.
Qed.

Definition formula_codec : Codec formula :=
  {| encode := encode_formula;
     decode := decode_formula;
     decode_encode := decode_formula_encode |}.

Definition encode_sequent : sequent -> nat := list_encode formula_codec.
Definition decode_sequent : nat -> option sequent := list_decode formula_codec.

Lemma decode_sequent_encode : forall Gamma,
    decode_sequent (encode_sequent Gamma) = Some Gamma.
Proof. apply list_decode_encode. Qed.

Definition sequent_codec : Codec sequent := list_codec formula_codec.
