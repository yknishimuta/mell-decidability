From Coq Require Import List.

Inductive FiniteTree (Leaf Node : Type) : Type :=
| tree_leaf : Leaf -> FiniteTree Leaf Node
| tree_node : Node -> FiniteForest Leaf Node -> FiniteTree Leaf Node
with FiniteForest (Leaf Node : Type) : Type :=
| forest_nil : FiniteForest Leaf Node
| forest_cons : FiniteTree Leaf Node -> FiniteForest Leaf Node ->
    FiniteForest Leaf Node.

Arguments tree_leaf {Leaf Node} _.
Arguments tree_node {Leaf Node} _ _.
Arguments forest_nil {Leaf Node}.
Arguments forest_cons {Leaf Node} _ _.

Scheme FiniteTree_ind' := Induction for FiniteTree Sort Prop
with FiniteForest_ind' := Induction for FiniteForest Sort Prop.

Combined Scheme FiniteTree_FiniteForest_ind
  from FiniteTree_ind', FiniteForest_ind'.

Fixpoint forest_length {Leaf Node} (rs : FiniteForest Leaf Node) : nat :=
  match rs with
  | forest_nil => 0
  | forest_cons _ rs => S (forest_length rs)
  end.
