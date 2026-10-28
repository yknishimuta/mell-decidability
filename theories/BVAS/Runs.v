From Coq Require Import List Lia Arith.PeanoNat.
From Mell.Core Require Import Vector FiniteTree.
From Mell.BVAS Require Import System.

Definition RawRun := FiniteTree nat nat.
Definition RawRuns := FiniteForest nat nat.

Inductive Reach {d} (S : IBVAS d) : NVec d -> Prop :=
| reach_initial : forall index value,
    nth_error (initial_vectors S) index = Some value ->
    Reach S value
| reach_action : forall index action children value,
    nth_error (system_actions S) index = Some action ->
    ReachChildren S children ->
    apply_action action children = Some value ->
    Reach S value
with ReachChildren {d} (S : IBVAS d) : list (NVec d) -> Prop :=
| reach_children_nil : ReachChildren S nil
| reach_children_cons : forall value values,
    Reach S value -> ReachChildren S values ->
    ReachChildren S (value :: values).

Scheme Reach_ind' := Induction for Reach Sort Prop
with ReachChildren_ind' := Induction for ReachChildren Sort Prop.

Combined Scheme Reach_mutind from Reach_ind', ReachChildren_ind'.

Lemma positive_action_rejects_no_children : forall d (a : Action d),
    apply_action a nil = None.
Proof.
  intros d [arity positive offset].
  destruct arity; [lia | reflexivity].
Qed.

Lemma reach_has_initial : forall d (S : IBVAS d) value,
    Reach S value -> exists initial, In initial (initial_vectors S).
Proof.
  intros d S.
  apply (Reach_ind' d S
    (fun value _ => exists initial, In initial (initial_vectors S))
    (fun values _ => values = nil \/
      exists initial, In initial (initial_vectors S))).
  - intros index value Hinitial.
    exists value. exact (nth_error_In _ _ Hinitial).
  - intros index action children value Haction reaches IHchildren Happly.
    destruct IHchildren as [Hempty | Hinitial].
    + subst children.
      rewrite positive_action_rejects_no_children in Happly.
      discriminate.
    + exact Hinitial.
  - left; reflexivity.
  - intros child children reach IHchild reaches IHchildren.
    right; exact IHchild.
Qed.

Theorem empty_initials_unreachable : forall d (actions : list (Action d)) value,
    ~ Reach {| initial_vectors := nil; system_actions := actions |} value.
Proof.
  intros d actions value Hreach.
  destruct (reach_has_initial _ _ _ Hreach) as [initial Hin].
  exact Hin.
Qed.
