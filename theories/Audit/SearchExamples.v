From Coq Require Import Arith.PeanoNat Lia Extraction.
From Mell.Core Require Import Search.

Definition parity_stage (x n : nat) : option bool :=
  if Nat.eqb n x then Some (Nat.even x) else None.

Lemma parity_eventual : forall x, exists n, parity_stage x n <> None.
Proof.
  intro x; exists x.
  unfold parity_stage; rewrite Nat.eqb_refl; discriminate.
Qed.

Definition parity_search (x : nat) : bool :=
  search_of_eventual parity_stage parity_eventual x.

Lemma parity_search_spec : forall x, parity_search x = Nat.even x.
Proof.
  intro x.
  unfold parity_search.
  destruct (@search_of_eventual_spec nat parity_stage parity_eventual x)
    as [n Hstage].
  unfold parity_stage in Hstage.
  destruct (Nat.eqb n x).
  - injection Hstage as Heq. symmetry; exact Heq.
  - discriminate.
Qed.

Lemma parity_fuel_before : forall x fuel,
    fuel <= x -> search_fuel parity_stage x fuel = None.
Proof.
  intros x fuel; induction fuel as [|fuel IH]; simpl.
  - reflexivity.
  - intro Hle. rewrite IH by lia.
    unfold parity_stage.
    destruct (Nat.eqb fuel x) eqn:Heq; [|reflexivity].
    apply Nat.eqb_eq in Heq; lia.
Qed.

Lemma parity_fuel_agrees : forall x,
    search_fuel parity_stage x (S x) = Some (parity_search x).
Proof.
  intro x; simpl.
  rewrite parity_fuel_before by lia.
  unfold parity_stage; rewrite Nat.eqb_refl, parity_search_spec.
  reflexivity.
Qed.

Check search_fuel.
Check search_fuel_sound.
Check search_fuel_first.
Check search_fuel_eventually_hits.
Check stage_hit_dec.
Check search_of_eventual.
Check search_of_eventual_spec.
Check search_of_eventual_sound.

Check parity_stage.
Check parity_search.
Check parity_search_spec.
Check parity_fuel_agrees.

Print Assumptions search_of_eventual_spec.
Print Assumptions search_of_eventual_sound.
Print Assumptions parity_search_spec.

Extraction Language OCaml.
Set Extraction Output Directory "docs/review/extraction".
Extraction "search.ml"
  search_fuel search_of_eventual parity_stage parity_search.
