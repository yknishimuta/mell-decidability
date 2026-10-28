From Coq Require Import List Vector ZArith Arith.Cantor.
From Mell.Core Require Import Vector FiniteTree Search Code.
From Mell.Logic Require Import Syntax Calculus YallaBridge Code.
From Mell.BVAS Require Import System Runs Code.
From Mell.Decision Require Import Stage BVAS MELL.

Import ListNotations.
Open Scope Z_scope.

Definition final_nvec1 (n : nat) : NVec 1 :=
  Vector.cons nat n 0 (Vector.nil nat).

Definition final_zvec1 (z : Z) : ZVec 1 :=
  Vector.cons Z z 0 (Vector.nil Z).

Definition final_plus_two : Action 1 :=
  {| action_arity := 1;
     action_arity_positive := Nat.lt_0_succ 0;
     action_offset := final_zvec1 2 |}.

Definition final_even_system : IBVAS 1 :=
  {| initial_vectors := [final_nvec1 0];
     system_actions := [final_plus_two] |}.

Example final_stage_run_yes :
  bvas_stage final_even_system (final_nvec1 0)
    (2 * encode_run (tree_leaf 0%nat : RawRun)) = Some true.
Proof. reflexivity. Qed.

Example final_search_zero_fuel :
  bvas_search_fuel final_even_system (final_nvec1 0) 0 = None.
Proof. reflexivity. Qed.

Example final_bvas_reachable_decides_true :
  bvas_decide final_even_system (final_nvec1 0) = true.
Proof.
  apply (proj2 (bvas_decide_true_iff 1 final_even_system (final_nvec1 0))).
  apply (reach_initial final_even_system 0). reflexivity.
Qed.

Example final_mell_one_yes : mell_decide [One] = true.
Proof. apply (proj2 (mell_decide_true_iff [One])), provable_one. Qed.

Example final_mell_empty_no : mell_decide [] = false.
Proof. apply (proj2 (mell_decide_false_iff [])), not_provable_empty. Qed.

Example final_code_round_trip :
  decode_sequent (encode_sequent [Atom 0; CoAtom 0]) =
    Some [Atom 0; CoAtom 0].
Proof. apply decode_encode_sequent. Qed.

Definition invalid_sequent_code : nat := 16%nat.

Example final_invalid_sequent_code_rejected :
  decode_sequent invalid_sequent_code = None.
Proof. reflexivity. Qed.

Example final_invalid_sequent_code_decides_false :
  decide_code invalid_sequent_code = false.
Proof. apply decide_code_invalid, final_invalid_sequent_code_rejected. Qed.

Example final_encoded_one_agrees :
  decide_code (encode_sequent [One]) = mell_decide [One].
Proof. apply decide_code_encode. Qed.
