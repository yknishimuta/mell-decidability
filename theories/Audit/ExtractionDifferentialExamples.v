From Coq Require Import List Vector ZArith Lia.
From Mell.Core Require Import Vector FiniteTree Code Search.
From Mell.Logic Require Import Syntax Code UnitFragment MultiplicativeWeight.
From Mell.BVAS Require Import System Runs Certificates Code.
From Mell.Semilinear Require Import Presentation Code.
From Mell.Presburger Require Import Syntax Decide.
From Mell.Decision Require Import Invariant Stage MELL.
From Mell.Reduction Require Import Main.

Import ListNotations.
Open Scope Z_scope.

(** Closed computations used as the Gallina side of the QA-3 differential
    audit.  The OCaml runner reconstructs the same named data independently. *)

Definition qa3_nvec1 (n : nat) : NVec 1 :=
  Vector.cons nat n 0 (Vector.nil nat).

Definition qa3_zvec1 (z : Z) : ZVec 1 :=
  Vector.cons Z z 0 (Vector.nil Z).

Definition qa3_plus_two : Action 1 :=
  {| action_arity := 1;
     action_arity_positive := Nat.lt_0_succ 0;
     action_offset := qa3_zvec1 2 |}.

Definition qa3_minus_one : Action 1 :=
  {| action_arity := 1;
     action_arity_positive := Nat.lt_0_succ 0;
     action_offset := qa3_zvec1 (-1) |}.

Definition qa3_binary_minus_one : Action 1 :=
  {| action_arity := 2;
     action_arity_positive := Nat.lt_0_succ 1;
     action_offset := qa3_zvec1 (-1) |}.

Definition qa3_even_system : IBVAS 1 :=
  {| initial_vectors := [qa3_nvec1 0]; system_actions := [qa3_plus_two] |}.

Definition qa3_intermediate_system : IBVAS 1 :=
  {| initial_vectors := [qa3_nvec1 0];
     system_actions := [qa3_minus_one; qa3_plus_two] |}.

Definition qa3_binary_system : IBVAS 1 :=
  {| initial_vectors := [qa3_nvec1 1];
     system_actions := [qa3_binary_minus_one] |}.

Definition qa3_empty_system : IBVAS 1 :=
  {| initial_vectors := []; system_actions := [] |}.

Definition qa3_leaf : RawRun := (tree_leaf 0%nat : RawRun).
Definition qa3_unary_run : RawRun :=
  tree_node 0%nat (forest_cons qa3_leaf forest_nil).
Definition qa3_binary_run : RawRun :=
  tree_node 0%nat (forest_cons qa3_leaf (forest_cons qa3_leaf forest_nil)).
Definition qa3_bad_intermediate_run : RawRun :=
  tree_node 1%nat
    (forest_cons (tree_node 0%nat (forest_cons qa3_leaf forest_nil)) forest_nil).

Definition qa3_even_code : SemiCode 1 :=
  [(qa3_nvec1 0, [qa3_nvec1 2])].
Definition qa3_zero_code : SemiCode 1 := [(qa3_nvec1 0, [])].
Definition qa3_odd_code : SemiCode 1 :=
  [(qa3_nvec1 1, [qa3_nvec1 2])].
Definition qa3_nat_code : SemiCode 1 :=
  [(qa3_nvec1 0, [qa3_nvec1 1])].

Definition qa3_reach0 : ReachInstance :=
  {| reach_dimension := 0;
     reach_system := {| initial_vectors := [Vector.nil nat];
                        system_actions := [] |};
     reach_target := Vector.nil nat |}.

Example qa3_sequent_roundtrip :
  decode_sequent (encode_sequent [One]) = Some [One].
Proof. apply decode_sequent_encode. Qed.

Example qa3_sequent_duplicate_roundtrip :
  decode_sequent (encode_sequent [One; One]) = Some [One; One].
Proof. apply decode_sequent_encode. Qed.

Example qa3_sequent_big_atom_roundtrip :
  decode_sequent (encode_sequent [Atom (Nat.pow 2 80)]) =
    Some [Atom (Nat.pow 2 80)].
Proof. apply decode_sequent_encode. Qed.

Example qa3_invalid_sequent : decode_sequent 16 = None.
Proof. reflexivity. Qed.

Example qa3_reach_roundtrip :
  decode_reach_instance (encode_reach_instance qa3_reach0) = Some qa3_reach0.
Proof. apply decode_reach_instance_encode. Qed.

Definition qa3_invalid_reach_code : nat :=
  Cantor.to_nat (0%nat,
    Cantor.to_nat (encode_ibvas qa3_empty_system, 1%nat)).

Example qa3_invalid_reach :
  decode_reach_instance qa3_invalid_reach_code = None.
Proof. reflexivity. Qed.

Example qa3_run_roundtrip :
  decode_run (encode_run qa3_binary_run) = Some qa3_binary_run.
Proof. apply decode_run_encode. Qed.

Example qa3_semi_roundtrip :
  decode_semi 1 (encode_semi qa3_even_code) = Some qa3_even_code.
Proof. apply decode_semi_encode. Qed.

Example qa3_semi_duplicate_roundtrip :
  decode_semi 1 (encode_semi
    [(qa3_nvec1 0, [qa3_nvec1 2]); (qa3_nvec1 0, [qa3_nvec1 2])]) =
  Some [(qa3_nvec1 0, [qa3_nvec1 2]); (qa3_nvec1 0, [qa3_nvec1 2])].
Proof. apply decode_semi_encode. Qed.

Example qa3_semi_dimension_zero_roundtrip :
  decode_semi 0 (encode_semi [(@Vector.nil nat, [])]) =
    Some [(@Vector.nil nat, [])].
Proof. apply decode_semi_encode. Qed.

Example qa3_invalid_vector_length :
  decode_nvec 2 (list_encode nat_codec [7%nat]) = None.
Proof. reflexivity. Qed.

Example qa3_eval_leaf :
  eval_run qa3_even_system qa3_leaf = Some (qa3_nvec1 0).
Proof. reflexivity. Qed.

Example qa3_eval_unary :
  eval_run qa3_even_system qa3_unary_run = Some (qa3_nvec1 2).
Proof. reflexivity. Qed.

Example qa3_eval_binary_duplicate :
  eval_run qa3_binary_system qa3_binary_run = Some (qa3_nvec1 1).
Proof. reflexivity. Qed.

Example qa3_eval_bad_action :
  eval_run qa3_even_system
    (tree_node 7%nat (forest_cons qa3_leaf forest_nil)) = None.
Proof. reflexivity. Qed.

Example qa3_eval_bad_arity :
  eval_run qa3_even_system (tree_node 0%nat forest_nil) = None.
Proof. reflexivity. Qed.

Example qa3_eval_bad_initial :
  eval_run qa3_even_system (tree_leaf 3%nat) = None.
Proof. reflexivity. Qed.

Example qa3_eval_negative_intermediate :
  eval_run qa3_intermediate_system qa3_bad_intermediate_run = None.
Proof. reflexivity. Qed.

Example qa3_invariant_even_accept :
  check_invariantP qa3_even_system qa3_even_code (qa3_nvec1 1) = true.
Proof. reflexivity. Qed.

Example qa3_invariant_closure_reject :
  check_invariantP qa3_even_system qa3_zero_code (qa3_nvec1 1) = false.
Proof. reflexivity. Qed.

Example qa3_invariant_initial_reject :
  check_invariantP qa3_even_system qa3_odd_code (qa3_nvec1 0) = false.
Proof. reflexivity. Qed.

Example qa3_invariant_target_reject :
  check_invariantP qa3_even_system qa3_nat_code (qa3_nvec1 1) = false.
Proof. reflexivity. Qed.

Definition qa3_exists_true : sentence :=
  close_sentence (Exists (Eq (Var 0) (Num (-1)))) eq_refl.
Definition qa3_exists_false : sentence :=
  close_sentence (Exists (ANd (Lt (Var 0) (Num 0))
    (Le (Num 0) (Var 0)))) eq_refl.
Definition qa3_forall_true : sentence :=
  close_sentence (Forall (Eq (Var 0) (Var 0))) eq_refl.
Definition qa3_forall_false : sentence :=
  close_sentence (Forall (Eq (Var 0) (Num 0))) eq_refl.
Definition qa3_nested_quantifiers : sentence :=
  close_sentence
    (Forall (Exists (Eq (Var 0) (Plus (Var 1) (Num 1))))) eq_refl.
Definition qa3_divisible : sentence :=
  close_sentence (Exists (Eq (Scale 3 (Var 0)) (Num (-12)))) eq_refl.

Example qa3_presburger_exists_true : presburger_decide qa3_exists_true = true.
Proof. reflexivity. Qed.
Example qa3_presburger_exists_false : presburger_decide qa3_exists_false = false.
Proof. reflexivity. Qed.
Example qa3_presburger_forall_true : presburger_decide qa3_forall_true = true.
Proof. reflexivity. Qed.
Example qa3_presburger_forall_false : presburger_decide qa3_forall_false = false.
Proof. reflexivity. Qed.
Example qa3_presburger_nested : presburger_decide qa3_nested_quantifiers = true.
Proof. reflexivity. Qed.
Example qa3_presburger_divisible : presburger_decide qa3_divisible = true.
Proof. reflexivity. Qed.

Example qa3_unit_yes : unit_sequent_provableb [One] = true.
Proof. reflexivity. Qed.
Example qa3_unit_no : unit_sequent_provableb [Atom 0] = false.
Proof. reflexivity. Qed.
Example qa3_unit_exponential : unit_sequent_provableb [Bang One] = true.
Proof. reflexivity. Qed.
Example qa3_weight_refutes : multiplicative_weight_refutes [One; One] = true.
Proof. reflexivity. Qed.
Example qa3_weight_not_applicable :
  multiplicative_weight_refutes [Bang One] = false.
Proof. reflexivity. Qed.
Example qa3_goal_saturation_yes :
  mell_goal_saturation_decide [Atom 0; CoAtom 0] = Some true.
Proof. reflexivity. Qed.
Example qa3_goal_saturation_none :
  mell_goal_saturation_decide [Atom 0; CoAtom 1] = None.
Proof. reflexivity. Qed.
Example qa3_full_saturation_yes :
  mell_full_saturation_decide [One] = Some true.
Proof. reflexivity. Qed.
Example qa3_full_saturation_no :
  mell_full_saturation_decide [] = Some false.
Proof. reflexivity. Qed.

Example qa3_bvas_stage_yes :
  bvas_stage qa3_even_system (qa3_nvec1 0) 0 = Some true.
Proof. reflexivity. Qed.
Example qa3_bvas_stage_target_mismatch :
  bvas_stage qa3_even_system (qa3_nvec1 1) 0 = None.
Proof. reflexivity. Qed.
Example qa3_bvas_stage_no :
  bvas_stage qa3_even_system (qa3_nvec1 1)
    (2 * encode_semi qa3_even_code + 1) = Some false.
Proof. reflexivity. Qed.

Example qa3_mell_stage_fast_yes : mell_stage [One] 0 = Some true.
Proof. reflexivity. Qed.
Example qa3_mell_stage_fast_no : mell_stage [] 1 = Some false.
Proof. reflexivity. Qed.
Example qa3_mell_fuel_zero : mell_search_fuel [One] 0 = None.
Proof. reflexivity. Qed.
Example qa3_mell_fuel_one_yes : mell_search_fuel [One] 1 = Some true.
Proof. reflexivity. Qed.
Example qa3_mell_fuel_one_no : mell_search_fuel [] 1 = Some false.
Proof. reflexivity. Qed.

Definition qa3_big_nat : nat := Nat.pow 2 80.
Example qa3_big_nat_codec :
  decode nat_codec (encode nat_codec qa3_big_nat) = Some qa3_big_nat.
Proof. apply decode_encode. Qed.
Example qa3_big_nat_add :
  (qa3_big_nat + 1)%nat = S qa3_big_nat.
Proof. apply Nat.add_1_r. Qed.
Example qa3_big_nat_sub :
  (qa3_big_nat + 7 - qa3_big_nat)%nat = 7%nat.
Proof. rewrite Nat.add_comm. apply Nat.add_sub. Qed.
Example qa3_z_add_cancel :
  (Z.of_nat qa3_big_nat + (- Z.of_nat qa3_big_nat))%Z = 0%Z.
Proof. apply Z.add_opp_diag_r. Qed.
Example qa3_z_div_negative : (-7 / 3)%Z = (-3)%Z.
Proof. reflexivity. Qed.
Example qa3_z_mod_negative : (-7 mod 3)%Z = 2%Z.
Proof. reflexivity. Qed.
Example qa3_signed_action :
  apply_action qa3_minus_one [qa3_nvec1 1] = Some (qa3_nvec1 0).
Proof. reflexivity. Qed.

Example qa3_decide_code_invalid : decide_code 16 = false.
Proof. reflexivity. Qed.
Example qa3_public_mell_yes : mell_decide [One] = true.
Proof. reflexivity. Qed.
Example qa3_public_mell_no : mell_decide [] = false.
Proof. reflexivity. Qed.

Print Assumptions qa3_presburger_nested.
Print Assumptions qa3_goal_saturation_yes.
Print Assumptions qa3_bvas_stage_yes.
Print Assumptions qa3_mell_fuel_one_yes.
