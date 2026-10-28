From Coq Require Import List Vector ZArith.
From Mell.Core Require Import Vector FiniteTree.
From Mell.BVAS Require Import System Runs Code.
From Mell.Semilinear Require Import Presentation Formula Code.
From Mell.Decision Require Import Invariant Stage BVASOfSeparator.

Import ListNotations.
Open Scope Z_scope.

Definition invariant_nvec1 (n : nat) : NVec 1 :=
  Vector.cons nat n 0 (Vector.nil nat).

Definition invariant_zvec1 (z : Z) : ZVec 1 :=
  Vector.cons Z z 0 (Vector.nil Z).

Definition unary_plus_two : Action 1 :=
  {| action_arity := 1;
     action_arity_positive := Nat.lt_0_succ 0;
     action_offset := invariant_zvec1 2 |}.

Definition even_system : IBVAS 1 :=
  {| initial_vectors := [invariant_nvec1 0];
     system_actions := [unary_plus_two] |}.

Definition even_code : SemiCode 1 :=
  [(invariant_nvec1 0, [invariant_nvec1 2])].

Definition zero_code : SemiCode 1 :=
  [(invariant_nvec1 0, [])].

Definition odd_code : SemiCode 1 :=
  [(invariant_nvec1 1, [invariant_nvec1 2])].

Definition naturals_code : SemiCode 1 :=
  [(invariant_nvec1 0, [invariant_nvec1 1])].

Example even_invariant_accepted :
    check_invariantP even_system even_code (invariant_nvec1 1) = true.
Proof. reflexivity. Qed.

Example zero_candidate_rejected_for_closure :
    check_invariantP even_system zero_code (invariant_nvec1 1) = false.
Proof. reflexivity. Qed.

Example odd_candidate_rejected_for_initial :
    check_invariantP even_system odd_code (invariant_nvec1 0) = false.
Proof. reflexivity. Qed.

Example naturals_candidate_rejected_for_target :
    check_invariantP even_system naturals_code (invariant_nvec1 1) = false.
Proof. reflexivity. Qed.

Definition binary_minus_one_invariant : Action 1 :=
  {| action_arity := 2;
     action_arity_positive := Nat.lt_0_succ 1;
     action_offset := invariant_zvec1 (-1) |}.

Definition binary_system : IBVAS 1 :=
  {| initial_vectors := [invariant_nvec1 1];
     system_actions := [binary_minus_one_invariant] |}.

Example binary_odd_invariant_accepted :
    check_invariantP binary_system odd_code (invariant_nvec1 0) = true.
Proof. reflexivity. Qed.

Definition unary_minus_one_invariant : Action 1 :=
  {| action_arity := 1;
     action_arity_positive := Nat.lt_0_succ 0;
     action_offset := invariant_zvec1 (-1) |}.

Definition negative_result_system : IBVAS 1 :=
  {| initial_vectors := [invariant_nvec1 0];
     system_actions := [unary_minus_one_invariant] |}.

Example negative_result_is_not_an_applicable_rule :
    check_invariantP negative_result_system zero_code (invariant_nvec1 1) = true.
Proof. reflexivity. Qed.

Definition empty_system : IBVAS 1 :=
  {| initial_vectors := [];
     system_actions := [] |}.

Example empty_initials_admit_empty_invariant :
    check_invariantP empty_system ([] : SemiCode 1) (invariant_nvec1 0) = true.
Proof. reflexivity. Qed.

Definition zero_period_code : SemiCode 1 :=
  [(invariant_nvec1 0, [invariant_nvec1 0])].

Example zero_period_contains_base :
    check_membership zero_period_code (invariant_nvec1 0) = true.
Proof. reflexivity. Qed.

Example zero_period_excludes_successor :
    check_membership zero_period_code (invariant_nvec1 1) = false.
Proof. reflexivity. Qed.

Example bvas_stage_finds_run_on_even_stage :
    bvas_stage even_system (invariant_nvec1 0)
      (2 * encode_run (tree_leaf 0%nat : RawRun)) = Some true.
Proof. reflexivity. Qed.

Example bvas_stage_finds_invariant_on_odd_stage :
    bvas_stage even_system (invariant_nvec1 1)
      (2 * encode_semi even_code + 1) = Some false.
Proof. reflexivity. Qed.

Example bvas_stage_miss_is_none :
    bvas_stage empty_system (invariant_nvec1 0) 0 = None.
Proof. reflexivity. Qed.

Check compile_membership.
Check compile_membership_correct.
Check check_invariantP_correct.
Check check_invariant_sound.
Check bvas_stage_sound.
Check bvas_decide_of_separator.
Check bvas_decide_of_separator_spec.
Check bvas_decide_of_separator_sound.
Check bvas_decide_of_separator_complete.
Check bvas_decide_of_separator_correct.
Check bvas_decide_of_separator_false.

Print bvas_decide_of_separator.
Print Assumptions compile_membership_correct.
Print Assumptions check_invariantP_correct.
Print Assumptions check_invariant_sound.
Print Assumptions bvas_stage_sound.
Print Assumptions bvas_decide_of_separator_spec.
Print Assumptions bvas_decide_of_separator_sound.
Print Assumptions bvas_decide_of_separator_complete.
Print Assumptions bvas_decide_of_separator_correct.
Print Assumptions bvas_decide_of_separator_false.
