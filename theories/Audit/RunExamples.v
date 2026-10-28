From Coq Require Import List ZArith.
From Mell.Core Require Import Vector FiniteTree.
From Mell.BVAS Require Import System Runs Certificates.

Import ListNotations.

Definition nvec1 (n : nat) : NVec 1 :=
  Vector.cons nat n 0 (Vector.nil nat).

Definition zvec1 (z : Z) : ZVec 1 :=
  Vector.cons Z z 0 (Vector.nil Z).

Definition unary_minus_one : Action 1 :=
  {| action_arity := 1;
     action_arity_positive := Nat.lt_0_succ 0;
     action_offset := zvec1 (-1)%Z |}.

Definition unary_plus_one : Action 1 :=
  {| action_arity := 1;
     action_arity_positive := Nat.lt_0_succ 0;
     action_offset := zvec1 1%Z |}.

Definition intermediate_system : IBVAS 1 :=
  {| initial_vectors := [nvec1 0];
     system_actions := [unary_minus_one; unary_plus_one] |}.

Definition invalid_intermediate_run : RawRun :=
  tree_node 1
    (forest_cons
      (tree_node 0 (forest_cons (tree_leaf 0) forest_nil))
      forest_nil).

Example invalid_intermediate_rejected :
    eval_run intermediate_system invalid_intermediate_run = None.
Proof. reflexivity. Qed.

Example unknown_initial_rejected :
    eval_run intermediate_system (tree_leaf 1) = None.
Proof. reflexivity. Qed.

Example unknown_action_rejected :
    eval_run intermediate_system
      (tree_node 2 (forest_cons (tree_leaf 0) forest_nil)) = None.
Proof. reflexivity. Qed.

Example arity_mismatch_rejected :
    eval_run intermediate_system (tree_node 0 forest_nil) = None.
Proof. reflexivity. Qed.

Definition binary_minus_one : Action 1 :=
  {| action_arity := 2;
     action_arity_positive := Nat.lt_0_succ 1;
     action_offset := zvec1 (-1)%Z |}.

Definition duplicated_leaf_system : IBVAS 1 :=
  {| initial_vectors := [nvec1 1];
     system_actions := [binary_minus_one] |}.

Definition duplicated_leaf_run : RawRun :=
  tree_node 0
    (forest_cons (tree_leaf 0)
      (forest_cons (tree_leaf 0) forest_nil)).

Example duplicated_leaf_binary_accepted :
    eval_run duplicated_leaf_system duplicated_leaf_run = Some (nvec1 1).
Proof. reflexivity. Qed.

Definition dimension_zero_system : IBVAS 0 :=
  {| initial_vectors := [Vector.nil nat];
     system_actions := [] |}.

Example dimension_zero_accepted :
    eval_run dimension_zero_system (tree_leaf 0) = Some (Vector.nil nat).
Proof. reflexivity. Qed.

Check Vec.
Check NVec.
Check ZVec.
Check @IBVAS.
Check RawRun.
Check @Reach.
Check @apply_action.
Check @eval_run.
Check eval_run_sound.
Check eval_run_complete.

Check invalid_intermediate_rejected.
Check unknown_initial_rejected.
Check unknown_action_rejected.
Check arity_mismatch_rejected.
Check duplicated_leaf_binary_accepted.
Check dimension_zero_accepted.
Check empty_initials_unreachable.

Print Assumptions eval_run_sound.
Print Assumptions eval_run_complete.
Print Assumptions empty_initials_unreachable.
