From Mell.BVASS Require Import Stateful StatefulAmalgamation Extend
  BoundedBranching.
From Mell.Core Require Import Vector.

From Coq Require Import List Vector ZArith Sorting.Permutation.

Import ListNotations.

Definition bb_state0 : Fin.t 1 := Fin.F1.
Definition bb_nvec1 (value : nat) : NVec 1 := Vector.of_list [value].
Definition bb_zvec1 (value : Z) : ZVec 1 := Vector.of_list [value].

Definition bb_rule (inputs : list (Fin.t 1))
    (nonempty : inputs <> []) : SRule 1 1 :=
  {| input_states := inputs;
     input_nonempty := nonempty;
     output_state := bb_state0;
     rule_delta := bb_zvec1 0 |}.

Definition bb_leaf : SRun 1 1 :=
  srun_leaf (bb_state0, bb_nvec1 0).
Definition bb_unary : SRun 1 1 :=
  srun_node (bb_rule [bb_state0] (fun H => List.nil_cons (eq_sym H)))
    (sruns_cons bb_leaf sruns_nil) (bb_state0, bb_nvec1 0).
Definition bb_binary : SRun 1 1 :=
  srun_node (bb_rule [bb_state0; bb_state0]
    (fun H => List.nil_cons (eq_sym H)))
    (sruns_cons bb_leaf (sruns_cons bb_leaf sruns_nil))
    (bb_state0, bb_nvec1 0).
Definition bb_nested : SRun 1 1 :=
  srun_node (bb_rule [bb_state0; bb_state0]
    (fun H => List.nil_cons (eq_sym H)))
    (sruns_cons bb_binary (sruns_cons bb_unary sruns_nil))
    (bb_state0, bb_nvec1 0).

Example branching_depth_leaf_regression : branching_depth bb_leaf = 0.
Proof. reflexivity. Qed.

Example branching_depth_unary_regression : branching_depth bb_unary = 0.
Proof. reflexivity. Qed.

Example branching_depth_binary_regression : branching_depth bb_binary = 1.
Proof. reflexivity. Qed.

Example branching_depth_nested_regression : branching_depth bb_nested = 2.
Proof. reflexivity. Qed.

Example node_count_differs_from_branching_depth :
    run_node_count bb_unary = 2 /\ branching_depth bb_unary = 0.
Proof. split; reflexivity. Qed.

Definition bb_state_left : Fin.t 2 := Fin.F1.
Definition bb_state_right : Fin.t 2 := Fin.FS Fin.F1.
Definition bb_config_left : SConfig 1 2 := (bb_state_left, bb_nvec1 3).

Example omission_selection_swap_keeps_full_configuration :
    exists retained omitted,
      OmissionSelection [bb_config_left]
        [bb_state_right; bb_state_left] retained omitted /\
      Permutation [bb_state_right] retained /\
      Permutation [bb_config_left] omitted.
Proof.
  eapply omission_selection_permutation_transport.
  - apply perm_swap.
  - apply omission_selection_omit; [cbn; auto|].
    apply omission_selection_keep. constructor.
Qed.

Check branching_depth.
Check SameTargetAndSize.
Check finite_basis_bounded_branching_depth.
Check bounded_branching_by_r_cardinality.
Check lemma_9_uniform_bounded_branching.
Check lemma_9_reach_bounded_branching_iff.
Check omission_selection_permutation_transport.
Check bad_child_r_cardinality_strict.

Print Assumptions finite_basis_bounded_branching_depth.
Print Assumptions bounded_branching_by_r_cardinality.
Print Assumptions lemma_9_uniform_bounded_branching.
Print Assumptions lemma_9_reach_bounded_branching_iff.
Print Assumptions omission_selection_permutation_transport.
