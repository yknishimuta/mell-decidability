From Coq Require Import List Vector ZArith.
From Mell.Core Require Import Vector FiniteTree.
From Mell.BVAS Require Import System Runs Contexts.
From Mell.BVASS Require Import Stateful.
From Mell.Order Require Import FiniteBasis CountableFiniteBasis.
From Mell.BVAS Require Import Code.
From Mell.BVASS Require Import Code.

Import ListNotations.

Set Printing Implicit.

Check irun_le_finite_cover.
Check context_order_finite_cover.
Check countable_af_finite_cover.

Definition t10g_nvec0 : NVec 0 := @Vector.nil nat.
Definition t10g_zvec0 : ZVec 0 := @Vector.nil Z.

Definition t10g_irun_system : IBVAS 0 :=
  {| initial_vectors := [t10g_nvec0]; system_actions := [] |}.

Example t10g_zero_dimension_leaf_enumerates :
    enumerate_irun t10g_irun_system (encode_run (tree_leaf 0)) =
      Some (irun_leaf t10g_nvec0).
Proof. reflexivity. Qed.

Example t10g_invalid_leaf_code_rejected :
    enumerate_irun ({| initial_vectors := []; system_actions := [] |} : IBVAS 0)
      (encode_run (tree_leaf 0)) = None.
Proof. reflexivity. Qed.

Example t10g_leaf_order_decides_true :
    irun_leb (irun_leaf t10g_nvec0) (irun_leaf t10g_nvec0) = true.
Proof. reflexivity. Qed.

Definition t10g_q : Fin.t 2 := Fin.F1.
Definition t10g_r : Fin.t 2 := Fin.FS Fin.F1.

Definition t10g_rule_qr : SRule 0 2 :=
  {| input_states := [t10g_q; t10g_r];
     input_nonempty := ltac:(discriminate);
     output_state := t10g_q;
     rule_delta := t10g_zvec0 |}.

Definition t10g_permutation_system : SBVAS 0 2 :=
  {| initial_configs := [(t10g_q, t10g_nvec0); (t10g_r, t10g_nvec0)];
     stateful_rules := [t10g_rule_qr] |}.

Definition t10g_permuted_raw : RawRun :=
  tree_node 0
    (forest_cons (tree_leaf 1)
      (forest_cons (tree_leaf 0) forest_nil)).

Example t10g_permuted_children_enumerate :
    exists run, enumerate_srun t10g_permutation_system
      (encode_run t10g_permuted_raw) = Some run.
Proof. vm_compute. eexists. reflexivity. Qed.

Definition t10g_rule_qq : SRule 0 2 :=
  {| input_states := [t10g_q; t10g_q];
     input_nonempty := ltac:(discriminate);
     output_state := t10g_q;
     rule_delta := t10g_zvec0 |}.

Definition t10g_duplicate_system : SBVAS 0 2 :=
  {| initial_configs := [(t10g_q, t10g_nvec0)];
     stateful_rules := [t10g_rule_qq] |}.

Definition t10g_duplicate_raw : RawRun :=
  tree_node 0
    (forest_cons (tree_leaf 0)
      (forest_cons (tree_leaf 0) forest_nil)).

Example t10g_duplicate_children_enumerate :
    exists run, enumerate_srun t10g_duplicate_system
      (encode_run t10g_duplicate_raw) = Some run.
Proof. vm_compute. eexists. reflexivity. Qed.

Definition t10g_empty_stateful : SBVAS 0 0 :=
  {| initial_configs := []; stateful_rules := [] |}.

Example t10g_zero_state_vacuity_rejects :
    enumerate_srun t10g_empty_stateful (encode_run (tree_leaf 0)) = None.
Proof. reflexivity. Qed.

Print Assumptions almost_full_finite_cover.

Goal True.
  idtac "T10_G_CONCRETE_ASSUMPTIONS".
  exact I.
Qed.

Print Assumptions irun_le_finite_cover.
Print Assumptions context_order_finite_cover.
Print Assumptions countable_af_finite_cover.
