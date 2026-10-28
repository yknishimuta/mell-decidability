From Coq Require Import List.
From Mell.Core Require Import Vector.
From Mell.BVASS Require Import Stateful.
From Mell.Reduction Require Import FullZeroSystem ZeroTestFree.
From Mell.Reduction Require Import Main.

Import ListNotations.

Check zero_test_freeb.
Check zero_test_freeb_spec.
Check direct_bottom_up.
Check direct_root_state.
Check direct_zero_test_free_correct.
Check reduce_mell_reference.
Check reduce_mell_optimized_correct_reference.

Definition direct_d0_leaf_system : FullZeroBVASS 0 bool :=
  {| full_zero_leaves := [true];
     full_zero_unary_rules := [];
     full_zero_split_rules := [];
     full_zero_test_rules := [] |}.

Example direct_d0_leaf_is_zero_test_free :
  zero_test_freeb direct_d0_leaf_system = true.
Proof. reflexivity. Qed.

Example direct_d0_leaf_reaches :
  SReach (direct_bottom_up Bool.bool_dec direct_d0_leaf_system)
    (direct_root_state Bool.bool_dec direct_d0_leaf_system true)
    (nvec_zero 0).
Proof.
  apply (proj1 (direct_zero_test_free_correct
    0 bool Bool.bool_dec direct_d0_leaf_system true (nvec_zero 0)
    eq_refl ltac:(cbn; auto))).
  constructor. cbn. auto.
Qed.

Print Assumptions direct_zero_test_free_correct.
