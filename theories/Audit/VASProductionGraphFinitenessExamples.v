From Mell.VAS Require Import ProductionGraphFiniteness.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Order Require Import AlmostFullBridge.
From Mell.VAS Require Import Runs Intraproductions ProductionGraph.
From Coq Require Import List Vector.

Import ListNotations.

Check BoundedMask.
Check all_bounded_masks_complete.
Check production_graph_common_special_state.
Check projected_step_deterministic_across_graphs.
Check projected_step_bounded_coordinate_equation.
Check projected_step_unbounded_coordinate_zero.
Check production_graph_word_determines_projected_trace.
Check production_graph_word_prefix_deterministic_across_graphs.
Check production_graph_simple_path_from_special.
Check simple_production_graph_path_bad.
Check finite_branching_af_bad_paths_bounded.
Check fixed_mask_simple_path_uniform_bound.
Check fixed_mask_production_states_uniform_finite.
Check fixed_capacity_production_states_uniform_finite.
Check fixed_capacity_production_transitions_uniform_finite.
Check GraphSignatureRepresents.
Check graph_signature_witness_independent.
Check corollary_5_12_production_graph_class_finite.

Example task4b_dimension_zero_mask :
    all_bounded_masks 0 = [@Vector.nil bool].
Proof. reflexivity. Qed.

Example task4b_one_dimensional_masks :
    List.In (@Vector.cons bool true 0 (@Vector.nil bool))
      (all_bounded_masks 1) /\
    List.In (@Vector.cons bool false 0 (@Vector.nil bool))
      (all_bounded_masks 1).
Proof. cbn. tauto. Qed.

Example task4b_empty_action_bad_paths_bounded :
    exists bound : nat,
      forall word : list (ZVec 0),
        List.Forall (fun action => List.In action []) word ->
        ForwardBad (@nvec_le 0)
          (FiniteBranchTrace
            (ProjectedActionTarget (@Vector.nil bool))
            (@Vector.nil nat) word) ->
        List.length word <= bound.
Proof.
  eapply finite_branching_af_bad_paths_bounded.
  apply nvec_le_almost_full.
Qed.

Example task4b_duplicate_action_alphabet_bad_paths_bounded :
    forall (action : ZVec 0),
      exists bound : nat,
        forall word : list (ZVec 0),
          List.Forall (fun label => List.In label [action; action]) word ->
          ForwardBad (@nvec_le 0)
            (FiniteBranchTrace
              (ProjectedActionTarget (@Vector.nil bool))
              (@Vector.nil nat) word) ->
          List.length word <= bound.
Proof.
  intro action. eapply finite_branching_af_bad_paths_bounded.
  apply nvec_le_almost_full.
Qed.

Example task4b_catalog_covers_zero_dimension :
    forall (system : PlainVAS 0) (capacity : NVec 0),
      exists graph_catalog : list (ProductionGraphSignature 0),
        forall gamma,
          ValidProductionTriple system gamma ->
          GammaCapacity gamma = capacity ->
          exists witness signature,
            Lemma57Witness system gamma witness /\
            List.In signature graph_catalog /\
            GraphSignatureRepresents signature system gamma witness.
Proof. apply corollary_5_12_production_graph_class_finite. Qed.

Print Assumptions projected_step_deterministic_across_graphs.
Print Assumptions finite_branching_af_bad_paths_bounded.
Print Assumptions fixed_mask_simple_path_uniform_bound.
Print Assumptions fixed_capacity_production_states_uniform_finite.
Print Assumptions fixed_capacity_production_transitions_uniform_finite.
Print Assumptions graph_signature_witness_independent.
Print Assumptions corollary_5_12_production_graph_class_finite.
Print All Dependencies corollary_5_12_production_graph_class_finite.
