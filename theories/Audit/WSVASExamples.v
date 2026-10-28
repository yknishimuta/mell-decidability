From Coq Require Import List.
From Mell.Core Require Import Vector.
From Mell.WSVAS Require Import System Runs RunOrder Amalgamation
  WitnessAlphabet BVASSimulation.

Import ListNotations.

Check WSVAS.
Check WSRun.
Check ValidWSRun.
Check ws_source.
Check ws_target.
Check ws_direction.
Check ws_run_length.
Check ws_run_concat.
Check ws_run_shift.
Check valid_ws_run_empty.
Check valid_ws_run_concat.
Check valid_ws_run_shift.
Check WSRunOrder.
Check lemma_c_1_wsrun_order_iff_higman.
Check corollary_c_2_wsrun_wqo.
Check ws_run_order_refl.
Check ws_run_order_trans.
Check amalgamate_ws_gaps.
Check ws_run_order_stitch.
Check lemma_c_4_wsrun_exact_amalgamation.
Check lemma_5_2_wsvas_runs_wqo_amalgamation.
Check corollary_5_3_wsvas_run_scaling.
Check WitnessAlphabet.
Check witness_value.
Check witness_alphabet_wqo.
Check witness_alphabet_diamond.
Check ConcreteTransition.
Check concrete_wsvas.
Check BVASSideStep.
Check bvas_side_step_occurrences.
Check concrete_transition_step_apply_iff.
Check lemma_5_6_bvas_wsvas_step_iff.
Check ValidFreeIRun.
Check free_irun_sources.
Check SourceShuffle.
Check MarkedFreeIRun.
Check marked_free_source_shuffle.
Check marked_free_irun_iff_source_shuffle.
Check marked_reach_iff_reach_from_shuffle.
Check ClosedUnderFreeRuns.
Check lemma_5_5_bvas_wsvas_reach_iff.

Section WSVASRegression.
  Context {d : nat} (system : WSVAS d) (configuration : NVec d).

  Example zero_transition_run_is_valid :
    ValidWSRun (empty_ws_run (system := system) configuration).
  Proof. apply valid_ws_run_empty. Qed.

  Example zero_transition_run_has_empty_higman_word :
    encode_ws_run (empty_ws_run (system := system) configuration) = [].
  Proof. reflexivity. Qed.

  Example zero_transition_run_keeps_both_endpoints :
    ws_direction (empty_ws_run (system := system) configuration) =
      (configuration, configuration).
  Proof. reflexivity. Qed.
End WSVASRegression.

Section SourceOccurrenceRegression.
  Context {d : nat} (value : NVec d).

  Example special_leaf_may_also_belong_to_invariant :
    SourceShuffle (fun x => x = value) (fun x => x = value) [value].
  Proof.
    exists [], value, []. split; [reflexivity|]. split; [reflexivity|].
    split; constructor.
  Qed.

  Example duplicate_equal_leaves_remain_occurrences :
    SourceShuffle (fun x => x = value) (fun x => x = value) [value; value].
  Proof.
    exists [], value, [value]. split; [reflexivity|]. split; [reflexivity|].
    split; [constructor|]. constructor; [reflexivity|constructor].
  Qed.
End SourceOccurrenceRegression.

Print Assumptions lemma_c_4_wsrun_exact_amalgamation.
Print Assumptions corollary_5_3_wsvas_run_scaling.
Print Assumptions witness_alphabet_wqo.
Print Assumptions witness_alphabet_diamond.
Print Assumptions lemma_5_6_bvas_wsvas_step_iff.
Print Assumptions lemma_5_5_bvas_wsvas_reach_iff.
Print Assumptions marked_free_irun_iff_source_shuffle.
