From Mell.VAS Require Import Runs Intraproductions IntraproductionsLemma57
  ProductionGraph GraphParikh EulerCycles KirchhoffRelation KirchhoffLemma515
  GraphCyclePumping KirchhoffScaling.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge.
From Coq Require Import List.

Import ListNotations.

Check CapacityTransformerCone.
Check capacity_transformer_scaled_pair_in_cone.
Check intraproduction_split_runs.
Check positive_rational_kirchhoff_uniform_scaling.
Check positive_residual_kirchhoff.
Check production_graph_cycle_realizable_after_pumping.
Check capacity_run_power_and_shift.
Check RepeatActionWord.
Check pumped_graph_cycle_iterated_run.
Check pumped_graph_cycle_iterated.
Check lemma_5_15_kirchhoff_in_capacity_cone.

Example regression_empty_word_credit_dimension_zero :
    @WordRequiredCredit 0 [] = nvec_zero 0.
Proof. reflexivity. Qed.

Example regression_repeat_word_zero : forall d (word : list (ZVec d)),
    RepeatActionWord 0 word = [].
Proof. reflexivity. Qed.

Example regression_repeat_word_successor : forall d coefficient
    (word : list (ZVec d)),
    RepeatActionWord (S coefficient) word =
      word ++ RepeatActionWord coefficient word.
Proof. reflexivity. Qed.

Example regression_dimension_zero_lemma_5_15
    (system : PlainVAS 0) (gamma : ProductionTriple 0)
    (input output : QVec 0) :
    ValidProductionTriple system gamma ->
    ProductionKirchhoffRelation system gamma input output ->
    CapacityTransformerCone system (GammaCapacity gamma) input output.
Proof. apply lemma_5_15_kirchhoff_in_capacity_cone. Qed.

Print Assumptions positive_rational_kirchhoff_uniform_scaling.
Print Assumptions positive_residual_kirchhoff.
Print Assumptions production_graph_cycle_realizable_after_pumping.
Print Assumptions pumped_graph_cycle_iterated_run.
Print Assumptions pumped_graph_cycle_iterated.
Print Assumptions production_graph_positive_kirchhoff_realized.
Print Assumptions production_graph_exact_nodup_edges.
Print Assumptions lemma_5_7_bounded_coordinates_intraproduction.
Print Assumptions lemma_5_15_kirchhoff_in_capacity_cone.
