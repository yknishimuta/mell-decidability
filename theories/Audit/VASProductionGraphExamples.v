From Coq Require Import Fin Lia List Vector VectorSpec ZArith.
From Mell.BVAS Require Import RunOrder.
From Mell.VAS Require Import Runs Intraproductions ProductionGraph
  ProductionGraphPaths.
From Mell.Audit Require Import VASIntraproductionsExamples
  VASIntraproductionsLemma57Examples.

Import ListNotations.

Check ProjectBounded.
Check Lemma57Witness.
Check ProductionGraphState.
Check ProductionGraphSpecialState.
Check RunAdjacentStep.
Check ProductionGraphTransition.
Check ProductionGraphPath.
Check omega_run_projects_to_graph_path.
Check corollary_5_9_omega_endpoints_special.
Check omega_run_projects_to_special_cycle.
Check corollary_5_10_production_graph_strongly_connected.
Check corollary_5_11_projected_states_antichain.
Check production_graph_states_finite.
Check production_graph_transitions_finite.
Check finite_production_graph_exists.
Check project_bounded_witness_independent.
Check production_graph_state_witness_independent.
Check production_graph_transition_witness_independent.
Check production_graph_path_witness_independent.
Check production_graph_special_state_witness_independent.

Example production_graph_dimension_zero (system : PlainVAS 0)
    (gamma : ProductionTriple 0) :
    ValidProductionTriple system gamma ->
    exists witness states transitions,
      Lemma57Witness system gamma witness /\
      (forall state,
        ProductionGraphState system gamma witness state <->
        List.In state states) /\
      (forall source action target,
        ProductionGraphTransition system gamma witness source action target <->
        List.In {| RunEdgeSource := source;
                   RunEdgeAction := action;
                   RunEdgeTarget := target |} transitions).
Proof. apply finite_production_graph_exists. Qed.

Lemma production_graph_unbounded_witness_one :
    Lemma57Witness intra_plus_one_system intra_unbounded_gamma (intra_n1 1).
Proof.
  split; [apply intra_unbounded_hgamma|]. intro index.
  refine (Fin.caseS' index (fun index =>
    BoundedGammaCoordinate intra_plus_one_system intra_unbounded_gamma index <->
    Vector.nth (intra_n1 1) index = 0%nat) _ _).
  - cbn. split; [intro Hbounded; exfalso; exact (lemma57_unbounded_coordinate Hbounded)|lia].
  - intro impossible. inversion impossible.
Qed.

Lemma production_graph_unbounded_witness_two :
    Lemma57Witness intra_plus_one_system intra_unbounded_gamma (intra_n1 2).
Proof.
  split; [apply intra_unbounded_hgamma|]. intro index.
  refine (Fin.caseS' index (fun index =>
    BoundedGammaCoordinate intra_plus_one_system intra_unbounded_gamma index <->
    Vector.nth (intra_n1 2) index = 0%nat) _ _).
  - cbn. split; [intro Hbounded; exfalso; exact (lemma57_unbounded_coordinate Hbounded)|lia].
  - intro impossible. inversion impossible.
Qed.

Example production_graph_all_unbounded_projection :
    ProjectBounded (intra_n1 1) (intra_n1 37) = intra_n1 0.
Proof. reflexivity. Qed.

Example production_graph_mixed_projection :
    ProjectBounded (intra_n2 0 1) (intra_n2 5 37) = intra_n2 5 0.
Proof. reflexivity. Qed.

Example production_graph_witness_projection_independent :
    forall configuration,
      ProjectBounded (intra_n1 1) configuration =
      ProjectBounded (intra_n1 2) configuration.
Proof.
  apply project_bounded_witness_independent with
    (system := intra_plus_one_system) (gamma := intra_unbounded_gamma);
    [exact production_graph_unbounded_witness_one|
     exact production_graph_unbounded_witness_two].
Qed.

Example production_graph_plus_one_special_cycle :
    ProductionGraphPath intra_plus_one_system intra_unbounded_gamma
      (intra_n1 1)
      (ProductionGraphSpecialState intra_unbounded_gamma (intra_n1 1))
      (ProductionGraphSpecialState intra_unbounded_gamma (intra_n1 1))
      (RunActionWord intra_plus_one_run).
Proof.
  eapply omega_run_projects_to_special_cycle.
  - exact intra_unbounded_gamma_valid.
  - exact production_graph_unbounded_witness_one.
  - exact intra_omega_common_multiplier.
Qed.

Example production_graph_empty_special_cycle :
    ProductionGraphPath intra_plus_one_system intra_unbounded_gamma
      (intra_n1 1)
      (ProductionGraphSpecialState intra_unbounded_gamma (intra_n1 1))
      (ProductionGraphSpecialState intra_unbounded_gamma (intra_n1 1)) [].
Proof.
  change (ProductionGraphPath intra_plus_one_system intra_unbounded_gamma
    (intra_n1 1)
    (ProductionGraphSpecialState intra_unbounded_gamma (intra_n1 1))
    (ProductionGraphSpecialState intra_unbounded_gamma (intra_n1 1))
    (RunActionWord
      (EmptyVASRun (GammaCapacity intra_unbounded_gamma)))).
  eapply omega_run_projects_to_special_cycle.
  - exact intra_unbounded_gamma_valid.
  - exact production_graph_unbounded_witness_one.
  - exact intra_omega_zero_run.
Qed.

Example production_graph_plus_one_strongly_connected :
    forall source target,
      ProductionGraphState intra_plus_one_system intra_unbounded_gamma
        (intra_n1 1) source ->
      ProductionGraphState intra_plus_one_system intra_unbounded_gamma
        (intra_n1 1) target ->
      exists word,
        ProductionGraphPath intra_plus_one_system intra_unbounded_gamma
          (intra_n1 1) source target word.
Proof.
  intros. eapply corollary_5_10_production_graph_strongly_connected; eauto.
  - exact intra_unbounded_gamma_valid.
  - exact production_graph_unbounded_witness_one.
Qed.

Example production_graph_plus_one_antichain :
    forall source target,
      ProductionGraphState intra_plus_one_system intra_unbounded_gamma
        (intra_n1 1) source ->
      ProductionGraphState intra_plus_one_system intra_unbounded_gamma
        (intra_n1 1) target ->
      nvec_le source target -> source = target.
Proof.
  intros. eapply corollary_5_11_projected_states_antichain; eauto.
  - exact intra_unbounded_gamma_valid.
  - exact production_graph_unbounded_witness_one.
Qed.

Example production_graph_plus_one_finite :
    exists states transitions,
      (forall state,
        ProductionGraphState intra_plus_one_system intra_unbounded_gamma
          (intra_n1 1) state <-> List.In state states) /\
      (forall source action target,
        ProductionGraphTransition intra_plus_one_system intra_unbounded_gamma
          (intra_n1 1) source action target <->
        List.In {| RunEdgeSource := source;
                   RunEdgeAction := action;
                   RunEdgeTarget := target |} transitions).
Proof.
  destruct (production_graph_states_finite _ _ _ _
    intra_unbounded_gamma_valid production_graph_unbounded_witness_one)
    as [states Hstates].
  destruct (production_graph_transitions_finite _ _ _ _
    intra_unbounded_gamma_valid production_graph_unbounded_witness_one)
    as [transitions Htransitions].
  exists states, transitions. split; assumption.
Qed.

Print Assumptions corollary_5_9_omega_endpoints_special.
Print Assumptions corollary_5_10_production_graph_strongly_connected.
Print Assumptions corollary_5_11_projected_states_antichain.
Print Assumptions production_graph_states_finite.
Print Assumptions production_graph_transitions_finite.
Print Assumptions finite_production_graph_exists.
Print Assumptions project_bounded_witness_independent.
