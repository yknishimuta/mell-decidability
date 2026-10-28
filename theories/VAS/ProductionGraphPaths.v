From Coq Require Import Arith Fin Lia List Vector VectorSpec Classical_Prop.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.VAS Require Import Runs Intraproductions IntraproductionsLemma57
  ProductionGraph.

Import ListNotations.

Inductive ProductionGraphPath {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness : NVec d) :
    NVec d -> NVec d -> list (ZVec d) -> Prop :=
| production_graph_path_refl : forall state,
    ProductionGraphPath system gamma witness state state []
| production_graph_path_step : forall source middle target action word,
    ProductionGraphTransition system gamma witness source action middle ->
    ProductionGraphPath system gamma witness middle target word ->
    ProductionGraphPath system gamma witness source target (action :: word).

Lemma ProductionGraphPath_refl : forall d system gamma witness state,
    @ProductionGraphPath d system gamma witness state state [].
Proof. constructor. Qed.

Lemma ProductionGraphPath_append : forall d system gamma witness
    source middle target left right,
    @ProductionGraphPath d system gamma witness source middle left ->
    ProductionGraphPath system gamma witness middle target right ->
    ProductionGraphPath system gamma witness source target (left ++ right).
Proof.
  intros d system gamma witness source middle target left right Hleft.
  induction Hleft; intro Hright; cbn; [exact Hright|].
  econstructor; eauto.
Qed.

Lemma ProductionGraphPath_split : forall d system gamma witness
    source target left right,
    @ProductionGraphPath d system gamma witness source target (left ++ right) ->
    exists middle,
      ProductionGraphPath system gamma witness source middle left /\
      ProductionGraphPath system gamma witness middle target right.
Proof.
  intros d system gamma witness source target left.
  revert source. induction left as [|action tail IH]; intros source right Hpath.
  - cbn in Hpath. exists source. split; [constructor|exact Hpath].
  - cbn in Hpath. inversion Hpath as [|s m t a w Hedge Hrest]; subst.
    destruct (IH _ _ Hrest) as [middle [Hprefix Hsuffix]].
    exists middle. split; [econstructor; eauto|exact Hsuffix].
Qed.

Lemma project_bounded_add_intraproduction : forall d system gamma witness
    configuration increment,
    @Lemma57Witness d system gamma witness ->
    IntraProduction system gamma increment ->
    ProjectBounded witness (nvec_add configuration increment) =
      ProjectBounded witness configuration.
Proof.
  intros d system gamma witness configuration increment [_ Hmask] Hintra.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  repeat rewrite project_bounded_nth.
  destruct (Nat.eqb (Vector.nth witness index) 0) eqn:Heq.
  - apply Nat.eqb_eq in Heq.
    pose proof (bounded_coordinate_intraproduction_zero d system gamma
      index increment ((proj2 (Hmask index)) Heq) Hintra) as Hz.
    unfold nvec_add.
    rewrite (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl), Hz.
    lia.
  - reflexivity.
Qed.

Lemma run_edge_trace_actions : forall d source targets,
    List.map RunEdgeAction (@run_edge_trace d source targets) =
    List.map fst (steps_of_targets source targets).
Proof. intros d source targets. revert source. induction targets; intros; cbn;
  [reflexivity|now rewrite IHtargets]. Qed.

Lemma projected_targets_path : forall (d : nat) (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness : NVec d) (original : VASRun d)
    (current : NVec d) (targets : list (NVec d)),
    OmegaGamma system gamma original ->
    ValidVASTargets system current targets ->
    (forall edge, List.In edge (run_edge_trace current targets) ->
      List.In edge (run_edge_trace (RunSource original) (RunTargets original))) ->
    ProductionGraphPath system gamma witness
      (ProjectBounded witness current)
      (ProjectBounded witness (targets_target current targets))
      (List.map RunEdgeAction (run_edge_trace current targets)).
Proof.
  intros d system gamma witness original current targets Homega Hvalid Hsub.
  revert current Hvalid Hsub. induction targets as [|next tail IH];
    intros current Hvalid Hsub; cbn in *; [constructor|].
  destruct Hvalid as [Hstep Htail]. econstructor.
  - exists original, current, next. split; [exact Homega|]. split.
    + apply Hsub. now left.
    + split; [split; [exact Hstep|reflexivity]|]. split; reflexivity.
  - apply IH; [exact Htail|]. intros edge Hin. apply Hsub. now right.
Qed.

Theorem omega_run_projects_to_graph_path : forall d system gamma witness run,
    @OmegaGamma d system gamma run ->
    ProductionGraphPath system gamma witness
      (ProjectBounded witness (RunSource run))
      (ProjectBounded witness (RunTarget run))
      (RunActionWord run).
Proof.
  intros d system gamma witness [source targets] Homega.
  unfold RunActionWord, RunSteps. rewrite <- run_edge_trace_actions.
  apply projected_targets_path with
    (original := {| RunSource := source; RunTargets := targets |});
    try exact Homega.
  - exact (proj1 Homega).
  - intros; assumption.
Qed.

Theorem corollary_5_9_omega_endpoints_special : forall d system gamma witness
    run,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    OmegaGamma system gamma run ->
    ProjectBounded witness (RunSource run) =
      ProductionGraphSpecialState gamma witness /\
    ProjectBounded witness (RunTarget run) =
      ProductionGraphSpecialState gamma witness.
Proof.
  intros d system gamma witness run _ Hw
    [Hvalid [multiplier [Hsource Htarget]]].
  assert (Hreach : PlainVASReach system (RunSource run) (RunTarget run)).
  { destruct run as [source targets]. cbn in *. now apply valid_targets_reach. }
  assert (Hinput : IntraProduction system gamma
      (nvec_scale multiplier (GammaInput gamma))).
  { exists multiplier. rewrite <- Hsource, <- Htarget. split;
      [constructor|exact Hreach]. }
  assert (Houtput : IntraProduction system gamma
      (nvec_scale multiplier (GammaOutput gamma))).
  { exists multiplier. rewrite <- Hsource, <- Htarget. split;
      [exact Hreach|constructor]. }
  split.
  - rewrite Hsource. exact (project_bounded_add_intraproduction d system gamma
      witness (GammaCapacity gamma) _ Hw Hinput).
  - rewrite Htarget. exact (project_bounded_add_intraproduction d system gamma
      witness (GammaCapacity gamma) _ Hw Houtput).
Qed.

Theorem omega_run_projects_to_special_cycle : forall d system gamma witness run,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    OmegaGamma system gamma run ->
    ProductionGraphPath system gamma witness
      (ProductionGraphSpecialState gamma witness)
      (ProductionGraphSpecialState gamma witness)
      (RunActionWord run).
Proof.
  intros d system gamma witness run Hvalid Hw Homega.
  pose proof (omega_run_projects_to_graph_path d system gamma witness run
    Homega) as Hpath.
  destruct (corollary_5_9_omega_endpoints_special d system gamma witness run
    Hvalid Hw Homega) as [Hs Ht]. now rewrite Hs, Ht in Hpath.
Qed.

Lemma projected_targets_split_at_occurrence : forall (d : nat)
    (system : PlainVAS d) (gamma : ProductionTriple d) (witness : NVec d)
    (original : VASRun d) (current : NVec d) (targets : list (NVec d))
    (configuration : NVec d),
    OmegaGamma system gamma original ->
    ValidVASTargets system current targets ->
    (forall edge, List.In edge (run_edge_trace current targets) ->
      List.In edge (run_edge_trace (RunSource original) (RunTargets original))) ->
    List.In configuration (current :: targets) ->
    exists prefix suffix,
      ProductionGraphPath system gamma witness
        (ProjectBounded witness current) (ProjectBounded witness configuration)
        prefix /\
      ProductionGraphPath system gamma witness
        (ProjectBounded witness configuration)
        (ProjectBounded witness (targets_target current targets)) suffix.
Proof.
  intros d system gamma witness original current targets configuration
    Homega Hvalid Hsub Hin.
  revert current Hvalid Hsub Hin. induction targets as [|next tail IH];
    intros current Hvalid Hsub Hin; cbn in Hin.
  - destruct Hin as [->|[]]. exists [], []. split; constructor.
  - destruct Hvalid as [Hstep Htail]. destruct Hin as [Heq|Hin].
    + subst configuration.
      exists [], (List.map RunEdgeAction (run_edge_trace current (next :: tail))).
      split; [constructor|].
      eapply projected_targets_path with (original := original).
      * exact Homega.
      * cbn. split; assumption.
      * exact Hsub.
    + destruct (IH next Htail (fun edge Hedge => Hsub edge (or_intror Hedge))
        Hin) as [prefix [suffix [Hprefix Hsuffix]]].
      exists (StepAction current next :: prefix), suffix. split; [|exact Hsuffix].
      econstructor; [|exact Hprefix].
      exists original, current, next. split; [exact Homega|]. split.
      * apply Hsub. now left.
      * split; [split; [exact Hstep|reflexivity]|]. split; reflexivity.
Qed.

Lemma omega_occurrence_special_paths : forall d system gamma witness run q,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    OmegaGamma system gamma run -> RunOccurs q run ->
    exists prefix suffix,
      ProductionGraphPath system gamma witness
        (ProductionGraphSpecialState gamma witness) (ProjectBounded witness q)
        prefix /\
      ProductionGraphPath system gamma witness
        (ProjectBounded witness q) (ProductionGraphSpecialState gamma witness)
        suffix.
Proof.
  intros d system gamma witness [source targets] q Hvalid Hw Homega Hoccurs.
  destruct (projected_targets_split_at_occurrence d system gamma witness
    {| RunSource := source; RunTargets := targets |} source targets q Homega
    (proj1 Homega) (fun edge Hedge => Hedge) Hoccurs)
    as [prefix [suffix [Hprefix Hsuffix]]].
  destruct (corollary_5_9_omega_endpoints_special d system gamma witness
    {| RunSource := source; RunTargets := targets |} Hvalid Hw Homega)
    as [Hs Ht]. cbn in Hs, Ht. exists prefix, suffix.
  now rewrite Hs in Hprefix; rewrite Ht in Hsuffix.
Qed.

Theorem corollary_5_10_production_graph_strongly_connected : forall d
    system gamma witness source target,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    ProductionGraphState system gamma witness source ->
    ProductionGraphState system gamma witness target ->
    exists word,
      ProductionGraphPath system gamma witness source target word.
Proof.
  intros d system gamma witness source target Hvalid Hw
    [q [Hq ->]] [q' [Hq' ->]].
  apply qgamma_iff_occurs_in_omega in Hq as [run [Homega Hoccurs]].
  apply qgamma_iff_occurs_in_omega in Hq' as [run' [Homega' Hoccurs']].
  destruct (omega_occurrence_special_paths d system gamma witness run q
    Hvalid Hw Homega Hoccurs) as [to_q [from_q [_ Hfrom_q]]].
  destruct (omega_occurrence_special_paths d system gamma witness run' q'
    Hvalid Hw Homega' Hoccurs') as [to_q' [from_q' [Hto_q' _]]].
  exists (from_q ++ to_q'). eapply ProductionGraphPath_append; eauto.
Qed.

Theorem production_graph_path_witness_independent : forall d system gamma
    left right,
    @Lemma57Witness d system gamma left -> Lemma57Witness system gamma right ->
    forall source target word,
      ProductionGraphPath system gamma left source target word <->
      ProductionGraphPath system gamma right source target word.
Proof.
  intros d system gamma left right Hl Hr source target word. split; intro Hpath.
  - induction Hpath; [constructor|econstructor; eauto].
    apply (proj1 (production_graph_transition_witness_independent
      d system gamma left right Hl Hr _ _ _)); assumption.
  - induction Hpath; [constructor|econstructor; eauto].
    apply (proj2 (production_graph_transition_witness_independent
      d system gamma left right Hl Hr _ _ _)); assumption.
Qed.
