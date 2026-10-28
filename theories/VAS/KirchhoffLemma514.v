From Coq Require Import Arith Fin Lia List Vector Vectors.VectorSpec ZArith QArith Qring.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore RationalHToV.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.VAS Require Import Runs Transformer Intraproductions
  IntraproductionsLemma57 ProductionGraph ProductionGraphPaths GraphParikh
  Kirchhoff EulerCycles KirchhoffRelation KirchhoffDefinability.

Import ListNotations.
Open Scope Q_scope.

Definition ProjectRunEdge {d} (witness : NVec d)
    (edge : ProductionGraphEdge d) : ProductionGraphEdge d :=
  {| RunEdgeSource := ProjectBounded witness (RunEdgeSource edge);
     RunEdgeAction := RunEdgeAction edge;
     RunEdgeTarget := ProjectBounded witness (RunEdgeTarget edge) |}.

Definition ProjectedRunEdgeTrace {d} (witness : NVec d) (run : VASRun d) :=
  List.map (ProjectRunEdge witness)
    (run_edge_trace (RunSource run) (RunTargets run)).

Lemma projected_targets_edge_trace : forall d system gamma witness original
    current targets,
    @OmegaGamma d system gamma original ->
    ValidVASTargets system current targets ->
    (forall edge, List.In edge (run_edge_trace current targets) ->
      List.In edge (run_edge_trace (RunSource original) (RunTargets original))) ->
    ProductionGraphEdgeTrace system gamma witness
      (ProjectBounded witness current)
      (ProjectBounded witness (targets_target current targets))
      (List.map (ProjectRunEdge witness) (run_edge_trace current targets)).
Proof.
  intros d system gamma witness original current targets Homega Hvalid Hsub.
  revert current Hvalid Hsub. induction targets as [|next tail IH];
    intros current Hvalid Hsub; cbn in *.
  - split; constructor.
  - destruct Hvalid as [Hstep Htail].
    assert (Hprojected_tail := IH next Htail (fun edge Hin => Hsub edge (or_intror Hin))).
    split.
    + change (GraphEdgeTrace
        (RunEdgeSource (ProjectRunEdge witness
          {| RunEdgeSource := current; RunEdgeAction := StepAction current next;
             RunEdgeTarget := next |}))
        (ProjectBounded witness (targets_target next tail))
        (ProjectRunEdge witness
          {| RunEdgeSource := current; RunEdgeAction := StepAction current next;
             RunEdgeTarget := next |} ::
         List.map (ProjectRunEdge witness) (run_edge_trace next tail))).
      constructor. exact (proj1 Hprojected_tail).
    + constructor.
      * exists original, current, next.
        refine (conj Homega (conj _ (conj _ (conj eq_refl eq_refl)))).
        -- apply Hsub. now left.
        -- split; [exact Hstep|reflexivity].
      * exact (proj2 Hprojected_tail).
Qed.

Lemma omega_run_projects_to_special_edge_cycle : forall d system gamma witness run,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    OmegaGamma system gamma run ->
    ProductionGraphEdgeTrace system gamma witness
      (ProductionGraphSpecialState gamma witness)
      (ProductionGraphSpecialState gamma witness)
      (ProjectedRunEdgeTrace witness run) /\
    GraphTraceActionWord (ProjectedRunEdgeTrace witness run) = RunActionWord run.
Proof.
  intros d system gamma witness [source targets] Hvalid Hw Homega.
  unfold ProjectedRunEdgeTrace.
  pose proof (projected_targets_edge_trace d system gamma witness
    {| RunSource := source; RunTargets := targets |} source targets Homega
    (proj1 Homega) (fun edge Hin => Hin)) as Htrace.
  destruct (corollary_5_9_omega_endpoints_special d system gamma witness
    {| RunSource := source; RunTargets := targets |} Hvalid Hw Homega) as [Hs Ht].
  cbn in Hs, Ht. rewrite Hs, Ht in Htrace. split; [exact Htrace|].
  unfold GraphTraceActionWord. rewrite List.map_map.
  unfold ProjectRunEdge. cbn. rewrite run_edge_trace_actions. reflexivity.
Qed.

Lemma production_graph_edge_has_omega_cycle : forall d system gamma witness edges edge,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    ExactProductionGraphEdges system gamma witness edges ->
    List.In edge edges ->
    exists run multiplier trace,
      OmegaGamma system gamma run /\
      RunSource run = nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaInput gamma)) /\
      RunTarget run = nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaOutput gamma)) /\
      ProductionGraphEdgeTrace system gamma witness
        (ProductionGraphSpecialState gamma witness)
        (ProductionGraphSpecialState gamma witness) trace /\
      List.In edge trace /\
      GraphTraceActionWord trace = RunActionWord run.
Proof.
  intros d system gamma witness edges [source action target] Hvalid Hw
    [_ Hexact] Hin.
  apply <- Hexact in Hin.
  destruct Hin as [run [configuration [next [Homega [Hadj
    [Hstep [Hsource Htarget]]]]]]].
  destruct Homega as [Hrun [multiplier [Hrun_source Hrun_target]]].
  exists run, multiplier, (ProjectedRunEdgeTrace witness run).
  set (Homega' := conj Hrun (ex_intro _ multiplier
    (conj Hrun_source Hrun_target)) : OmegaGamma system gamma run).
  refine (conj Homega' (conj Hrun_source (conj Hrun_target
    (conj _ (conj _ _))))).
  - apply (proj1 (omega_run_projects_to_special_edge_cycle d system gamma witness
      run Hvalid Hw Homega')).
  - unfold ProjectedRunEdgeTrace. apply in_map_iff.
    exists {| RunEdgeSource := configuration; RunEdgeAction := action;
              RunEdgeTarget := next |}. split.
    + unfold ProjectRunEdge. cbn. now rewrite <- Hsource, <- Htarget.
    + exact Hadj.
  - apply (proj2 (omega_run_projects_to_special_edge_cycle d system gamma witness
      run Hvalid Hw Homega')).
Qed.

Definition GammaDirection {d} (gamma : ProductionTriple d) : ZVec d :=
  zvec_sub_run (nvec_to_zvec (GammaOutput gamma))
    (nvec_to_zvec (GammaInput gamma)).

Lemma nvec_to_zvec_add_scale_nth : forall d (capacity value : NVec d)
    multiplier (index : Fin.t d),
    Vector.nth (nvec_to_zvec (nvec_add capacity (nvec_scale multiplier value)))
      index =
    (Z.of_nat (Vector.nth capacity index) +
     Z.of_nat multiplier * Z.of_nat (Vector.nth value index))%Z.
Proof.
  intros. unfold nvec_to_zvec, nvec_add, nvec_scale.
  rewrite (nth_map Z.of_nat _ index index eq_refl),
    (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (nth_map (Nat.mul multiplier) _ index index eq_refl),
    Nat2Z.inj_add, Nat2Z.inj_mul. reflexivity.
Qed.

Lemma gamma_direction_nth : forall d (gamma : ProductionTriple d)
    (index : Fin.t d),
    Vector.nth (GammaDirection gamma) index =
      (Z.of_nat (Vector.nth (GammaOutput gamma) index) -
       Z.of_nat (Vector.nth (GammaInput gamma) index))%Z.
Proof.
  intros. unfold GammaDirection, zvec_sub_run, nvec_to_zvec.
  rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl),
    (nth_map Z.of_nat (GammaOutput gamma) index index eq_refl),
    (nth_map Z.of_nat (GammaInput gamma) index index eq_refl). reflexivity.
Qed.

Lemma omega_run_action_displacement : forall d system gamma run multiplier,
    @OmegaGamma d system gamma run ->
    RunSource run = nvec_add (GammaCapacity gamma)
      (nvec_scale multiplier (GammaInput gamma)) ->
    RunTarget run = nvec_add (GammaCapacity gamma)
      (nvec_scale multiplier (GammaOutput gamma)) ->
    ActionDisplacement (RunActionWord run) =
      zvec_scale_nat multiplier (GammaDirection gamma).
Proof.
  intros d system gamma run multiplier [Hvalid _] Hsource Htarget.
  pose proof (valid_run_target_displacement d system run Hvalid) as Hdisp.
  rewrite Hsource, Htarget in Hdisp.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index index' Heq; subst index'.
  pose proof (f_equal (fun value : ZVec d => Vector.nth value index) Hdisp) as Hnth.
  unfold zvec_add in Hnth.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    !nvec_to_zvec_add_scale_nth in Hnth.
  rewrite zvec_scale_nat_nth.
  rewrite gamma_direction_nth. lia.
Qed.

Lemma valid_production_basic_omega_run : forall d system gamma,
    @ValidProductionTriple d system gamma ->
    exists run,
      OmegaGamma system gamma run /\
      RunSource run = nvec_add (GammaCapacity gamma) (GammaInput gamma) /\
      RunTarget run = nvec_add (GammaCapacity gamma) (GammaOutput gamma).
Proof.
  intros d system gamma Hvalid.
  apply capacity_transformer_run_iff in Hvalid as [run [Hrun [Hsource Htarget]]].
  exists run. refine (conj _ (conj Hsource Htarget)).
  split; [exact Hrun|]. exists 1%nat. now rewrite !nvec_scale_one.
Qed.

Lemma zvec_scale_nat_add : forall d left right (value : ZVec d),
    zvec_add (zvec_scale_nat left value) (zvec_scale_nat right value) =
      zvec_scale_nat (left + right) value.
Proof.
  intros. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'. unfold zvec_add.
  rewrite (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    !zvec_scale_nat_nth, Nat2Z.inj_add. lia.
Qed.

Lemma zvec_scale_nat_zero_local : forall d (value : ZVec d),
    zvec_scale_nat 0 value = zvec_zero d.
Proof.
  intros. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  rewrite zvec_scale_nat_nth. unfold zvec_zero. rewrite const_nth. cbn. lia.
Qed.

Lemma collect_edge_cycles_subset : forall d system gamma witness graph todo,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    ExactProductionGraphEdges system gamma witness graph ->
    (forall edge, List.In edge todo -> List.In edge graph) ->
    exists multiplier trace,
      ProductionGraphEdgeTrace system gamma witness
        (ProductionGraphSpecialState gamma witness)
        (ProductionGraphSpecialState gamma witness) trace /\
      TotalGraphCycle todo trace /\
      ActionDisplacement (GraphTraceActionWord trace) =
        zvec_scale_nat multiplier (GammaDirection gamma).
Proof.
  intros d system gamma witness graph todo Hvalid Hw Hedges Hsubset.
  induction todo as [|edge tail IH].
  - exists 0%nat, []. refine (conj _ (conj _ _)).
    + split; constructor.
    + intros other Hin. contradiction.
    + cbn. symmetry. apply zvec_scale_nat_zero_local.
  - destruct (IH (fun other Hin => Hsubset other (or_intror Hin)))
      as [tail_multiplier [tail_trace
      [Htail_trace [Htail_total Htail_disp]]]].
    destruct (production_graph_edge_has_omega_cycle d system gamma witness
      graph edge Hvalid Hw Hedges (Hsubset edge (or_introl eq_refl)))
      as [run [edge_multiplier [edge_trace [Homega [Hsource [Htarget
        [Hedge_trace [Hedge_in Hedge_word]]]]]]]].
    exists (edge_multiplier + tail_multiplier)%nat, (edge_trace ++ tail_trace).
    refine (conj _ (conj _ _)).
    + eapply production_graph_edge_trace_append; eauto.
    + intros other [Heq|Hin].
      * subst. apply (proj2 (graph_edge_parikh_positive_iff _ _ _)).
        apply in_or_app. now left.
      * apply (proj2 (graph_edge_parikh_positive_iff _ _ _)).
        apply in_or_app. right.
        apply (proj1 (graph_edge_parikh_positive_iff _ _ _)). apply Htail_total. exact Hin.
    + unfold GraphTraceActionWord in Hedge_word, Htail_disp |- *.
      rewrite List.map_app, action_displacement_app.
      pose proof (f_equal (@ActionDisplacement d) Hedge_word) as Hedge_dispword.
      transitivity (zvec_add (ActionDisplacement (RunActionWord run))
        (ActionDisplacement (List.map RunEdgeAction tail_trace))).
      * apply f_equal2; [exact Hedge_dispword|reflexivity].
      *
      rewrite (omega_run_action_displacement d system gamma run edge_multiplier
        Homega Hsource Htarget).
      rewrite Htail_disp.
      apply zvec_scale_nat_add.
Qed.

Lemma collect_edge_cycles : forall d system gamma witness edges,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    ExactProductionGraphEdges system gamma witness edges ->
    exists multiplier trace,
      ProductionGraphEdgeTrace system gamma witness
        (ProductionGraphSpecialState gamma witness)
        (ProductionGraphSpecialState gamma witness) trace /\
      TotalGraphCycle edges trace /\
      ActionDisplacement (GraphTraceActionWord trace) =
        zvec_scale_nat multiplier (GammaDirection gamma).
Proof.
  intros. eapply collect_edge_cycles_subset; eauto.
Qed.

Theorem production_graph_total_cycle_scaled_gamma_displacement : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d) witness edges,
    ValidProductionTriple system gamma ->
    Lemma57Witness system gamma witness ->
    ExactProductionGraphEdges system gamma witness edges ->
    exists multiplier trace,
      (0 < multiplier)%nat /\
      ProductionGraphEdgeTrace system gamma witness
        (ProductionGraphSpecialState gamma witness)
        (ProductionGraphSpecialState gamma witness) trace /\
      TotalGraphCycle edges trace /\
      ActionDisplacement (GraphTraceActionWord trace) =
        zvec_scale_nat multiplier (GammaDirection gamma).
Proof.
  intros d system gamma witness edges Hvalid Hw Hedges.
  destruct (valid_production_basic_omega_run d system gamma Hvalid)
    as [run [Homega [Hsource Htarget]]].
  destruct (omega_run_projects_to_special_edge_cycle d system gamma witness run
    Hvalid Hw Homega) as [Hbasic_trace Hbasic_word].
  destruct (collect_edge_cycles d system gamma witness edges Hvalid Hw Hedges)
    as [multiplier [trace [Htrace [Htotal Hdisp]]]].
  exists (S multiplier), (ProjectedRunEdgeTrace witness run ++ trace).
  refine (conj (Nat.lt_0_succ multiplier) (conj _ (conj _ _))).
  - eapply production_graph_edge_trace_append; eauto.
  - intros edge Hin. apply (proj2 (graph_edge_parikh_positive_iff _ _ _)).
    apply in_or_app. right. apply (proj1 (graph_edge_parikh_positive_iff _ _ _)).
    apply Htotal. exact Hin.
  - unfold GraphTraceActionWord. rewrite List.map_app, action_displacement_app.
    pose proof (f_equal (@ActionDisplacement d) Hbasic_word) as Hbasic_dispword.
    transitivity (zvec_add (ActionDisplacement (RunActionWord run))
      (ActionDisplacement (List.map RunEdgeAction trace))).
    + apply f_equal2; [exact Hbasic_dispword|reflexivity].
    + rewrite (omega_run_action_displacement d system gamma run 1 Homega).
      * unfold GraphTraceActionWord in Hdisp. rewrite Hdisp. cbn [zvec_scale_nat].
      apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index index' Heq; subst index'.
      unfold zvec_add. rewrite (Vector.nth_map2 Z.add _ _ index index index
        eq_refl eq_refl), !zvec_scale_nat_nth. rewrite Nat2Z.inj_succ. lia.
      * now rewrite nvec_scale_one.
      * now rewrite nvec_scale_one.
Qed.

Lemma graph_weight_sum_nat_to_q : forall d edges weight select,
    @GraphWeightSumQ d edges (fun edge => q_of_nat (weight edge)) select ==
    inject_Z (Z.of_nat (GraphWeightSumNat edges weight select)).
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros weight select; cbn;
    [reflexivity|].
  destruct (select edge).
  - cbn. unfold q_of_nat. rewrite Nat2Z.inj_add, inject_Z_plus.
    apply Qplus_comp; [reflexivity|apply IH].
  - cbn. eapply Qeq_trans; [apply Qplus_0_l|apply IH].
Qed.

Lemma kirchhoff_balance_nat_to_q : forall d edges weight,
    @KirchhoffBalanceNat d edges weight ->
    KirchhoffBalanceQ edges (fun edge => q_of_nat (weight edge)).
Proof.
  intros d edges weight Hbalance state.
  eapply Qeq_trans; [apply graph_weight_sum_nat_to_q|].
  rewrite Hbalance. symmetry. apply graph_weight_sum_nat_to_q.
Qed.

Lemma kirchhoff_displacement_nat_cons : forall d edge tail weight,
    @KirchhoffDisplacementNat d (edge :: tail) weight =
    zvec_add (zvec_scale_nat (weight edge) (RunEdgeAction edge))
      (KirchhoffDisplacementNat tail weight).
Proof.
  intros. unfold KirchhoffDisplacementNat, WeightedGraphActionWord. cbn.
  rewrite action_displacement_app, action_displacement_repeat. reflexivity.
Qed.

Lemma kirchhoff_displacement_nat_to_q : forall d edges weight,
    QVecEq (@KirchhoffDisplacementQ d edges (fun edge => q_of_nat (weight edge)))
      (zvec_to_qvec (KirchhoffDisplacementNat edges weight)).
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros weight index.
  - cbn. unfold qvec_zero, zvec_to_qvec, zvec_zero.
    rewrite Vector.const_nth. reflexivity.
  - change (qvec_add
      (qvec_scale (q_of_nat (weight edge)) (zvec_to_qvec (RunEdgeAction edge)))
      (KirchhoffDisplacementQ tail (fun e => q_of_nat (weight e))) index ==
      zvec_to_qvec (KirchhoffDisplacementNat (edge :: tail) weight) index).
    rewrite kirchhoff_displacement_nat_cons.
    unfold qvec_add, qvec_scale, zvec_to_qvec, zvec_add.
    rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
      zvec_scale_nat_nth, inject_Z_plus.
    unfold q_of_nat. rewrite inject_Z_mult.
    setoid_rewrite (IH weight index). reflexivity.
Qed.

Lemma kirchhoff_displacement_q_scale_local : forall d edges coefficient weight,
    QVecEq (@KirchhoffDisplacementQ d edges
      (fun edge => coefficient * weight edge))
      (qvec_scale coefficient (KirchhoffDisplacementQ edges weight)).
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros coefficient weight index.
  - cbn [KirchhoffDisplacementQ qvec_rsum].
    unfold qvec_zero, qvec_scale. symmetry. apply Qmult_0_r.
  - change (qvec_add
      (qvec_scale (coefficient * weight edge) (zvec_to_qvec (RunEdgeAction edge)))
      (KirchhoffDisplacementQ tail (fun e => coefficient * weight e)) index ==
      qvec_scale coefficient
        (qvec_add (qvec_scale (weight edge) (zvec_to_qvec (RunEdgeAction edge)))
          (KirchhoffDisplacementQ tail weight)) index).
    unfold qvec_add, qvec_scale.
    setoid_rewrite (IH coefficient weight index).
    unfold qvec_scale.
    setoid_rewrite <- Qmult_assoc. symmetry. apply Qmult_plus_distr_r.
Qed.

Lemma inject_Z_sub_qeq : forall left right,
    inject_Z (left - right) == inject_Z left - inject_Z right.
Proof.
  intros left right.
  replace (left - right)%Z with (left + - right)%Z by lia.
  rewrite inject_Z_plus, inject_Z_opp. reflexivity.
Qed.

Lemma graph_trace_edges_in_exact_graph : forall d system gamma witness edges trace
    source target,
    @ExactProductionGraphEdges d system gamma witness edges ->
    ProductionGraphEdgeTrace system gamma witness source target trace ->
    forall edge, List.In edge trace -> List.In edge edges.
Proof.
  intros d system gamma witness edges trace source target [_ Hexact]
    [_ Hall] edge Hin.
  destruct edge as [edge_source edge_action edge_target]. cbn in *.
  apply (proj1 (Hexact edge_source edge_action edge_target)).
  apply (proj1 (List.Forall_forall _ _)) with
    (x := {| RunEdgeSource := edge_source;
             RunEdgeAction := edge_action;
             RunEdgeTarget := edge_target |}) in Hall; assumption.
Qed.

Lemma normalized_parikh_displacement_gamma : forall d
    (gamma : ProductionTriple d) (edges trace : list (ProductionGraphEdge d))
    multiplier,
    NoDup edges ->
    (forall edge, List.In edge trace -> List.In edge edges) ->
    (0 < multiplier)%nat ->
    ActionDisplacement (GraphTraceActionWord trace) =
      zvec_scale_nat multiplier (GammaDirection gamma) ->
    QVecEq
      (KirchhoffDisplacementQ edges
        (fun edge => (/ q_of_nat multiplier) *
          q_of_nat (GraphEdgeParikh trace edge)))
      (QVecDifference (nvec_to_qvec (GammaOutput gamma))
        (nvec_to_qvec (GammaInput gamma))).
Proof.
  intros d gamma edges trace multiplier Hnodup Hsub Hpositive Hdisp index.
  pose proof (graph_edge_parikh_displacement d edges trace
    (GraphEdgeParikh trace) Hnodup Hsub (fun edge _ => eq_refl)) as Hnatdisp.
  pose proof (kirchhoff_displacement_nat_to_q d edges
    (GraphEdgeParikh trace) index) as Hnatq.
  pose proof (kirchhoff_displacement_q_scale_local d edges
    (/ q_of_nat multiplier) (fun edge => q_of_nat (GraphEdgeParikh trace edge))
    index) as Hscale.
  eapply Qeq_trans.
  - exact Hscale.
  -
    unfold qvec_scale. setoid_rewrite Hnatq.
    unfold zvec_to_qvec. rewrite Hnatdisp, Hdisp, zvec_scale_nat_nth,
      gamma_direction_nth.
    unfold QVecDifference, nvec_to_qvec, q_of_nat.
    rewrite inject_Z_mult. setoid_rewrite inject_Z_sub_qeq.
    assert (Hden : ~ q_of_nat multiplier == 0).
    { unfold q_of_nat, Qeq. cbn. lia. }
    field; assumption.
Qed.

Theorem lemma_5_14_gamma_in_kirchhoff_relation : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d),
    ValidProductionTriple system gamma ->
    ProductionKirchhoffRelation system gamma
      (nvec_to_qvec (GammaInput gamma))
      (nvec_to_qvec (GammaOutput gamma)).
Proof.
  intros d system gamma Hvalid.
  destruct (lemma_5_7_bounded_coordinates_intraproduction d system gamma Hvalid)
    as [witness [Hintra Hmask]].
  assert (Hw : Lemma57Witness system gamma witness) by (split; assumption).
  destruct (exact_production_graph_edges_exists d system gamma witness Hvalid Hw)
    as [edges Hedges].
  destruct (production_graph_total_cycle_scaled_gamma_displacement d system gamma
    witness edges Hvalid Hw Hedges) as [multiplier [trace
      [Hpositive [Htrace [Htotal Hdisp]]]]].
  exists witness, edges. refine (conj Hw (conj Hedges _)).
  unfold KirchhoffRelationForEdges.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - intros index. unfold nvec_to_qvec, q_of_nat, Qle. cbn. lia.
  - intros index. unfold nvec_to_qvec, q_of_nat, Qle. cbn. lia.
  - intro index. unfold nvec_to_qvec, q_of_nat, Qlt. cbn. lia.
  - intro index. unfold nvec_to_qvec, q_of_nat, Qlt. cbn. lia.
  - exists (fun edge => (/ q_of_nat multiplier) *
        q_of_nat (GraphEdgeParikh trace edge)).
    refine (conj _ (conj _ _)).
    + apply kirchhoff_balance_q_scale with
        (coefficient := / q_of_nat multiplier).
      apply kirchhoff_balance_nat_to_q.
      apply graph_cycle_parikh_kirchhoff with
        (root := ProductionGraphSpecialState gamma witness).
      * exact (proj1 Hedges).
      * intros edge Hin. eapply graph_trace_edges_in_exact_graph; eauto.
      * exact (proj1 Htrace).
    + intros edge Hin.
      apply Qmult_lt_0_compat.
      * apply Qinv_lt_0_compat. unfold q_of_nat, Qlt. cbn. lia.
      * unfold q_of_nat, Qlt. cbn. specialize (Htotal edge Hin). lia.
    + apply qvec_eq_sym.
      apply normalized_parikh_displacement_gamma.
      * exact (proj1 Hedges).
      * intros edge Hin. eapply graph_trace_edges_in_exact_graph; eauto.
      * exact Hpositive.
      * exact Hdisp.
Qed.
