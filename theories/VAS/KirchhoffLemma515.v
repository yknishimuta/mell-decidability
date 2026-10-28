From Coq Require Import Arith Fin Lia List Vector ZArith QArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore RationalHToV.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.VAS Require Import Runs Transformer RelationCone Intraproductions
  IntraproductionsLemma57 ProductionGraph ProductionGraphPaths GraphParikh
  Kirchhoff EulerCycles KirchhoffRelation KirchhoffLemma514
  GraphCyclePumping KirchhoffScaling.

Import ListNotations.
Open Scope Q_scope.

(** The rational cone of the (natural) capacity transformer.  Notice that this
    is a cone of the exact signed embedding of the reachability relation, not a
    relation on rational configurations. *)
Definition CapacityTransformerCone {d} (system : PlainVAS d)
    (capacity : NVec d) : QVec d -> QVec d -> Prop :=
  RationalRelationCone
    (NRelationAsZ (CapacityTransformer system capacity)).

Lemma capacity_transformer_scaled_pair_in_cone : forall d system capacity
    multiplier (input output : QVec d) (scaled_input scaled_output : NVec d),
    (0 < multiplier)%nat ->
    CapacityTransformer system capacity scaled_input scaled_output ->
    QVecEq (qvec_scale (q_of_nat multiplier) input)
      (nvec_to_qvec scaled_input) ->
    QVecEq (qvec_scale (q_of_nat multiplier) output)
      (nvec_to_qvec scaled_output) ->
    CapacityTransformerCone system capacity input output.
Proof.
  intros d system capacity multiplier input output scaled_input scaled_output
    Hpositive Htransform Hinput Houtput.
  unfold CapacityTransformerCone.
  pose proof (periodic_nrelation_as_z d
    (CapacityTransformer system capacity)
    (capacity_transformer_periodic d system capacity)) as Hperiodic.
  apply (proj2 (periodic_relation_cone_positive_multiple_iff d
    (NRelationAsZ (CapacityTransformer system capacity)) input output
    Hperiodic)).
  - exists multiplier, (nvec_to_zvec scaled_input),
      (nvec_to_zvec scaled_output). repeat split; try assumption.
    + exists scaled_input, scaled_output. auto.
    + intro index. unfold nvec_to_qvec, zvec_to_qvec, nvec_to_zvec.
      rewrite (Vector.nth_map Z.of_nat _ index index eq_refl).
      apply Hinput.
    + intro index. unfold nvec_to_qvec, zvec_to_qvec, nvec_to_zvec.
      rewrite (Vector.nth_map Z.of_nat _ index index eq_refl).
      apply Houtput.
Qed.
(** The two concrete reachability witnesses carried by an intraproduction.
    Keeping the common multiplier explicit is important in Lemma 5.15. *)
Lemma intraproduction_split_runs : forall d system gamma witness,
    @IntraProduction d system gamma witness ->
    exists multiplier,
      PlainVASReach system
        (nvec_add (GammaCapacity gamma)
          (nvec_scale multiplier (GammaInput gamma)))
        (nvec_add (GammaCapacity gamma) witness) /\
      PlainVASReach system
        (nvec_add (GammaCapacity gamma) witness)
        (nvec_add (GammaCapacity gamma)
          (nvec_scale multiplier (GammaOutput gamma))).
Proof. intros d system gamma witness H; exact H. Qed.

Lemma periodic_nrelation_nsmul : forall d (relation : NRelation d)
    coefficient input output,
    PeriodicNRelation relation ->
    relation input output ->
    relation (nvec_scale coefficient input) (nvec_scale coefficient output).
Proof.
  intros d relation coefficient. induction coefficient as [|coefficient IH];
    intros input output [Hzero Hadd] Hrelation.
  - rewrite !nvec_scale_zero. exact Hzero.
  - rewrite !nvec_scale_succ. apply Hadd; [exact Hrelation|].
    apply IH; [split; assumption|assumption].
Qed.

Lemma intraproduction_projects_to_parikh_cycle : forall d system gamma witness
    edges,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    ExactProductionGraphEdges system gamma witness edges ->
    exists multiplier trace,
      PlainVASReach system
        (nvec_add (GammaCapacity gamma)
          (nvec_scale multiplier (GammaInput gamma)))
        (nvec_add (GammaCapacity gamma) witness) /\
      PlainVASReach system
        (nvec_add (GammaCapacity gamma) witness)
        (nvec_add (GammaCapacity gamma)
          (nvec_scale multiplier (GammaOutput gamma))) /\
      ProductionGraphEdgeTrace system gamma witness
        (ProductionGraphSpecialState gamma witness)
        (ProductionGraphSpecialState gamma witness) trace /\
      KirchhoffBalanceNat edges (GraphEdgeParikh trace) /\
      KirchhoffDisplacementNat edges (GraphEdgeParikh trace) =
        zvec_scale_nat multiplier (GammaDirection gamma).
Proof.
  intros d system gamma witness edges Hvalid Hw Hedges.
  destruct Hw as [Hintra Hmask].
  destruct Hintra as [multiplier [Hprefix Hsuffix]].
  pose proof (PlainVASReach_trans d system _ _ _ Hprefix Hsuffix) as Hreach.
  apply vas_reach_run_iff in Hreach.
  destruct Hreach as [run [Hrun [Hsource Htarget]]].
  assert (Homega : OmegaGamma system gamma run).
  { split; [exact Hrun|]. exists multiplier. auto. }
  pose proof (omega_run_projects_to_special_cycle d system gamma witness run
    Hvalid (conj (ex_intro _ multiplier (conj Hprefix Hsuffix)) Hmask) Homega)
    as Hpath.
  destruct (production_graph_path_has_edge_trace d system gamma witness
    _ _ (RunActionWord run) Hpath) as [trace [Htrace Hword]].
  exists multiplier, trace. split; [exact Hprefix|]. split; [exact Hsuffix|].
  split; [exact Htrace|]. split.
  - apply graph_cycle_parikh_kirchhoff with
      (root := ProductionGraphSpecialState gamma witness).
    + exact (proj1 Hedges).
    + intros edge Hin.
      destruct Htrace as [Hconnected Hall].
      apply List.Forall_forall with (x := edge) in Hall; [|exact Hin].
      destruct edge as [source action target]. cbn in *.
      now apply (proj1 (proj2 Hedges source action target)).
    + exact (proj1 Htrace).
  - eapply eq_trans.
    + apply graph_edge_parikh_displacement.
      * exact (proj1 Hedges).
      * intros edge Hin.
        destruct Htrace as [Hconnected Hall].
        apply List.Forall_forall with (x := edge) in Hall; [|exact Hin].
        destruct edge as [source action target]. cbn in *.
        now apply (proj1 (proj2 Hedges source action target)).
      * intros; reflexivity.
    + rewrite Hword.
      apply omega_run_action_displacement with (system := system)
        (gamma := gamma); assumption.
Qed.

Lemma gamma_scaled_endpoint : forall d (gamma : ProductionTriple d) multiplier,
    nvec_to_zvec (nvec_scale multiplier (GammaOutput gamma)) =
      zvec_add
        (nvec_to_zvec (nvec_scale multiplier (GammaInput gamma)))
        (zvec_scale_nat multiplier (GammaDirection gamma)).
Proof.
  intros d gamma multiplier.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index other <-.
  unfold nvec_to_zvec, nvec_scale, zvec_add.
  repeat rewrite (Vector.nth_map Z.of_nat _ index index eq_refl).
  repeat rewrite (Vector.nth_map (Nat.mul multiplier) _ index index eq_refl).
  rewrite (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    zvec_scale_nat_nth, gamma_direction_nth, !Nat2Z.inj_mul.
  rewrite (Vector.nth_map Z.of_nat _ index index eq_refl),
    (Vector.nth_map (Nat.mul multiplier) _ index index eq_refl),
    Nat2Z.inj_mul. lia.
Qed.

Lemma capacity_run_power_and_shift : forall d system capacity input output
    coefficient offset,
    @CapacityTransformer d system capacity input output ->
    PlainVASReach system
      (nvec_add (nvec_add capacity (nvec_scale coefficient input)) offset)
      (nvec_add (nvec_add capacity (nvec_scale coefficient output)) offset).
Proof.
  intros d system capacity input output coefficient offset Htransform.
  pose proof (periodic_nrelation_nsmul d
    (CapacityTransformer system capacity) coefficient input output
    (capacity_transformer_periodic d system capacity) Htransform) as Hscaled.
  unfold CapacityTransformer in Hscaled.
  now apply vas_reach_monotone.
Qed.

Fixpoint RepeatActionWord {d} (coefficient : nat)
    (word : list (ZVec d)) : list (ZVec d) :=
  match coefficient with
  | O => []
  | S tail => word ++ RepeatActionWord tail word
  end.

Lemma steps_of_targets_app_actions : forall d source left right,
    List.map fst (@steps_of_targets d source (left ++ right)) =
      List.map fst (steps_of_targets source left) ++
      List.map fst (steps_of_targets (targets_target source left) right).
Proof.
  intros d source left. revert source.
  induction left as [|target tail IH]; intros source right; cbn; auto.
  now rewrite IH.
Qed.

Lemma run_concat_action_word : forall d (left right : VASRun d),
    RunTarget left = RunSource right ->
    RunActionWord (VASRunConcat left right) =
      RunActionWord left ++ RunActionWord right.
Proof.
  intros d [left_source left_targets] [right_source right_targets] Hconnect.
  unfold RunActionWord, RunSteps, VASRunConcat; cbn in *.
  rewrite steps_of_targets_app_actions, Hconnect. reflexivity.
Qed.

(** Unlike mere periodicity of the transformer relation, this theorem keeps
    the concrete word: the witness run executes the original word exactly
    [coefficient] times. *)
Lemma pumped_graph_cycle_iterated_run : forall d system base
    (input output : NVec d) run coefficient,
    @ValidVASRun d system run ->
    RunSource run = base ->
    nvec_to_zvec (RunTarget run) = zvec_add (nvec_to_zvec base)
      (ActionDisplacement (RunActionWord run)) ->
    nvec_to_zvec output = zvec_add (nvec_to_zvec input)
      (ActionDisplacement (RunActionWord run)) ->
    exists iterated,
      ValidVASRun system iterated /\
      RunSource iterated =
        nvec_add base (nvec_scale coefficient input) /\
      RunTarget iterated =
        nvec_add base (nvec_scale coefficient output) /\
      RunActionWord iterated =
        RepeatActionWord coefficient (RunActionWord run).
Proof.
  intros d system base input output run coefficient Hvalid Hsource Htarget Hdelta.
  induction coefficient as [|coefficient IH].
  - exists (EmptyVASRun base). split; [apply empty_vas_run_valid|].
    rewrite !nvec_scale_zero, !nvec_add_zero_right_local. repeat split; reflexivity.
  - destruct IH as [tail_run [Htail_valid
      [Htail_source [Htail_target Htail_word]]]].
    set (first := ShiftVASRun (nvec_scale (S coefficient) input) run).
    set (tail := ShiftVASRun output tail_run).
    assert (Hfirst_valid : ValidVASRun system first).
    { unfold first. now apply vas_run_shift_valid. }
    assert (Htail_shift_valid : ValidVASRun system tail).
    { unfold tail. now apply vas_run_shift_valid. }
    assert (Hfirst_source : RunSource first =
        nvec_add base (nvec_scale (S coefficient) input)).
    { unfold first. destruct (shift_run_endpoints d
        (nvec_scale (S coefficient) input) run) as [Hs _].
      now rewrite Hs, Hsource. }
    assert (Hfirst_target : RunTarget first =
        nvec_add (nvec_add base (nvec_scale coefficient input)) output).
    { unfold first. destruct (shift_run_endpoints d
        (nvec_scale (S coefficient) input) run) as [_ Ht]. rewrite Ht.
      apply nvec_to_zvec_injective.
      apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index other <-.
      pose proof (f_equal (fun value : ZVec d => Vector.nth value index)
        Htarget) as Hti.
      pose proof (f_equal (fun value : ZVec d => Vector.nth value index)
        Hdelta) as Hdi.
      unfold nvec_to_zvec, nvec_add, nvec_scale, zvec_add in *.
      repeat rewrite (Vector.nth_map Z.of_nat _ index index eq_refl) in *.
      repeat rewrite (Vector.nth_map (Nat.mul _) _ index index eq_refl) in *.
      repeat rewrite
        (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in *.
      repeat rewrite (Vector.nth_map (Nat.mul _) _ index index eq_refl) in *.
      repeat rewrite
        (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl) in *.
      repeat rewrite (Vector.nth_map Z.of_nat _ index index eq_refl) in *.
      repeat rewrite
        (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in *.
      repeat rewrite Nat2Z.inj_mul in *.
      nia. }
    assert (Htail_source_shift : RunSource tail =
        nvec_add (nvec_add base (nvec_scale coefficient input)) output).
    { unfold tail. destruct (shift_run_endpoints d output tail_run) as [Hs _].
      now rewrite Hs, Htail_source. }
    assert (Htail_target_shift : RunTarget tail =
        nvec_add base (nvec_scale (S coefficient) output)).
    { unfold tail. destruct (shift_run_endpoints d output tail_run) as [_ Ht].
      rewrite Ht, Htail_target, nvec_scale_succ.
      apply (proj1 (Vector.eq_nth_iff nat d _ _)). intros index other <-.
      unfold nvec_add. repeat rewrite
        (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl). lia. }
    assert (Hconnect : RunTarget first = RunSource tail).
    { now rewrite Hfirst_target, Htail_source_shift. }
    exists (VASRunConcat first tail). split.
    + now apply vas_run_concat_valid.
    + split; [exact Hfirst_source|]. split.
      * rewrite run_concat_target by exact Hconnect. exact Htail_target_shift.
      * rewrite run_concat_action_word by exact Hconnect.
        unfold first, tail. rewrite !shift_run_action_word, Htail_word.
        reflexivity.
Qed.

Lemma pumped_graph_cycle_iterated : forall d system base
    (input output : NVec d) run coefficient,
    @ValidVASRun d system run ->
    RunSource run = base ->
    nvec_to_zvec (RunTarget run) = zvec_add (nvec_to_zvec base)
      (ActionDisplacement (RunActionWord run)) ->
    nvec_to_zvec output = zvec_add (nvec_to_zvec input)
      (ActionDisplacement (RunActionWord run)) ->
    CapacityTransformer system base
      (nvec_scale coefficient input) (nvec_scale coefficient output).
Proof.
  intros d system base input output run coefficient Hrun Hsource Htarget Hdelta.
  destruct (pumped_graph_cycle_iterated_run d system base input output run
    coefficient Hrun Hsource Htarget Hdelta) as
    [iterated [Hiterated [Hiterated_source [Hiterated_target _]]]].
  unfold CapacityTransformer. apply vas_reach_run_iff.
  exists iterated. auto.
Qed.

Theorem lemma_5_15_kirchhoff_in_capacity_cone : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d)
    (input output : QVec d),
    ValidProductionTriple system gamma ->
    ProductionKirchhoffRelation system gamma input output ->
    CapacityTransformerCone system (GammaCapacity gamma) input output.
Proof.
  intros d system gamma input output Hvalid Hrelation.
  destruct Hrelation as [witness [edges [Hw [Hedges Hfixed]]]].
  destruct Hfixed as [Hinput_nonnegative [Houtput_nonnegative
    [Hinput_support [Houtput_support
    [weight [Hweight_balance [Hweight_positive Hweight_displacement]]]]]]].
  destruct (intraproduction_projects_to_parikh_cycle d system gamma witness
    edges Hvalid Hw Hedges) as [n [removed_trace
    [Hprefix [Hsuffix [Hremoved_trace
    [Hremoved_balance Hremoved_displacement]]]]]].
  set (removed := GraphEdgeParikh removed_trace).
  destruct (positive_rational_kirchhoff_uniform_scaling d gamma edges input
    output weight n removed (fun _ => 0%nat) (proj1 Hedges)
    Hinput_nonnegative Houtput_nonnegative Hinput_support Houtput_support
    Hweight_balance Hweight_positive Hweight_displacement)
    as [k [scaled_input [scaled_output [scaled_weight
    [Hk [Hscaled_input [Hscaled_output [Hinput_lower [Houtput_lower
    [Hscaled_balance [Hstrict Hscaled_endpoint]]]]]]]]]]].
  set (removed_input := nvec_scale n (GammaInput gamma)).
  set (removed_output := nvec_scale n (GammaOutput gamma)).
  assert (Hremoved_endpoint : nvec_to_zvec removed_output =
      zvec_add (nvec_to_zvec removed_input)
        (KirchhoffDisplacementNat edges removed)).
  { unfold removed_input, removed_output, removed.
    rewrite Hremoved_displacement. apply gamma_scaled_endpoint. }
  destruct (positive_residual_kirchhoff d edges scaled_weight removed
    scaled_input scaled_output removed_input removed_output Hscaled_balance
    Hremoved_balance) as [Hresidual_balance
    [Hresidual_positive Hresidual_endpoint]].
  - intros edge Hin. specialize (Hstrict edge Hin). cbn in Hstrict. lia.
  - exact Hinput_lower.
  - exact Houtput_lower.
  - exact Hscaled_endpoint.
  - exact Hremoved_endpoint.
  set (residual_input := nvec_sub scaled_input removed_input).
  set (residual_output := nvec_sub scaled_output removed_output).
  set (residual_weight := fun edge =>
    (scaled_weight edge - removed edge)%nat).
  change (KirchhoffBalanceNat edges residual_weight) in Hresidual_balance.
  change (forall edge, List.In edge edges ->
    (0 < residual_weight edge)%nat) in Hresidual_positive.
  change (nvec_to_zvec residual_output =
    zvec_add (nvec_to_zvec residual_input)
      (KirchhoffDisplacementNat edges residual_weight)) in Hresidual_endpoint.
  destruct (production_graph_positive_kirchhoff_realized d system gamma witness
    edges residual_weight Hvalid Hw (proj1 Hedges) (proj2 Hedges)
    Hresidual_balance Hresidual_positive) as [cycle
    [Hcycle_trace [Hcycle_total Hcycle_parikh]]].
  destruct (production_graph_cycle_realizable_after_pumping d system gamma
    witness cycle Hvalid Hw Hcycle_trace) as [m [cycle_run
    [Hm [Hcycle_run [Hcycle_source [Hcycle_word Hcycle_target]]]]]].
  assert (Hcycle_displacement : KirchhoffDisplacementNat edges residual_weight =
      ActionDisplacement (GraphTraceActionWord cycle)).
  { apply graph_edge_parikh_displacement.
    - exact (proj1 Hedges).
    - intros edge Hin.
      destruct Hcycle_trace as [Hconnected Hall].
      apply List.Forall_forall with (x := edge) in Hall; [|exact Hin].
      destruct edge as [source action target]. cbn in *.
      now apply (proj1 (proj2 Hedges source action target)).
    - exact Hcycle_parikh. }
  assert (Hresidual_run_endpoint : nvec_to_zvec residual_output =
      zvec_add (nvec_to_zvec residual_input)
        (ActionDisplacement (RunActionWord cycle_run))).
  { rewrite Hcycle_word. rewrite <- Hcycle_displacement.
    exact Hresidual_endpoint. }
  assert (Hcycle_target_run : nvec_to_zvec (RunTarget cycle_run) =
      zvec_add (nvec_to_zvec (RunSource cycle_run))
        (ActionDisplacement (RunActionWord cycle_run))).
  { rewrite Hcycle_source, Hcycle_word. exact Hcycle_target. }
  assert (Hcycle_target_base : nvec_to_zvec (RunTarget cycle_run) =
      zvec_add
        (nvec_to_zvec (nvec_add (GammaCapacity gamma) (nvec_scale m witness)))
        (ActionDisplacement (RunActionWord cycle_run))).
  { rewrite <- Hcycle_source. exact Hcycle_target_run. }
  pose proof (pumped_graph_cycle_iterated d system
    (nvec_add (GammaCapacity gamma) (nvec_scale m witness))
    residual_input residual_output cycle_run m Hcycle_run Hcycle_source
    Hcycle_target_base Hresidual_run_endpoint) as Hmiddle.
  assert (Hprefix_transform : CapacityTransformer system (GammaCapacity gamma)
      removed_input witness).
  { exact Hprefix. }
  assert (Hsuffix_transform : CapacityTransformer system (GammaCapacity gamma)
      witness removed_output).
  { exact Hsuffix. }
  pose proof (capacity_run_power_and_shift d system (GammaCapacity gamma)
    removed_input witness m (nvec_scale m residual_input) Hprefix_transform)
    as Hfirst.
  pose proof (capacity_run_power_and_shift d system (GammaCapacity gamma)
    witness removed_output m (nvec_scale m residual_output) Hsuffix_transform)
    as Hlast.
  pose proof (nvec_sub_exact d removed_input scaled_input Hinput_lower)
    as Hinput_exact.
  pose proof (nvec_sub_exact d removed_output scaled_output Houtput_lower)
    as Houtput_exact.
  assert (Hfirst_source :
      nvec_add (nvec_add (GammaCapacity gamma)
        (nvec_scale m removed_input)) (nvec_scale m residual_input) =
      nvec_add (GammaCapacity gamma) (nvec_scale m scaled_input)).
  { rewrite Hinput_exact, nvec_scale_add_vector, nvec_add_assoc_local. reflexivity. }
  assert (Hlast_target :
      nvec_add (nvec_add (GammaCapacity gamma)
        (nvec_scale m removed_output)) (nvec_scale m residual_output) =
      nvec_add (GammaCapacity gamma) (nvec_scale m scaled_output)).
  { rewrite Houtput_exact, nvec_scale_add_vector, nvec_add_assoc_local. reflexivity. }
  rewrite Hfirst_source in Hfirst.
  rewrite Hlast_target in Hlast.
  unfold CapacityTransformer in Hmiddle.
  pose proof (PlainVASReach_trans d system _ _ _ Hfirst Hmiddle) as Hcombined.
  pose proof (PlainVASReach_trans d system _ _ _ Hcombined Hlast) as Hwhole.
  apply (capacity_transformer_scaled_pair_in_cone d system
    (GammaCapacity gamma) (m * k)%nat input output
    (nvec_scale m scaled_input) (nvec_scale m scaled_output)).
  - nia.
  - exact Hwhole.
  - rewrite Nat.mul_comm. now apply qvec_clear_multiply.
  - rewrite Nat.mul_comm. now apply qvec_clear_multiply.
Qed.
