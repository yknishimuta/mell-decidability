From Coq Require Import List Vector Lia.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.VAS Require Import Runs JancarOrder Transformer.

Import ListNotations.

Fixpoint ValidAnnotatedTrace {d} (system : PlainVAS d) (source : NVec d)
    (trace : list (ActionConfiguration d)) : Prop :=
  match trace with
  | [] => True
  | (action, target) :: tail =>
      PlainVASStep system source action target /\
      ValidAnnotatedTrace system target tail
  end.

Lemma valid_annotated_trace_app : forall d (system : PlainVAS d)
    source left right,
    ValidAnnotatedTrace system source (left ++ right) <->
    ValidAnnotatedTrace system source left /\
    ValidAnnotatedTrace system (TraceTarget source left) right.
Proof.
  intros d system source left. revert source.
  induction left as [|[action target] tail IH]; intros source right; cbn.
  - tauto.
  - rewrite IH. tauto.
Qed.

Lemma valid_annotated_trace_connected : forall d (system : PlainVAS d)
    source trace,
    ValidAnnotatedTrace system source trace -> ConnectedTrace source trace.
Proof.
  intros d system source trace. revert source.
  induction trace as [|[action target] tail IH]; intros source H; cbn in *; auto.
  destruct H as [[_ Haction] Htail]. split; [exact Haction|now apply IH].
Qed.

Lemma valid_annotated_trace_reach : forall d (system : PlainVAS d)
    source trace,
    ValidAnnotatedTrace system source trace ->
    PlainVASReach system source (TraceTarget source trace).
Proof.
  intros d system source trace. revert source.
  induction trace as [|[action target] tail IH]; intros source H; cbn in *.
  - constructor.
  - destruct H as [[Hin Haction] Htail]. subst action.
    econstructor; [exact Hin|now apply IH].
Qed.

Lemma valid_run_annotated_trace : forall d (system : PlainVAS d) run,
    ValidVASRun system run ->
    ValidAnnotatedTrace system (RunSource run) (RunAnnotatedWord run).
Proof.
  intros d system [source targets]. cbn. revert source.
  induction targets as [|target tail IH]; intros source H; cbn in *; auto.
  destruct H as [Hin Htail]. split; [now split|now apply IH].
Qed.

Definition RunOfAnnotatedTrace {d} (source : NVec d)
    (trace : list (ActionConfiguration d)) : VASRun d :=
  {| RunSource := source; RunTargets := List.map snd trace |}.

Lemma steps_of_connected_trace : forall d source trace,
    @ConnectedTrace d source trace ->
    steps_of_targets source (List.map snd trace) = trace.
Proof.
  intros d source trace. revert source.
  induction trace as [|[action target] tail IH]; intros source H; cbn in *; auto.
  destruct H as [Haction Htail]. subst action. f_equal. now apply IH.
Qed.

Lemma run_of_trace_annotated : forall d source trace,
    @ConnectedTrace d source trace ->
    RunAnnotatedWord (RunOfAnnotatedTrace source trace) = trace.
Proof. intros; apply steps_of_connected_trace; assumption. Qed.

Lemma run_of_trace_target : forall d source trace,
    @RunTarget d (RunOfAnnotatedTrace source trace) = TraceTarget source trace.
Proof.
  intros d source trace. unfold RunOfAnnotatedTrace; cbn. revert source.
  induction trace as [|[action target] tail IH]; intros source; cbn; auto.
Qed.

Lemma valid_trace_run : forall d (system : PlainVAS d) source trace,
    ValidAnnotatedTrace system source trace ->
    ValidVASRun system (RunOfAnnotatedTrace source trace).
Proof.
  intros d system source trace. revert source.
  induction trace as [|[action target] tail IH]; intros source H; cbn in *; auto.
  destruct H as [[Hin Haction] Htail]. subst action. split; [exact Hin|now apply IH].
Qed.

Fixpoint TransformerAlongTrace {d} (system : PlainVAS d)
    (current : NVec d) (trace : list (ActionConfiguration d)) : NRelation d :=
  match trace with
  | [] => CapacityTransformer system current
  | (_, target) :: tail =>
      NRelCompose (CapacityTransformer system current)
        (TransformerAlongTrace system target tail)
  end.

Lemma transformer_along_run_trace : forall d (system : PlainVAS d) run,
    NRelSame (TransformerAlongRun system run)
      (TransformerAlongTrace system (RunSource run) (RunAnnotatedWord run)).
Proof.
  intros d system [source targets]. cbn. revert source.
  induction targets as [|target tail IH]; intros source input output; cbn.
  - tauto.
  - unfold NRelCompose. split; intros [middle [Hleft Hright]];
      exists middle; split; [exact Hleft|apply IH|exact Hleft|apply IH];
      exact Hright.
Qed.

Lemma gap_decomposition_transformer : forall d (system : PlainVAS d)
    small_current small_steps big_current big_steps input output,
    ValidAnnotatedTrace system big_current big_steps ->
    JancarGapDecomposition small_current small_steps big_current big_steps ->
    big_current = nvec_add small_current input ->
    TraceTarget big_current big_steps =
      nvec_add (TraceTarget small_current small_steps) output ->
    TransformerAlongTrace system small_current small_steps input output.
Proof.
  intros d system small_current small_steps big_current big_steps input output
    Hvalid Hgap. revert input output Hvalid.
  induction Hgap; intros input output Hvalid Hstart Hend.
  - cbn in *. unfold CapacityTransformer.
    rewrite <- Hstart.
    pose proof (valid_annotated_trace_reach d system big_current gap Hvalid)
      as Hreach.
    rewrite Hend in Hreach. exact Hreach.
  - cbn. unfold NRelCompose.
    apply valid_annotated_trace_app in Hvalid.
    destruct Hvalid as [Hvalid_gap Hvalid_rest]. cbn in Hvalid_rest.
    destruct Hvalid_rest as [_ Hvalid_tail].
    exists offset. split.
    + unfold CapacityTransformer. rewrite <- Hstart, <- H.
      now apply valid_annotated_trace_reach.
    + apply IHHgap with (input := offset) (output := output).
      * exact Hvalid_tail.
      * reflexivity.
      * rewrite trace_target_app in Hend. cbn in Hend. exact Hend.
Qed.

Theorem jancar_run_le_transformer : forall d (system : PlainVAS d)
    (rho sigma : VASRun d),
    ValidVASRun system rho -> ValidVASRun system sigma ->
    JancarRunLe rho sigma ->
    exists input output,
      RunSource sigma = nvec_add (RunSource rho) input /\
      RunTarget sigma = nvec_add (RunTarget rho) output /\
      TransformerAlongRun system rho input output.
Proof.
  intros d system rho sigma Hvalid_rho Hvalid_sigma
    [input [Hsource Hgap]].
  destruct (gap_decomposition_final_offset _ _ _ _ _ Hgap)
    as [output Htarget].
  exists input, output. split; [exact Hsource|]. split.
  - rewrite <- !run_annotated_target. exact Htarget.
  - apply (proj2 (transformer_along_run_trace d system rho input output)).
    apply gap_decomposition_transformer with
      (big_current := RunSource sigma) (big_steps := RunAnnotatedWord sigma).
    + now apply valid_run_annotated_trace.
    + exact Hgap.
    + exact Hsource.
    + exact Htarget.
Qed.

Lemma shifted_plain_vas_step : forall d (system : PlainVAS d)
    source action target offset,
    PlainVASStep system source action target ->
    PlainVASStep system (nvec_add source offset) action (nvec_add target offset).
Proof.
  intros d system source action target offset [Hin Haction]. split; [exact Hin|].
  rewrite step_action_shift. exact Haction.
Qed.

Lemma transformer_trace_realization : forall d (system : PlainVAS d)
    small_current small_steps input output,
    ValidAnnotatedTrace system small_current small_steps ->
    TransformerAlongTrace system small_current small_steps input output ->
    exists big_steps,
      ValidAnnotatedTrace system (nvec_add small_current input) big_steps /\
      JancarGapDecomposition small_current small_steps
        (nvec_add small_current input) big_steps /\
      TraceTarget (nvec_add small_current input) big_steps =
        nvec_add (TraceTarget small_current small_steps) output.
Proof.
  intros d system small_current small_steps. revert small_current.
  induction small_steps as [|[action target] tail IH];
    intros small_current input output Hvalid Htransformer.
  - cbn in Hvalid, Htransformer |- *.
    apply vas_reach_run_iff in Htransformer.
    destruct Htransformer as [gap_run [Hgap_valid [Hgap_source Hgap_target]]].
    exists (RunAnnotatedWord gap_run). split.
    + rewrite <- Hgap_source. now apply valid_run_annotated_trace.
    + split.
      * apply jancar_gap_final with (final_offset := output).
        rewrite <- Hgap_source, run_annotated_target, Hgap_target. reflexivity.
      * rewrite <- Hgap_source, run_annotated_target, Hgap_target. reflexivity.
  - cbn in Hvalid, Htransformer |- *.
    destruct Hvalid as [Hsmall_step Hvalid_tail].
    destruct Htransformer as [middle [Hgap_transformer Htail_transformer]].
    apply vas_reach_run_iff in Hgap_transformer.
    destruct Hgap_transformer as
      [gap_run [Hgap_valid [Hgap_source Hgap_target]]].
    destruct (IH target middle output Hvalid_tail Htail_transformer)
      as [big_tail [Hbig_tail_valid [Hbig_tail_gap Hbig_tail_target]]].
    exists (RunAnnotatedWord gap_run ++
      (action, nvec_add target middle) :: big_tail).
    split.
    + apply valid_annotated_trace_app. split.
      * rewrite <- Hgap_source. now apply valid_run_annotated_trace.
      * rewrite <- Hgap_source, run_annotated_target, Hgap_target. cbn.
        split.
        -- now apply shifted_plain_vas_step.
        -- exact Hbig_tail_valid.
    + split.
      * apply jancar_gap_match with
          (gap := RunAnnotatedWord gap_run) (offset := middle)
          (big_tail := big_tail).
        -- rewrite <- Hgap_source, run_annotated_target, Hgap_target. reflexivity.
        -- exact Hbig_tail_gap.
      * rewrite trace_target_app, <- Hgap_source, run_annotated_target, Hgap_target.
        cbn. exact Hbig_tail_target.
Qed.

Theorem transformer_realized_by_jancar_extension : forall d
    (system : PlainVAS d) (rho : VASRun d) input output,
    ValidVASRun system rho ->
    TransformerAlongRun system rho input output ->
    exists sigma,
      ValidVASRun system sigma /\
      JancarRunLe rho sigma /\
      RunSource sigma = nvec_add (RunSource rho) input /\
      RunTarget sigma = nvec_add (RunTarget rho) output.
Proof.
  intros d system rho input output Hvalid Htransformer.
  apply transformer_along_run_trace in Htransformer.
  pose proof (valid_run_annotated_trace d system rho Hvalid) as Htrace_valid.
  destruct (transformer_trace_realization d system
    (RunSource rho) (RunAnnotatedWord rho) input output
    Htrace_valid Htransformer) as [big_steps [Hbig_valid [Hgap Htarget]]].
  pose (sigma := RunOfAnnotatedTrace (nvec_add (RunSource rho) input) big_steps).
  exists sigma. split.
  - unfold sigma. now apply valid_trace_run.
  - assert (Hconnected : ConnectedTrace
      (nvec_add (RunSource rho) input) big_steps).
    { now apply valid_annotated_trace_connected with (system := system). }
    split.
    + exists input. split; [reflexivity|].
      unfold sigma. rewrite (run_of_trace_annotated d _ _ Hconnected). exact Hgap.
    + split; [reflexivity|]. unfold sigma.
      rewrite run_of_trace_target, Htarget, run_annotated_target. reflexivity.
Qed.

Lemma nvec_add_left_cancel_transformer : forall d
    (base left right : NVec d),
    nvec_add base left = nvec_add base right -> left = right.
Proof.
  intros d base left right H.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Hindex; subst index'.
  pose proof (f_equal (fun value : NVec d => Vector.nth value index) H) as Hnth.
  unfold nvec_add in Hnth.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in Hnth.
  lia.
Qed.

Theorem transformer_along_run_iff_jancar_extension : forall d
    (system : PlainVAS d) (rho : VASRun d) input output,
    ValidVASRun system rho ->
    (TransformerAlongRun system rho input output <->
      exists sigma,
        ValidVASRun system sigma /\
        JancarRunLe rho sigma /\
        RunSource sigma = nvec_add (RunSource rho) input /\
        RunTarget sigma = nvec_add (RunTarget rho) output).
Proof.
  intros d system rho input output Hvalid. split.
  - now apply transformer_realized_by_jancar_extension.
  - intros [sigma [Hsigma [Hle [Hsource Htarget]]]].
    destruct (jancar_run_le_transformer d system rho sigma Hvalid Hsigma Hle)
      as [actual_input [actual_output [Hactual_source
        [Hactual_target Htransformer]]]].
    assert (actual_input = input) as ->.
    { apply nvec_add_left_cancel_transformer with (base := RunSource rho).
      now rewrite <- Hactual_source, <- Hsource. }
    assert (actual_output = output) as ->.
    { apply nvec_add_left_cancel_transformer with (base := RunTarget rho).
      now rewrite <- Hactual_target, <- Htarget. }
    exact Htransformer.
Qed.
