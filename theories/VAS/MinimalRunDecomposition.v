From Coq Require Import List.
From Mell.Core Require Import Vector.
From Mell.VAS Require Import Runs Transformer TransformerJancar
  LinearReachRelation MinimalRunFiniteBasis.

Definition LinearReachRestricted {d}
    (system : PlainVAS d) (data : LinearRelationData d)
    (source target : NVec d) : Prop :=
  PlainVASReach system source target /\
  LinearRelationContains data source target.

Definition LinearRunTransformerComponent {d}
    (system : PlainVAS d) (data : LinearRelationData d)
    (rho : VASRun d) (source target : NVec d) : Prop :=
  exists offset_input offset_output,
    GeneratedPeriodPair (LinearGenerators data) offset_input offset_output /\
    TransformerAlongRun system rho offset_input offset_output /\
    source = nvec_add (RunSource rho) offset_input /\
    target = nvec_add (RunTarget rho) offset_output.

Theorem linear_reach_restricted_iff_omega_run : forall d
    (system : PlainVAS d) (data : LinearRelationData d) source target,
    LinearReachRestricted system data source target <->
    exists run,
      LinearOmegaRun system data run /\
      RunSource run = source /\
      RunTarget run = target.
Proof.
  intros d system data source target. split.
  - intros [Hreach Hlinear]. apply vas_reach_run_iff in Hreach.
    destruct Hreach as [run [Hvalid [Hsource Htarget]]].
    exists run. split.
    + split; [exact Hvalid|]. now rewrite Hsource, Htarget.
    + now split.
  - intros [run [[Hvalid Hlinear] [Hsource Htarget]]]. split.
    + apply vas_reach_run_iff. exists run. repeat split; assumption.
    + now rewrite <- Hsource, <- Htarget.
Qed.

Theorem linear_run_transformer_component_sound : forall d
    (system : PlainVAS d) (data : LinearRelationData d)
    (rho : VASRun d) source target,
    LinearOmegaRun system data rho ->
    LinearRunTransformerComponent system data rho source target ->
    LinearReachRestricted system data source target.
Proof.
  intros d system data rho source target Homega
    [offset_input [offset_output
      [Hperiod [Htransformer [Hsource Htarget]]]]].
  destruct (transformer_realized_by_jancar_extension d system rho
    offset_input offset_output (linear_omega_run_valid _ _ _ _ Homega)
    Htransformer) as [sigma
      [Hvalid [Hjancar [Hsigma_source Hsigma_target]]]].
  apply linear_reach_restricted_iff_omega_run.
  exists sigma. split.
  - eapply linear_omega_run_upward; [exact Homega| |exact Hvalid].
    split; [exact Hjancar|].
    exists offset_input, offset_output. repeat split; assumption.
  - split.
    + now rewrite Hsigma_source, Hsource.
    + now rewrite Hsigma_target, Htarget.
Qed.

Theorem linear_finite_cover_component_complete : forall d
    (system : PlainVAS d) (data : LinearRelationData d)
    (basis : list (VASRun d)),
    (forall rho, List.In rho basis -> LinearOmegaRun system data rho) ->
    (forall sigma, LinearOmegaRun system data sigma ->
      exists rho, List.In rho basis /\ LinearRunLe data rho sigma) ->
    forall source target,
      LinearReachRestricted system data source target ->
      exists rho,
        List.In rho basis /\
        LinearRunTransformerComponent system data rho source target.
Proof.
  intros d system data basis Hbasis Hcover source target Hrestricted.
  apply linear_reach_restricted_iff_omega_run in Hrestricted.
  destruct Hrestricted as [sigma [Homega [Hsource Htarget]]].
  destruct (Hcover sigma Homega) as [rho [Hin Hle]].
  destruct (linear_run_le_transformer_period_witness d system data rho sigma
    (linear_omega_run_valid _ _ _ _ (Hbasis rho Hin))
    (linear_omega_run_valid _ _ _ _ Homega) Hle)
    as [offset_input [offset_output
      [Hperiod [Hsigma_source [Hsigma_target Htransformer]]]]].
  exists rho. split; [exact Hin|].
  exists offset_input, offset_output. repeat split; try assumption.
  - now rewrite <- Hsource, Hsigma_source.
  - now rewrite <- Htarget, Hsigma_target.
Qed.

Theorem linear_reach_finite_basis_decomposition : forall d
    (system : PlainVAS d) (data : LinearRelationData d)
    (basis : list (VASRun d)),
    (forall rho, List.In rho basis -> LinearOmegaRun system data rho) ->
    (forall sigma, LinearOmegaRun system data sigma ->
      exists rho, List.In rho basis /\ LinearRunLe data rho sigma) ->
    forall source target,
      LinearReachRestricted system data source target <->
      exists rho,
        List.In rho basis /\
        LinearRunTransformerComponent system data rho source target.
Proof.
  intros d system data basis Hbasis Hcover source target. split.
  - now apply linear_finite_cover_component_complete.
  - intros [rho [Hin Hcomponent]].
    eapply linear_run_transformer_component_sound.
    + exact (Hbasis rho Hin).
    + exact Hcomponent.
Qed.

Theorem lemma_6_1_linear_reach_decomposition : forall d
    (system : PlainVAS d) (data : LinearRelationData d),
    exists basis : list (VASRun d),
      (forall rho, List.In rho basis -> LinearOmegaRun system data rho) /\
      (forall sigma, LinearOmegaRun system data sigma ->
        exists rho, List.In rho basis /\ LinearRunLe data rho sigma) /\
      (forall source target,
        LinearReachRestricted system data source target <->
        exists rho,
          List.In rho basis /\
          LinearRunTransformerComponent system data rho source target).
Proof.
  intros d system data.
  destruct (linear_omega_finite_cover d system data) as [basis [Hbasis Hcover]].
  exists basis. split; [exact Hbasis|]. split; [exact Hcover|].
  now apply linear_reach_finite_basis_decomposition.
Qed.

Theorem linear_transformer_period_intersection_periodic : forall d
    (system : PlainVAS d) (data : LinearRelationData d) (rho : VASRun d),
    PeriodicNRelation
      (fun offset_input offset_output =>
        TransformerAlongRun system rho offset_input offset_output /\
        GeneratedPeriodPair (LinearGenerators data)
          offset_input offset_output).
Proof.
  intros d system data rho.
  destruct (transformer_along_run_periodic d system rho)
    as [Htransformer_zero Htransformer_add].
  destruct (generated_period_pair_periodic d (LinearGenerators data))
    as [Hperiod_zero Hperiod_add].
  split.
  - now split.
  - intros x1 y1 x2 y2 [Ht1 Hp1] [Ht2 Hp2]. split.
    + now apply Htransformer_add.
    + now apply Hperiod_add.
Qed.
