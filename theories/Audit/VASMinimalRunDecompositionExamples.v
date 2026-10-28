From Coq Require Import List Vector ZArith Lia.
From Mell.Core Require Import Vector.
From Mell.VAS Require Import Runs Transformer LinearReachRelation
  MinimalRunDecomposition.

Import ListNotations.

Definition decomposition_audit_n1 (value : nat) : NVec 1 :=
  @Vector.cons nat value 0 (@Vector.nil nat).

Definition decomposition_audit_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition decomposition_audit_empty_run (value : nat) : VASRun 1 :=
  EmptyVASRun (decomposition_audit_n1 value).

Definition decomposition_audit_empty_period : LinearRelationData 1 :=
  {| LinearBaseInput := decomposition_audit_n1 0;
     LinearBaseOutput := decomposition_audit_n1 0;
     LinearGenerators := [] |}.

Definition decomposition_audit_target_period : LinearRelationData 1 :=
  {| LinearBaseInput := decomposition_audit_n1 0;
     LinearBaseOutput := decomposition_audit_n1 0;
     LinearGenerators :=
       [(decomposition_audit_n1 0, decomposition_audit_n1 1)] |}.

Definition decomposition_audit_identity_period : LinearRelationData 1 :=
  {| LinearBaseInput := decomposition_audit_n1 0;
     LinearBaseOutput := decomposition_audit_n1 0;
     LinearGenerators :=
       [(decomposition_audit_n1 1, decomposition_audit_n1 1)] |}.

Example decomposition_audit_transformer_without_period :
    TransformerAlongRun
      [StepAction (decomposition_audit_n1 0) (decomposition_audit_n1 1)]
      (decomposition_audit_empty_run 0)
      (decomposition_audit_n1 0) (decomposition_audit_n1 1) /\
    ~ GeneratedPeriodPair (LinearGenerators decomposition_audit_empty_period)
      (decomposition_audit_n1 0) (decomposition_audit_n1 1).
Proof.
  split.
  - unfold TransformerAlongRun, decomposition_audit_empty_run. cbn.
    unfold CapacityTransformer. cbn.
    eapply plain_vas_reach_step with
      (target := decomposition_audit_n1 1).
    + cbn. left. reflexivity.
    + constructor.
  - intros [coefficients [Hinput Houtput]].
    destruct coefficients using Vector.case0. cbn in Hinput, Houtput.
    subst.
    discriminate.
Qed.

Example decomposition_audit_transformer_condition_is_not_enough :
    ~ LinearRunTransformerComponent
      [StepAction (decomposition_audit_n1 0) (decomposition_audit_n1 1)]
      decomposition_audit_empty_period (decomposition_audit_empty_run 0)
      (decomposition_audit_n1 0) (decomposition_audit_n1 1).
Proof.
  intros [offset_input [offset_output [Hperiod [_ [Hsource Htarget]]]]].
  destruct Hperiod as [coefficients [Hinput Houtput]].
  destruct coefficients using Vector.case0. cbn in Hinput, Houtput.
  subst offset_input offset_output. cbn in Htarget.
  discriminate.
Qed.

Lemma decomposition_audit_empty_system_targets_nil : forall source targets,
    ValidVASTargets ([] : PlainVAS 1) source targets -> targets = [].
Proof.
  intros source [|target tail] Hvalid; [reflexivity|].
  cbn in Hvalid. tauto.
Qed.

Lemma decomposition_audit_empty_system_no_reach_up :
    ~ PlainVASReach ([] : PlainVAS 1)
      (decomposition_audit_n1 0) (decomposition_audit_n1 1).
Proof.
  intros Hreach. apply vas_reach_run_iff in Hreach.
  destruct Hreach as [[source targets] [Hvalid [Hsource Htarget]]].
  cbn in Hvalid, Hsource, Htarget.
  pose proof (decomposition_audit_empty_system_targets_nil source targets Hvalid)
    as ->.
  cbn in Htarget. subst source.
  discriminate.
Qed.

Lemma decomposition_audit_empty_system_reach_eq : forall source target,
    PlainVASReach ([] : PlainVAS 1) source target -> source = target.
Proof.
  intros source target Hreach. apply vas_reach_run_iff in Hreach.
  destruct Hreach as [[run_source targets] [Hvalid [Hsource Htarget]]].
  cbn in Hvalid, Hsource, Htarget.
  pose proof
    (decomposition_audit_empty_system_targets_nil run_source targets Hvalid)
    as ->.
  cbn in Htarget. now rewrite <- Hsource, <- Htarget.
Qed.

Example decomposition_audit_period_without_transformer :
    GeneratedPeriodPair (LinearGenerators decomposition_audit_target_period)
      (decomposition_audit_n1 0) (decomposition_audit_n1 1) /\
    ~ TransformerAlongRun ([] : PlainVAS 1)
      (decomposition_audit_empty_run 0)
      (decomposition_audit_n1 0) (decomposition_audit_n1 1).
Proof.
  split.
  - exists (decomposition_audit_n1 1). split; reflexivity.
  - unfold TransformerAlongRun, decomposition_audit_empty_run. cbn.
    exact decomposition_audit_empty_system_no_reach_up.
Qed.

Example decomposition_audit_period_condition_is_not_enough :
    ~ LinearRunTransformerComponent ([] : PlainVAS 1)
      decomposition_audit_target_period (decomposition_audit_empty_run 0)
      (decomposition_audit_n1 0) (decomposition_audit_n1 1).
Proof.
  intros [offset_input [offset_output [_ [Htransformer [Hsource Htarget]]]]].
  unfold TransformerAlongRun, decomposition_audit_empty_run in Htransformer.
  pose proof (decomposition_audit_empty_system_reach_eq _ _ Htransformer)
    as Hequal.
  pose proof (eq_trans Hsource (eq_trans Hequal (eq_sym Htarget))) as Hzero_one.
  discriminate.
Qed.

Example decomposition_audit_identity_component :
    LinearRunTransformerComponent ([] : PlainVAS 1)
      decomposition_audit_identity_period (decomposition_audit_empty_run 0)
      (decomposition_audit_n1 1) (decomposition_audit_n1 1).
Proof.
  exists (decomposition_audit_n1 1), (decomposition_audit_n1 1).
  repeat split.
  - exists (decomposition_audit_n1 1).
    unfold GeneratedPeriodPairBy, decomposition_audit_identity_period,
      decomposition_audit_n1.
    cbn. split; reflexivity.
  - apply capacity_transformer_refl.
Qed.

Example decomposition_audit_identity_base_in_omega :
    LinearOmegaRun ([] : PlainVAS 1) decomposition_audit_identity_period
      (decomposition_audit_empty_run 0).
Proof.
  split; [apply empty_vas_run_valid|].
  exists (decomposition_audit_n1 0), (decomposition_audit_n1 0).
  split; [apply generated_period_pair_zero|].
  split; reflexivity.
Qed.

Example decomposition_audit_identity_component_sound :
    LinearReachRestricted ([] : PlainVAS 1)
      decomposition_audit_identity_period
      (decomposition_audit_n1 1) (decomposition_audit_n1 1).
Proof.
  eapply linear_run_transformer_component_sound.
  - exact decomposition_audit_identity_base_in_omega.
  - apply decomposition_audit_identity_component.
Qed.

Definition decomposition_audit_empty_omega_data : LinearRelationData 1 :=
  {| LinearBaseInput := decomposition_audit_n1 0;
     LinearBaseOutput := decomposition_audit_n1 1;
     LinearGenerators := [] |}.

Example decomposition_audit_empty_omega : forall run,
    ~ LinearOmegaRun ([] : PlainVAS 1) decomposition_audit_empty_omega_data run.
Proof.
  intros [source targets] [Hvalid
    [period_input [period_output [[coefficients [Hinput Houtput]]
      [Hsource Htarget]]]]].
  cbn in Hvalid, Hsource, Htarget.
  pose proof (decomposition_audit_empty_system_targets_nil source targets Hvalid)
    as ->.
  destruct coefficients using Vector.case0.
  cbn in Hinput, Houtput, Hsource, Htarget.
  subst period_input period_output source.
  discriminate.
Qed.

Example decomposition_audit_empty_basis_exact : forall source target,
    LinearReachRestricted ([] : PlainVAS 1)
      decomposition_audit_empty_omega_data source target <->
    exists rho,
      List.In rho ([] : list (VASRun 1)) /\
      LinearRunTransformerComponent ([] : PlainVAS 1)
        decomposition_audit_empty_omega_data rho source target.
Proof.
  apply linear_reach_finite_basis_decomposition.
  - intros rho Hin. contradiction.
  - intros sigma Homega. exfalso.
    exact (decomposition_audit_empty_omega sigma Homega).
Qed.

Example decomposition_audit_dimension_zero_decomposition :
    exists basis : list (VASRun 0),
      (forall rho, List.In rho basis ->
        LinearOmegaRun ([] : PlainVAS 0)
          {| LinearBaseInput := @Vector.nil nat;
             LinearBaseOutput := @Vector.nil nat;
             LinearGenerators := [] |} rho) /\
      (forall sigma,
        LinearOmegaRun ([] : PlainVAS 0)
          {| LinearBaseInput := @Vector.nil nat;
             LinearBaseOutput := @Vector.nil nat;
             LinearGenerators := [] |} sigma ->
        exists rho, List.In rho basis /\
          LinearRunLe
            {| LinearBaseInput := @Vector.nil nat;
               LinearBaseOutput := @Vector.nil nat;
               LinearGenerators := [] |} rho sigma) /\
      forall source target,
        LinearReachRestricted ([] : PlainVAS 0)
          {| LinearBaseInput := @Vector.nil nat;
             LinearBaseOutput := @Vector.nil nat;
             LinearGenerators := [] |} source target <->
        exists rho, List.In rho basis /\
          LinearRunTransformerComponent ([] : PlainVAS 0)
            {| LinearBaseInput := @Vector.nil nat;
               LinearBaseOutput := @Vector.nil nat;
               LinearGenerators := [] |} rho source target.
Proof. apply lemma_6_1_linear_reach_decomposition. Qed.

Check LinearReachRestricted.
Check LinearRunTransformerComponent.
Check linear_reach_restricted_iff_omega_run.
Check linear_run_transformer_component_sound.
Check linear_finite_cover_component_complete.
Check linear_reach_finite_basis_decomposition.
Check lemma_6_1_linear_reach_decomposition.
Check linear_transformer_period_intersection_periodic.

Set Printing Implicit.
Check LinearReachRestricted.
Check LinearRunTransformerComponent.
Check linear_reach_restricted_iff_omega_run.
Check linear_run_transformer_component_sound.
Check linear_finite_cover_component_complete.
Check linear_reach_finite_basis_decomposition.
Check lemma_6_1_linear_reach_decomposition.
Check linear_transformer_period_intersection_periodic.
Unset Printing Implicit.

Print Assumptions linear_reach_restricted_iff_omega_run.
Print Assumptions linear_run_transformer_component_sound.
Print Assumptions linear_finite_cover_component_complete.
Print Assumptions linear_reach_finite_basis_decomposition.
Print Assumptions lemma_6_1_linear_reach_decomposition.
Print Assumptions linear_transformer_period_intersection_periodic.
Print Assumptions decomposition_audit_identity_component.
