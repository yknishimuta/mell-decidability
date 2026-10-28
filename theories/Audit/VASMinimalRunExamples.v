From Coq Require Import List Vector ZArith Lia.
From KruskalHigmanProp Require Import embeddings.list_embed.
From Mell.Core Require Import Vector.
From Mell.VAS Require Import Runs JancarOrder LinearReachRelation
  MinimalRunFiniteBasis.

Import ListNotations.

Definition minimal_audit_n1 (value : nat) : NVec 1 :=
  @Vector.cons nat value 0 (@Vector.nil nat).

Definition minimal_audit_empty_run (value : nat) : VASRun 1 :=
  EmptyVASRun (minimal_audit_n1 value).

Definition minimal_audit_empty_period : LinearRelationData 1 :=
  {| LinearBaseInput := minimal_audit_n1 0;
     LinearBaseOutput := minimal_audit_n1 0;
     LinearGenerators := [] |}.

Example minimal_audit_jancar_without_period :
    JancarRunLe (minimal_audit_empty_run 0) (minimal_audit_empty_run 1).
Proof.
  exists (minimal_audit_n1 1). split; [reflexivity|].
  apply jancar_gap_final with (final_offset := minimal_audit_n1 1).
  reflexivity.
Qed.

Example minimal_audit_jancar_not_enough :
    ~ LinearRunLe minimal_audit_empty_period
        (minimal_audit_empty_run 0) (minimal_audit_empty_run 1).
Proof.
  intros [_ [period_input [period_output [[coefficients Hperiod]
    [Hsource Htarget]]]]].
  destruct coefficients using Vector.case0.
  destruct Hperiod as [Hinput _]. cbn in Hinput, Hsource.
  subst period_input.
  pose proof (f_equal (fun value => Vector.nth value Fin.F1) Hsource).
  cbn in H. lia.
Qed.

Definition minimal_audit_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition minimal_audit_up_run : VASRun 1 :=
  {| RunSource := minimal_audit_n1 0;
     RunTargets := [minimal_audit_n1 1] |}.

Definition minimal_audit_plus_two_run : VASRun 1 :=
  {| RunSource := minimal_audit_n1 0;
     RunTargets := [minimal_audit_n1 2] |}.

Definition minimal_audit_target_period : LinearRelationData 1 :=
  {| LinearBaseInput := minimal_audit_n1 0;
     LinearBaseOutput := minimal_audit_n1 1;
     LinearGenerators :=
       [(minimal_audit_n1 0, minimal_audit_n1 1)] |}.

Example minimal_audit_period_increment_without_jancar :
    (exists period_input period_output,
      GeneratedPeriodPair (LinearGenerators minimal_audit_target_period)
        period_input period_output /\
      RunSource minimal_audit_plus_two_run =
        nvec_add (RunSource minimal_audit_up_run) period_input /\
      RunTarget minimal_audit_plus_two_run =
        nvec_add (RunTarget minimal_audit_up_run) period_output) /\
    ~ JancarRunLe minimal_audit_up_run minimal_audit_plus_two_run.
Proof.
  split.
  - exists (minimal_audit_n1 0), (minimal_audit_n1 1). split.
    + exists (minimal_audit_n1 1). split; reflexivity.
    + split; reflexivity.
  - intros Hle. apply jancar_run_le_iff_higman in Hle.
    destruct Hle as [_ Hembed]. cbn in Hembed.
    destruct (list_embed_cons_inv Hembed)
      as [prefix [[action configuration] [suffix [Heq [[Haction _] _]]]]].
    pose proof (f_equal (@length _) Heq) as Hlength.
    rewrite length_app in Hlength. cbn in Hlength.
    assert (prefix = [] /\ suffix = []) as [-> ->].
    { split; apply length_zero_iff_nil; lia. }
    pose proof (f_equal
      (fun values => fst (List.hd
        (minimal_audit_z1 0, minimal_audit_n1 0) values)) Heq) as Hmatched.
    cbn in Hmatched. rewrite <- Hmatched in Haction.
    pose proof (f_equal
      (fun value : ZVec 1 => Vector.nth value Fin.F1) Haction).
    cbn in H. lia.
Qed.

Definition minimal_audit_shift_period : LinearRelationData 1 :=
  {| LinearBaseInput := minimal_audit_n1 0;
     LinearBaseOutput := minimal_audit_n1 1;
     LinearGenerators :=
       [(minimal_audit_n1 1, minimal_audit_n1 1)] |}.

Definition minimal_audit_shifted_up_run : VASRun 1 :=
  {| RunSource := minimal_audit_n1 1;
     RunTargets := [minimal_audit_n1 2] |}.

Example minimal_audit_both_order_conditions :
    LinearRunLe minimal_audit_shift_period
      minimal_audit_up_run minimal_audit_shifted_up_run.
Proof.
  split.
  - exists (minimal_audit_n1 1). split; [reflexivity|].
    eapply jancar_gap_match with
      (gap := []) (offset := minimal_audit_n1 1) (big_tail := []).
    + reflexivity.
    + apply jancar_gap_final with
        (gap := []) (final_offset := minimal_audit_n1 1).
      reflexivity.
  - exists (minimal_audit_n1 1), (minimal_audit_n1 1). split.
    + exists (minimal_audit_n1 1). split; reflexivity.
    + split; reflexivity.
Qed.

Definition minimal_audit_zero_pair : NVec 1 * NVec 1 :=
  (minimal_audit_n1 0, minimal_audit_n1 0).

Definition minimal_audit_coeff_zero : NVec 1 := minimal_audit_n1 0.
Definition minimal_audit_coeff_one : NVec 1 := minimal_audit_n1 1.

Example minimal_audit_nonunique_coefficients :
    GeneratedPeriodPairBy [minimal_audit_zero_pair]
      minimal_audit_coeff_zero (minimal_audit_n1 0) (minimal_audit_n1 0) /\
    GeneratedPeriodPairBy [minimal_audit_zero_pair]
      minimal_audit_coeff_one (minimal_audit_n1 0) (minimal_audit_n1 0) /\
    minimal_audit_coeff_zero <> minimal_audit_coeff_one.
Proof.
  repeat split; cbn; try reflexivity.
  intros Heq.
  pose proof (f_equal (fun value => Vector.nth value Fin.F1) Heq).
  cbn in H. lia.
Qed.

Example minimal_audit_dimension_zero_period :
    GeneratedPeriodPair (@List.nil (NVec 0 * NVec 0))
      (@Vector.nil nat) (@Vector.nil nat).
Proof. apply generated_period_pair_zero. Qed.

Example minimal_audit_empty_omega_has_finite_cover :
    exists basis : list (VASRun 1),
      (forall rho, List.In rho basis ->
        LinearOmegaRun ([] : PlainVAS 1)
          {| LinearBaseInput := minimal_audit_n1 0;
             LinearBaseOutput := minimal_audit_n1 1;
             LinearGenerators := [] |} rho) /\
      (forall sigma,
        LinearOmegaRun ([] : PlainVAS 1)
          {| LinearBaseInput := minimal_audit_n1 0;
             LinearBaseOutput := minimal_audit_n1 1;
             LinearGenerators := [] |} sigma ->
        exists rho, List.In rho basis /\
          LinearRunLe
            {| LinearBaseInput := minimal_audit_n1 0;
               LinearBaseOutput := minimal_audit_n1 1;
               LinearGenerators := [] |} rho sigma).
Proof. apply linear_omega_finite_cover. Qed.

Lemma minimal_audit_empty_system_targets_nil : forall source targets,
    ValidVASTargets ([] : PlainVAS 1) source targets -> targets = [].
Proof.
  intros source [|target tail] Hvalid; [reflexivity|].
  cbn in Hvalid. tauto.
Qed.

Example minimal_audit_omega_really_empty : forall run,
    ~ LinearOmegaRun ([] : PlainVAS 1)
      {| LinearBaseInput := minimal_audit_n1 0;
         LinearBaseOutput := minimal_audit_n1 1;
         LinearGenerators := [] |} run.
Proof.
  intros [source targets] [Hvalid
    [period_input [period_output [[coefficients [Hinput Houtput]]
      [Hsource Htarget]]]]].
  cbn in Hvalid, Hsource, Htarget.
  pose proof (minimal_audit_empty_system_targets_nil source targets Hvalid) as ->.
  destruct coefficients using Vector.case0.
  cbn in Hinput, Houtput, Hsource, Htarget.
  subst period_input period_output.
  pose proof (f_equal (fun value => Vector.nth value Fin.F1)
    (eq_trans (eq_sym Hsource) Htarget)).
  cbn in H. lia.
Qed.

Definition minimal_audit_zero_duplicate_system : PlainVAS 1 :=
  [minimal_audit_z1 0; minimal_audit_z1 0].

Definition minimal_audit_nonzero_base : LinearRelationData 1 :=
  {| LinearBaseInput := minimal_audit_n1 2;
     LinearBaseOutput := minimal_audit_n1 2;
     LinearGenerators := [] |}.

Definition minimal_audit_zero_action_run : VASRun 1 :=
  {| RunSource := minimal_audit_n1 2;
     RunTargets := [minimal_audit_n1 2] |}.

Example minimal_audit_omega_nonempty_zero_duplicate_action :
    LinearOmegaRun minimal_audit_zero_duplicate_system
      minimal_audit_nonzero_base minimal_audit_zero_action_run.
Proof.
  split; [cbn; auto|].
  exists (minimal_audit_n1 0), (minimal_audit_n1 0). split.
  - apply generated_period_pair_zero.
  - split; reflexivity.
Qed.

Check LinearRelationData.
Check GeneratedPeriodPairBy.
Check GeneratedPeriodPair.
Check LinearRelationContains.
Check LinearOmegaRun.
Check LinearRunLe.
Check linear_run_le_refl.
Check linear_run_le_trans.
Check DecoratedLinearRun.
Check DecoratedLinearRunLe.
Check decorated_linear_run_wqo.
Check decorated_linear_run_finite_cover.
Check linear_omega_finite_cover.
Check linear_run_le_transformer_period_witness.

Set Printing Implicit.
Check LinearRelationData.
Check LinearOmegaRun.
Check LinearRunLe.
Check DecoratedLinearRun.
Check DecoratedLinearRunValid.
Check DecoratedLinearRunLe.
Check decorated_linear_run_wqo.
Check decorated_linear_run_finite_cover.
Check linear_omega_finite_cover.
Check linear_run_le_transformer_period_witness.
Unset Printing Implicit.

Print Assumptions generated_period_pair_periodic.
Print Assumptions linear_run_le_refl.
Print Assumptions linear_run_le_trans.
Print Assumptions decorated_linear_run_wqo.
Print Assumptions decorated_linear_run_finite_cover.
Print Assumptions linear_omega_finite_cover.
Print Assumptions linear_run_le_transformer_period_witness.
