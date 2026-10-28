From Coq Require Import List Vector ZArith Lia.
From KruskalHigmanProp Require Import embeddings.list_embed.
From Mell.Core Require Import Vector.
From Mell.VAS Require Import Runs JancarOrder Transformer TransformerJancar.
From Mell.Audit Require Import VASJancarExamples.

Import ListNotations.

Example audit_capacity_zero_up :
    CapacityTransformer audit_vas (audit_n1 0) (audit_n1 0) (audit_n1 1).
Proof. unfold CapacityTransformer. exact audit_up_reachable. Qed.

Example audit_capacity_nonzero_up :
    CapacityTransformer audit_vas (audit_n1 5) (audit_n1 0) (audit_n1 1).
Proof.
  change (CapacityTransformer audit_vas
    (nvec_add (audit_n1 0) (audit_n1 5)) (audit_n1 0) (audit_n1 1)).
  exact (capacity_transformer_capacity_monotone 1 audit_vas
    (audit_n1 0) (audit_n1 5) (audit_n1 0) (audit_n1 1)
    audit_capacity_zero_up).
Qed.

Example audit_capacity_reflexive :
    CapacityTransformer audit_vas (audit_n1 7) (audit_n1 3) (audit_n1 3).
Proof. apply capacity_transformer_refl. Qed.

Example audit_capacity_composition :
    NRelCompose (CapacityTransformer audit_vas (audit_n1 0))
      (CapacityTransformer audit_vas (audit_n1 0))
      (audit_n1 0) (audit_n1 2).
Proof.
  exists (audit_n1 1). split; unfold CapacityTransformer.
  - exact audit_up_reachable.
  - apply vas_reach_run_iff. exists audit_up_from_one.
    split; [destruct audit_same_action_different_configurations as [H _]; exact H|].
    split; reflexivity.
Qed.

Example audit_empty_run_transformer :
    NRelSame (TransformerAlongRun audit_vas (EmptyVASRun (audit_n1 4)))
      (CapacityTransformer audit_vas (audit_n1 4)).
Proof. apply transformer_along_empty_run. Qed.

Example audit_empty_system_transformer_periodic :
    PeriodicNRelation
      (TransformerAlongRun audit_empty_system (EmptyVASRun (audit_n1 3))).
Proof. apply transformer_along_run_periodic. Qed.

Example audit_run_transformer_zero_offsets :
    TransformerAlongRun audit_vas audit_up_run (audit_n1 0) (audit_n1 0).
Proof.
  apply (proj2 (transformer_along_run_iff_jancar_extension
    1 audit_vas audit_up_run (audit_n1 0) (audit_n1 0)
    audit_up_run_valid)).
  exists audit_up_run. split; [exact audit_up_run_valid|].
  split; [apply jancar_run_le_refl|].
  split; reflexivity.
Qed.

Example audit_inserted_gap_realizes_transformer :
    exists sigma,
      ValidVASRun audit_vas sigma /\
      JancarRunLe audit_up_run sigma /\
      RunSource sigma = nvec_add (RunSource audit_up_run) (audit_n1 0) /\
      RunTarget sigma = nvec_add (RunTarget audit_up_run) (audit_n1 0).
Proof.
  apply transformer_realized_by_jancar_extension; [exact audit_up_run_valid|].
  exact audit_run_transformer_zero_offsets.
Qed.

Example audit_existing_nonempty_gap_yields_transformer_offsets :
    exists input output,
      RunSource audit_zero_then_up =
        nvec_add (RunSource audit_up_run) input /\
      RunTarget audit_zero_then_up =
        nvec_add (RunTarget audit_up_run) output /\
      TransformerAlongRun audit_vas audit_up_run input output.
Proof.
  apply jancar_run_le_transformer.
  - exact audit_up_run_valid.
  - exact audit_zero_then_up_valid.
  - exact audit_inserted_zero_jancar.
Qed.

Definition audit_same_end_sigma : VASRun 1 :=
  {| RunSource := audit_n1 0;
     RunTargets := [audit_n1 2; audit_n1 1] |}.

Example audit_same_end_sigma_valid : ValidVASRun audit_vas audit_same_end_sigma.
Proof. cbn. tauto. Qed.

Example audit_same_endpoints_not_enough_for_jancar :
    RunSource audit_up_run = RunSource audit_same_end_sigma /\
    RunTarget audit_up_run = RunTarget audit_same_end_sigma /\
    ~ JancarRunLe audit_up_run audit_same_end_sigma.
Proof.
  split; [reflexivity|]. split; [reflexivity|].
  intros Hle. apply jancar_run_le_iff_higman in Hle.
  destruct Hle as [_ Hembed].
  pose proof (list_embed_in_left_inv Hembed
    (StepAction (audit_n1 0) (audit_n1 1), audit_n1 1)
    (or_introl eq_refl)) as [matched [Hin Hrel]].
  destruct matched as [action configuration].
  destruct Hrel as [Haction _].
  cbn in Hin. destruct Hin as [Heq | [Heq | []]]; inversion Heq; subst action;
    pose proof (f_equal
      (fun value : ZVec 1 => Vector.nth value Fin.F1) Haction) as Hcoordinate;
    cbn in Hcoordinate; lia.
Qed.

(** A zero total displacement does not validate a prescribed word: the
    capacity relation itself remains reflexive via its empty run. *)
Example audit_invalid_word_is_not_transformer_witness :
    ~ exists run : VASRun 1,
      ValidVASRun audit_vas run /\
      RunSource run = nvec_add (audit_n1 0) (audit_n1 0) /\
      RunActionWord run = audit_cancel_word.
Proof. exact audit_invalid_cancel_not_valid. Qed.

Example audit_dimension_zero_transformer_periodic :
    PeriodicNRelation
      (TransformerAlongRun audit_zero_vas audit_zero_run).
Proof. apply transformer_along_run_periodic. Qed.

Set Printing Implicit.
Check NRelation.
Check NRelCompose.
Check PeriodicNRelation.
Check CapacityTransformer.
Check capacity_transformer_periodic.
Check periodic_nrelation_compose.
Check TransformerAlongRun.
Check transformer_along_run_periodic.
Check jancar_run_le_transformer.
Check transformer_realized_by_jancar_extension.
Check transformer_along_run_iff_jancar_extension.
Unset Printing Implicit.

Print Assumptions capacity_transformer_periodic.
Print Assumptions periodic_nrelation_compose.
Print Assumptions transformer_along_run_periodic.
Print Assumptions jancar_run_le_transformer.
Print Assumptions transformer_realized_by_jancar_extension.
Print Assumptions transformer_along_run_iff_jancar_extension.
