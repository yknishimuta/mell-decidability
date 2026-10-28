From Coq Require Import List Vector ZArith Lia Program.Equality.
From KruskalAfProp Require Import af.af.
From KruskalHigmanProp Require Import embeddings.list_embed.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.VAS Require Import Runs JancarOrder.

Import ListNotations.
Open Scope Z_scope.

Definition audit_n1 (n : nat) : NVec 1 :=
  @Vector.cons nat n 0 (@Vector.nil nat).

Definition audit_z1 (z : Z) : ZVec 1 :=
  @Vector.cons Z z 0 (@Vector.nil Z).

Definition audit_vas : PlainVAS 1 :=
  [audit_z1 1; audit_z1 (-1); audit_z1 0; audit_z1 1; audit_z1 2].

Definition audit_up_run : VASRun 1 :=
  {| RunSource := audit_n1 0;
     RunTargets := [audit_n1 1] |}.

Example audit_up_run_valid : ValidVASRun audit_vas audit_up_run.
Proof. repeat split; cbn; auto. Qed.

Example audit_up_reachable :
    PlainVASReach audit_vas (audit_n1 0) (audit_n1 1).
Proof.
  apply vas_reach_run_iff. exists audit_up_run.
  split; [apply audit_up_run_valid|split; reflexivity].
Qed.

Example audit_empty_run_valid :
    ValidVASRun audit_vas (EmptyVASRun (audit_n1 7)).
Proof. apply empty_vas_run_valid. Qed.

Example audit_reach_reflexive :
    PlainVASReach audit_vas (audit_n1 7) (audit_n1 7).
Proof. constructor. Qed.

Definition audit_empty_system : PlainVAS 1 := [].

Example audit_empty_system_accepts_empty_run :
    ValidVASRun audit_empty_system (EmptyVASRun (audit_n1 3)).
Proof. reflexivity. Qed.

Example audit_empty_system_rejects_step :
    ~ ValidVASRun audit_empty_system audit_up_run.
Proof. cbn. tauto. Qed.

Definition audit_cancel_word : list (ZVec 1) := [audit_z1 (-1); audit_z1 1].

Example audit_invalid_cancel_displacement_zero :
    ActionDisplacement audit_cancel_word = zvec_zero 1.
Proof. reflexivity. Qed.

Example audit_invalid_cancel_not_valid :
    ~ exists run : VASRun 1,
      ValidVASRun audit_vas run /\
      RunSource run = audit_n1 0 /\
      RunActionWord run = audit_cancel_word.
Proof.
  intros [[source targets] [_ [Hsource Hword]]]. cbn in Hsource, Hword.
  subst source. destruct targets as [|target tail]; [discriminate|].
  inversion Hword.
  pose proof (f_equal
    (fun value : ZVec 1 => Vector.nth value Fin.F1) H0) as Hcoordinate.
  unfold StepAction, zvec_sub_run, nvec_to_zvec in Hcoordinate.
  repeat rewrite (nth_map2 Z.sub _ _ Fin.F1 Fin.F1 Fin.F1 eq_refl eq_refl)
    in Hcoordinate.
  repeat rewrite (nth_map Z.of_nat _ Fin.F1 Fin.F1 eq_refl) in Hcoordinate.
  cbn in Hcoordinate. lia.
Qed.

Definition audit_valid_cancel_run : VASRun 1 :=
  {| RunSource := audit_n1 1;
     RunTargets := [audit_n1 0; audit_n1 1] |}.

Example audit_valid_cancel : ValidVASRun audit_vas audit_valid_cancel_run.
Proof. repeat split; cbn; auto. Qed.

Example audit_same_endpoints_different_words :
    RunSource (EmptyVASRun (audit_n1 1)) = RunSource audit_valid_cancel_run /\
    RunTarget (EmptyVASRun (audit_n1 1)) = RunTarget audit_valid_cancel_run /\
    RunActionWord (EmptyVASRun (audit_n1 1)) <>
      RunActionWord audit_valid_cancel_run.
Proof. repeat split; cbn; discriminate. Qed.

Definition audit_up_from_one : VASRun 1 :=
  {| RunSource := audit_n1 1;
     RunTargets := [audit_n1 2] |}.

Example audit_same_action_different_configurations :
    ValidVASRun audit_vas audit_up_from_one /\
    RunActionWord audit_up_run = RunActionWord audit_up_from_one /\
    audit_up_run <> audit_up_from_one.
Proof.
  repeat split; cbn; auto.
  intro Heq. pose proof (f_equal RunSource Heq). discriminate.
Qed.

Example audit_shift_valid :
    ValidVASRun audit_vas (ShiftVASRun (audit_n1 9) audit_valid_cancel_run).
Proof. apply vas_run_shift_valid, audit_valid_cancel. Qed.

Example audit_shift_action_word_unchanged :
    RunActionWord (ShiftVASRun (audit_n1 9) audit_valid_cancel_run) =
    RunActionWord audit_valid_cancel_run.
Proof. apply shift_run_action_word. Qed.

Definition audit_zero_then_up : VASRun 1 :=
  {| RunSource := audit_n1 0;
     RunTargets := [audit_n1 0; audit_n1 1] |}.

Example audit_zero_then_up_valid : ValidVASRun audit_vas audit_zero_then_up.
Proof. repeat split; cbn; auto. Qed.

Example audit_inserted_zero_jancar :
    JancarRunLe audit_up_run audit_zero_then_up.
Proof.
  apply jancar_run_le_iff_higman. split.
  - split; apply nvec_le_refl.
  - cbn. constructor 3. constructor 2.
    + split; [reflexivity|apply nvec_le_refl].
    + constructor.
Qed.

Example audit_jancar_reflexive : JancarRunLe audit_valid_cancel_run audit_valid_cancel_run.
Proof. apply jancar_run_le_refl. Qed.

Example audit_jancar_transitive : forall left middle right : VASRun 1,
    JancarRunLe left middle -> JancarRunLe middle right ->
    JancarRunLe left right.
Proof. exact (jancar_run_le_trans 1). Qed.

Example audit_empty_word_jancar :
    JancarRunLe (EmptyVASRun (audit_n1 0)) audit_zero_then_up.
Proof.
  exists (audit_n1 0). split; [reflexivity|].
  apply jancar_gap_final with (final_offset := audit_n1 1). reflexivity.
Qed.

Definition audit_plus_two : VASRun 1 :=
  {| RunSource := audit_n1 0;
     RunTargets := [audit_n1 2] |}.

Example audit_action_mismatch_not_jancar :
    ~ JancarRunLe audit_up_run audit_plus_two.
Proof.
  intros Hle. apply jancar_run_le_iff_higman in Hle.
  destruct Hle as [_ Hembed]. cbn in Hembed.
  destruct (list_embed_cons_inv Hembed)
    as [prefix [[action configuration] [suffix [Heq [[Haction _] _]]]]].
  pose proof (f_equal (@length _) Heq) as Hlength.
  rewrite length_app in Hlength. cbn in Hlength.
  assert (prefix = [] /\ suffix = []) as [-> ->].
  { split; apply length_zero_iff_nil; lia. }
  pose proof (f_equal
    (fun values => fst (List.hd (audit_z1 0, audit_n1 0) values)) Heq)
    as Hmatched.
  cbn in Hmatched. rewrite <- Hmatched in Haction.
  pose proof (f_equal
    (fun value : ZVec 1 => Vector.nth value Fin.F1) Haction).
  cbn in H. lia.
Qed.

Example audit_source_direction_required :
    ~ JancarRunLe (EmptyVASRun (audit_n1 1)) (EmptyVASRun (audit_n1 0)).
Proof.
  intros Hle. apply jancar_run_le_iff_higman in Hle.
  destruct Hle as [[Hsource _] _].
  specialize (Hsource Fin.F1). cbn in Hsource. lia.
Qed.

Example audit_target_direction_required :
    ~ JancarRunLe audit_up_run (EmptyVASRun (audit_n1 0)).
Proof.
  intros Hle. apply jancar_run_le_iff_higman in Hle.
  destruct Hle as [[_ Htarget] _].
  specialize (Htarget Fin.F1). cbn in Htarget. lia.
Qed.

Definition audit_zero_action : ZVec 0 := @Vector.nil Z.
Definition audit_zero_vas : PlainVAS 0 := [audit_zero_action].
Definition audit_zero_run : VASRun 0 :=
  {| RunSource := @Vector.nil nat;
     RunTargets := [@Vector.nil nat] |}.

Example audit_dimension_zero_valid : ValidVASRun audit_zero_vas audit_zero_run.
Proof. repeat split; cbn; auto. Qed.

Example audit_dimension_zero_length_matters :
    JancarRunLe (EmptyVASRun (@Vector.nil nat)) audit_zero_run.
Proof.
  exists (@Vector.nil nat). split; [reflexivity|].
  apply jancar_gap_final with (final_offset := @Vector.nil nat). reflexivity.
Qed.

Set Printing Implicit.
Check PlainVAS.
Check PlainVASStep.
Check plain_vas_step_iff.
Check VASRun.
Check ValidVASRun.
Check PlainVASReach.
Check vas_reach_run_iff.
Check vas_reach_monotone.
Check JancarRunLe.
Check RunDirectionLe.
Check RunAnnotatedWord.
Check HigmanRunEmbed.
Check jancar_run_le_iff_higman.
Check jancar_run_wqo.
Unset Printing Implicit.

Print Assumptions vas_reach_run_iff.
Print Assumptions vas_reach_monotone.
Print Assumptions jancar_run_le_iff_higman.
Print Assumptions jancar_run_wqo.
