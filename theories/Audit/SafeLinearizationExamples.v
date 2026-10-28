From Coq Require Import List Sorting.Permutation Lia.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import LinearEquations Closure.
From Mell.VAS Require Import Intraproductions.
From Mell.BVAS Require Import OneSourceReduction.
From Mell.WSVAS Require Import SemilinearRayOrder.
From Mell.WSVAS Require Import SafeLinearization.
From Mell.WSVAS Require Import BVASSimulation.
From Mell.Separator Require Import SafeLinearization.

Import ListNotations.

Check SourceMultiShuffle.
Check ReachFromNonemptyShuffle.
Check lemma_5_7_one_source_reduction.
Check RayLe.
Check semilinear_ray_almost_full.
Check semilinear_complement_ray_almost_full.
Check ClosedLinearizationN.
Check ReachWSVASFromSet.
Check lemma_5_4_wsvas_safe_linearization.
Check IBVASInductiveInvariant.
Check lemma_5_1_bvas_safe_linearization.

Section SourceOccurrenceRegressions.
  Context {d : nat} (value : NVec d).

  Example empty_word_is_not_nonempty_source (X I : NVec d -> Prop) :
    ~ SourceMultiShuffle X I [].
  Proof.
    intros [xs [is [Hnonempty [_ [_ Hpermutation]]]]].
    apply Permutation_length in Hpermutation. cbn in Hpermutation.
    rewrite length_app in Hpermutation.
    destruct xs; [contradiction|]. cbn in Hpermutation. lia.
  Qed.

  Example singleton_is_one_source :
    SourceShuffle (fun x => x = value) (fun _ => False) [value].
  Proof.
    exists [], value, []. repeat split; cbn; auto.
  Qed.

  Example equal_values_remain_two_source_occurrences :
    SourceMultiShuffle (fun x => x = value) (fun x => x = value)
      [value; value].
  Proof.
    exists [value], [value]. repeat split.
    - discriminate.
    - constructor; [reflexivity|constructor].
    - constructor; [reflexivity|constructor].
    - apply Permutation_refl.
  Qed.

  Example singleton_is_nonempty_multi_source :
    SourceMultiShuffle (fun x => x = value) (fun _ => False) [value].
  Proof.
    exists [value], []. repeat split.
    - discriminate.
    - constructor; [reflexivity|constructor].
    - constructor.
    - apply Permutation_refl.
  Qed.
End SourceOccurrenceRegressions.

Section RayRegressions.
  Context {d : nat} (set : NVec d -> Prop) (value : NVec d).

  Example ray_le_is_reflexive_on_members :
    set value -> RayLe set value value.
  Proof.
    intro Hvalue. exists (nvec_zero d). split.
    - symmetry. apply nvec_add_zero_right_local.
    - intro coefficient.
      rewrite nvec_scale_zero_vector, nvec_add_zero_right_local.
      exact Hvalue.
  Qed.

  Example zero_period_set_is_periodic :
    PeriodicNSet (fun offset : NVec d => offset = nvec_zero d).
  Proof.
    split; [reflexivity|]. intros left right -> ->.
    apply nvec_add_zero_left_local.
  Qed.
End RayRegressions.

Example dimension_zero_ray :
  RayLe (fun _ : NVec 0 => True) (nvec_zero 0) (nvec_zero 0).
Proof. apply ray_le_is_reflexive_on_members. exact I. Qed.

Print Assumptions lemma_5_7_one_source_reduction.
Print Assumptions semilinear_ray_almost_full.
Print Assumptions lemma_5_4_wsvas_safe_linearization.
Print Assumptions lemma_5_1_bvas_safe_linearization.
