From Coq Require Import Bool List.
From Mell.Core Require Import Search.
From Mell.Logic Require Import Syntax Calculus UnitFragment MultiplicativeWeight.
From Mell.BVAS Require Import Runs.
From Mell.Decision Require Import MELL BVAS Stage.
From Mell.Reduction Require Import Main.

Import ListNotations.

(** These constructors are the executable branches that occur in the current
    public dispatcher.  Goal saturation is a YES-only precheck; full
    saturation may return either answer. *)
Inductive DecisionPath : Type :=
| UnitPath
| WeightPath
| GoalSaturationPath
| FullSaturationPath
| FallbackPath.

Definition traced_mell_decide (Gamma : sequent) : DecisionPath * bool :=
  if unit_sequent_provableb Gamma
  then (UnitPath, true)
  else if multiplicative_weight_refutes Gamma
       then (WeightPath, false)
       else
         match mell_goal_saturation_decide Gamma with
         | Some true => (GoalSaturationPath, true)
         | _ =>
             match mell_full_saturation_decide Gamma with
             | Some answer => (FullSaturationPath, answer)
             | None => (FallbackPath, mell_decide_reference Gamma)
             end
         end.

Definition mell_decision_path (Gamma : sequent) : DecisionPath :=
  fst (traced_mell_decide Gamma).

Theorem traced_mell_decide_result : forall Gamma,
  snd (traced_mell_decide Gamma) = mell_decide Gamma.
Proof.
  intro Gamma.
  unfold traced_mell_decide, mell_decide, mell_saturation_decide,
    mell_reach_saturation_decide.
  destruct (unit_sequent_provableb Gamma); [reflexivity|].
  destruct (multiplicative_weight_refutes Gamma); [reflexivity|].
  destruct (mell_goal_saturation_decide Gamma) as [[|]|];
    destruct (mell_full_saturation_decide Gamma) as [[|]|]; reflexivity.
Qed.

Theorem decision_path_unit_guard : forall Gamma,
  mell_decision_path Gamma = UnitPath <->
  unit_sequent_provableb Gamma = true.
Proof.
  intro Gamma. unfold mell_decision_path, traced_mell_decide.
  destruct (unit_sequent_provableb Gamma); split; intro H; try reflexivity;
    try discriminate.
  destruct (multiplicative_weight_refutes Gamma); [discriminate|].
  destruct (mell_goal_saturation_decide Gamma) as [[|]|];
    destruct (mell_full_saturation_decide Gamma) as [[|]|]; discriminate.
Qed.

Theorem decision_path_weight_guard : forall Gamma,
  mell_decision_path Gamma = WeightPath <->
  unit_sequent_provableb Gamma = false /\
  multiplicative_weight_refutes Gamma = true.
Proof.
  intro Gamma. unfold mell_decision_path, traced_mell_decide.
  destruct (unit_sequent_provableb Gamma) eqn:Hunit.
  - split; [discriminate|intros [H _]; discriminate].
  - destruct (multiplicative_weight_refutes Gamma) eqn:Hweight.
    + split; intro H; [now split|reflexivity].
    + split.
      * intro H. destruct (mell_goal_saturation_decide Gamma) as [[|]|];
          try discriminate;
          destruct (mell_full_saturation_decide Gamma); discriminate.
      * intros [_ H]. discriminate.
Qed.

Theorem decision_path_goal_saturation_guard : forall Gamma,
  mell_decision_path Gamma = GoalSaturationPath <->
  unit_sequent_provableb Gamma = false /\
  multiplicative_weight_refutes Gamma = false /\
  mell_goal_saturation_decide Gamma = Some true.
Proof.
  intro Gamma. unfold mell_decision_path, traced_mell_decide.
  destruct (unit_sequent_provableb Gamma) eqn:Hunit.
  - split; [discriminate|intros [H _]; discriminate].
  - destruct (multiplicative_weight_refutes Gamma) eqn:Hweight;
      [split; [discriminate|intros [_ [H _]]; discriminate]|].
    destruct (mell_goal_saturation_decide Gamma) as [[|]|] eqn:Hgoal.
  - split; intro H; [repeat split; assumption|reflexivity].
  - split; [intro H; destruct (mell_full_saturation_decide Gamma); discriminate|
      intros [_ [_ H]]; discriminate].
  - split; [intro H; destruct (mell_full_saturation_decide Gamma); discriminate|
      intros [_ [_ H]]; discriminate].
Qed.

Theorem decision_path_full_saturation_guard : forall Gamma,
  mell_decision_path Gamma = FullSaturationPath <->
  unit_sequent_provableb Gamma = false /\
  multiplicative_weight_refutes Gamma = false /\
  mell_goal_saturation_decide Gamma <> Some true /\
  exists answer, mell_full_saturation_decide Gamma = Some answer.
Proof.
  intro Gamma. unfold mell_decision_path, traced_mell_decide.
  destruct (unit_sequent_provableb Gamma) eqn:Hunit.
  - split; [discriminate|intros [H _]; discriminate].
  - destruct (multiplicative_weight_refutes Gamma) eqn:Hweight;
      [split; [discriminate|intros [_ [H _]]; discriminate]|].
    destruct (mell_goal_saturation_decide Gamma) as [[|]|] eqn:Hgoal.
  - split; [discriminate|intros [_ [_ [H _]]]; contradiction].
  - destruct (mell_full_saturation_decide Gamma) as [answer|] eqn:Hfull.
    + split; intro H.
      * repeat split; try assumption; [discriminate|now exists answer].
      * reflexivity.
    + split; [discriminate|intros [_ [_ [_ [answer H]]]]; discriminate].
  - destruct (mell_full_saturation_decide Gamma) as [answer|] eqn:Hfull.
    + split; intro H.
      * repeat split; try assumption; [discriminate|now exists answer].
      * reflexivity.
    + split; [discriminate|intros [_ [_ [_ [answer H]]]]; discriminate].
Qed.

Theorem decision_path_fallback_guard : forall Gamma,
  mell_decision_path Gamma = FallbackPath <->
  unit_sequent_provableb Gamma = false /\
  multiplicative_weight_refutes Gamma = false /\
  mell_goal_saturation_decide Gamma <> Some true /\
  mell_full_saturation_decide Gamma = None.
Proof.
  intro Gamma. unfold mell_decision_path, traced_mell_decide.
  destruct (unit_sequent_provableb Gamma) eqn:Hunit.
  - split; [discriminate|intros [H _]; discriminate].
  - destruct (multiplicative_weight_refutes Gamma) eqn:Hweight;
      [split; [discriminate|intros [_ [H _]]; discriminate]|].
    destruct (mell_goal_saturation_decide Gamma) as [[|]|] eqn:Hgoal.
  - split; [discriminate|intros [_ [_ [H _]]]; contradiction].
  - destruct (mell_full_saturation_decide Gamma) eqn:Hfull.
    + split; [discriminate|intros [_ [_ [_ H]]]; discriminate].
    + split; intro H; [repeat split; try assumption; discriminate|reflexivity].
  - destruct (mell_full_saturation_decide Gamma) eqn:Hfull.
    + split; [discriminate|intros [_ [_ [_ H]]]; discriminate].
    + split; intro H; [repeat split; try assumption; discriminate|reflexivity].
Qed.

Theorem traced_mell_decide_sound : forall Gamma,
  if snd (traced_mell_decide Gamma)
  then Provable Gamma
  else ~ Provable Gamma.
Proof.
  intro Gamma. rewrite traced_mell_decide_result.
  destruct (mell_decide Gamma) eqn:Hanswer; cbn.
  - now apply (proj1 (mell_decide_true_iff Gamma)).
  - now apply (proj1 (mell_decide_false_iff Gamma)).
Qed.

(** The reference functions are the complete certificate-search fallback,
    independently of every fast precheck. *)
Theorem mell_fallback_stage_sound_true : forall Gamma stage,
  mell_stage_reference Gamma stage = Some true -> Provable Gamma.
Proof.
  intros Gamma stage Hstage.
  unfold mell_stage_reference, reach_instance_stage in Hstage.
  destruct (reduce_mell Gamma) as [d system target] eqn:Hinstance; cbn in Hstage.
  apply reduce_mell_correct. rewrite Hinstance. unfold Holds. cbn.
  exact (bvas_stage_sound d system target stage true Hstage).
Qed.

Theorem mell_fallback_stage_sound_false : forall Gamma stage,
  mell_stage_reference Gamma stage = Some false -> ~ Provable Gamma.
Proof.
  intros Gamma stage Hstage Hprovable.
  unfold mell_stage_reference, reach_instance_stage in Hstage.
  destruct (reduce_mell Gamma) as [d system target] eqn:Hinstance; cbn in Hstage.
  pose proof (bvas_stage_sound d system target stage false Hstage) as Hnot.
  cbn in Hnot. apply Hnot.
  assert (Hholds : Holds (reduce_mell Gamma)).
  { apply reduce_mell_correct. exact Hprovable. }
  now rewrite Hinstance in Hholds.
Qed.

Theorem mell_fallback_stage_eventual : forall Gamma,
  exists stage, mell_stage_reference Gamma stage <> None.
Proof.
  intro Gamma.
  destruct (reduce_mell Gamma) as [d system target] eqn:Hinstance.
  destruct (bvas_stage_eventual_of_separator proved_singleton_separator
    d system target) as [stage Hstage].
  exists stage. unfold mell_stage_reference, reach_instance_stage.
  now rewrite Hinstance.
Qed.

Theorem mell_fallback_search_fuel_sound_true : forall Gamma fuel,
  mell_search_fuel_reference Gamma fuel = Some true -> Provable Gamma.
Proof.
  intros Gamma fuel Hfuel. unfold mell_search_fuel_reference in Hfuel.
  destruct (search_fuel_sound reach_instance_stage (reduce_mell Gamma)
    fuel true Hfuel) as [stage [_ Hstage]].
  unfold mell_stage_reference. exact (mell_fallback_stage_sound_true _ _ Hstage).
Qed.

Theorem mell_fallback_search_fuel_sound_false : forall Gamma fuel,
  mell_search_fuel_reference Gamma fuel = Some false -> ~ Provable Gamma.
Proof.
  intros Gamma fuel Hfuel. unfold mell_search_fuel_reference in Hfuel.
  destruct (search_fuel_sound reach_instance_stage (reduce_mell Gamma)
    fuel false Hfuel) as [stage [_ Hstage]].
  unfold mell_stage_reference. exact (mell_fallback_stage_sound_false _ _ Hstage).
Qed.

Theorem mell_fallback_search_halts : forall Gamma,
  exists fuel answer, mell_search_fuel_reference Gamma fuel = Some answer.
Proof.
  intro Gamma.
  destruct (mell_fallback_stage_eventual Gamma) as [stage Hhit].
  destruct (mell_stage_reference Gamma stage) as [answer|] eqn:Hstage.
  - unfold mell_search_fuel_reference, mell_stage_reference.
    destruct (search_fuel_eventually_hits reach_instance_stage
      (reduce_mell Gamma) stage answer Hstage) as [result Hresult].
    exists (S stage), result. exact Hresult.
  - exfalso. apply Hhit. reflexivity.
Qed.

Theorem mell_fallback_decide_true_iff : forall Gamma,
  mell_decide_reference Gamma = true <-> Provable Gamma.
Proof.
  intro Gamma. unfold mell_decide_reference.
  rewrite reach_instance_decide_true_iff. symmetry. apply reduce_mell_correct.
Qed.

Theorem mell_fallback_decide_false_iff : forall Gamma,
  mell_decide_reference Gamma = false <-> ~ Provable Gamma.
Proof.
  intro Gamma. unfold mell_decide_reference.
  rewrite reach_instance_decide_false_iff. split.
  - intros Hnot Hprovable. apply Hnot. now apply reduce_mell_correct.
  - intros Hnot Hholds. apply Hnot. now apply reduce_mell_correct.
Qed.

Theorem mell_fallback_decide_agrees : forall Gamma,
  mell_decide_reference Gamma = mell_decide Gamma.
Proof.
  intro Gamma.
  destruct (mell_decide_reference Gamma) eqn:Hreference,
    (mell_decide Gamma) eqn:Hpublic; try reflexivity.
  - exfalso. apply (proj1 (mell_decide_false_iff Gamma) Hpublic).
    now apply (proj1 (mell_fallback_decide_true_iff Gamma)).
  - exfalso. apply (proj1 (mell_fallback_decide_false_iff Gamma) Hreference).
    now apply (proj1 (mell_decide_true_iff Gamma)).
Qed.

Theorem mell_fallback_search_fuel_agrees : forall Gamma fuel answer,
  mell_search_fuel_reference Gamma fuel = Some answer ->
  answer = mell_decide Gamma.
Proof.
  intros Gamma fuel answer Hanswer.
  destruct answer, (mell_decide Gamma) eqn:Hpublic; try reflexivity.
  - exfalso. apply (proj1 (mell_decide_false_iff Gamma) Hpublic).
    exact (mell_fallback_search_fuel_sound_true _ _ Hanswer).
  - exfalso. apply (mell_fallback_search_fuel_sound_false _ _ Hanswer).
    now apply (proj1 (mell_decide_true_iff Gamma)).
Qed.
