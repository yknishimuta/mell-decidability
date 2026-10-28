From Coq Require Import Bool List.
From Mell.Core Require Import Search Vector.
From Mell.Logic Require Import Syntax Calculus Code YallaBridge
  MultiplicativeWeight UnitFragment.
From Mell.BVAS Require Import Runs.
From Mell.BVASS Require Import FiniteSaturation.
From Mell.Decision Require Import BVAS Stage BVASOfSeparator.
From Mell.Reduction Require Import Main FullZeroSystem ZeroTestFree ILZ
  ILZRuntime MELLToABVASSRuntime.

Import ListNotations.

Definition reach_instance_stage (instance : ReachInstance) (stage : nat) :
    option bool :=
  match instance with
  | {| reach_dimension := _; reach_system := system;
       reach_target := target |} => bvas_stage system target stage
  end.

Definition reach_instance_decide (instance : ReachInstance) : bool :=
  match instance with
  | {| reach_dimension := _; reach_system := system;
       reach_target := target |} => bvas_decide system target
  end.

Definition mell_stage_reference (Gamma : sequent) (stage : nat) : option bool :=
  reach_instance_stage (reduce_mell Gamma) stage.

Definition mell_search_fuel_reference (Gamma : sequent) (fuel : nat) : option bool :=
  search_fuel reach_instance_stage (reduce_mell Gamma) fuel.

Definition mell_decide_reference (Gamma : sequent) : bool :=
  reach_instance_decide (reduce_mell Gamma).

(** A bounded, fully verified saturation pass avoids Gödel-certificate search for
    small finite stateful instances.  [None] deliberately falls back to the
    original complete search. *)
Definition mell_saturation_fuel : nat := 6.
Definition mell_goal_saturation_fuel : nat := 9.
Definition mell_saturation_rule_limit : nat := 256.

Definition mell_goal_saturation_decide_with_fuel
    (Gamma : sequent) (fuel : nat) : option bool :=
  let machine := compile_ilz_runtime_goal Gamma in
  match full_zero_test_rules machine with
  | test :: tests => None
  | [] =>
      goal_saturation_decide
        (direct_bottom_up ilz_machine_state_eq_dec machine)
        (direct_root_state ilz_machine_state_eq_dec machine
          (ilz_machine_sequent []
            (snd (Mell.Reduction.ILZRuntime.translate_mell_runtime Gamma))))
        (nvec_zero (length
          (Mell.Reduction.ILZRuntime.runtime_ilz_subformulas
            (Mell.Reduction.ILZRuntime.translate_mell_runtime Gamma))))
        fuel fuel
  end.

Definition mell_goal_saturation_decide (Gamma : sequent) : option bool :=
  match mell_goal_saturation_decide_with_fuel Gamma mell_saturation_fuel with
  | Some true => Some true
  | _ => mell_goal_saturation_decide_with_fuel Gamma mell_goal_saturation_fuel
  end.

Definition mell_full_saturation_decide (Gamma : sequent) : option bool :=
  let machine := compile_ilz_runtime_goal Gamma in
  match full_zero_test_rules machine with
  | test :: tests => None
  | [] =>
      if Nat.leb
           (length (full_zero_unary_rules machine) +
            length (full_zero_split_rules machine))
           mell_saturation_rule_limit
      then saturation_decide (compile_ilz_direct Gamma)
        (ilz_direct_root_state Gamma) (ilz_direct_root_counters Gamma)
        mell_saturation_fuel
      else None
  end.

Definition mell_reach_saturation_decide (Gamma : sequent) : option bool :=
  match mell_goal_saturation_decide Gamma with
  | Some true => Some true
  | _ => mell_full_saturation_decide Gamma
  end.

Definition mell_saturation_decide (Gamma : sequent) : option bool :=
  if unit_sequent_provableb Gamma
  then Some true
  else if multiplicative_weight_refutes Gamma
       then Some false
       else mell_reach_saturation_decide Gamma.

Definition mell_stage (Gamma : sequent) (stage : nat) : option bool :=
  match mell_saturation_decide Gamma with
  | Some answer => Some answer
  | None => mell_stage_reference Gamma stage
  end.

Definition mell_search_fuel (Gamma : sequent) (fuel : nat) : option bool :=
  search_fuel mell_stage Gamma fuel.

Definition mell_decide (Gamma : sequent) : bool :=
  match mell_saturation_decide Gamma with
  | Some answer => answer
  | None => mell_decide_reference Gamma
  end.

Theorem mell_goal_saturation_decide_with_fuel_sound : forall Gamma fuel,
  mell_goal_saturation_decide_with_fuel Gamma fuel = Some true -> Provable Gamma.
Proof.
  intros Gamma fuel Hanswer.
  unfold mell_goal_saturation_decide_with_fuel in Hanswer.
  destruct (full_zero_test_rules (compile_ilz_runtime_goal Gamma))
    as [|test tests] eqn:Htests; [|discriminate].
  pose proof (goal_saturation_decide_sound _ _
    (compile_ilz_direct Gamma) (ilz_direct_root_state Gamma)
    (ilz_direct_root_counters Gamma) fuel fuel Hanswer) as Hreach.
  assert (Hfree : zero_test_freeb (compile_ilz_runtime_goal Gamma) = true).
  { unfold zero_test_freeb. now rewrite Htests. }
  apply (proj2 (ilz_direct_machine_correct Gamma Hfree)). exact Hreach.
Qed.
Theorem mell_goal_saturation_decide_sound : forall Gamma,
  mell_goal_saturation_decide Gamma = Some true -> Provable Gamma.
Proof.
  intros Gamma Hanswer. unfold mell_goal_saturation_decide in Hanswer.
  destruct (mell_goal_saturation_decide_with_fuel Gamma mell_saturation_fuel)
    as [answer|] eqn:Hfirst.
  - destruct answer.
    + apply mell_goal_saturation_decide_with_fuel_sound with
        (fuel := mell_saturation_fuel). exact Hfirst.
    + eapply mell_goal_saturation_decide_with_fuel_sound. exact Hanswer.
  - eapply mell_goal_saturation_decide_with_fuel_sound. exact Hanswer.
Qed.

Theorem mell_full_saturation_decide_sound : forall Gamma answer,
  mell_full_saturation_decide Gamma = Some answer ->
  if answer then Provable Gamma else ~ Provable Gamma.
Proof.
  intros Gamma answer Hanswer. unfold mell_full_saturation_decide in Hanswer.
  destruct (full_zero_test_rules (compile_ilz_runtime_goal Gamma))
    as [|test tests] eqn:Htests; [|discriminate].
  destruct (Nat.leb
    (length (full_zero_unary_rules (compile_ilz_runtime_goal Gamma)) +
     length (full_zero_split_rules (compile_ilz_runtime_goal Gamma)))
    mell_saturation_rule_limit) eqn:Hsmall; [|discriminate].
  pose proof (saturation_decide_sound _ _
    (compile_ilz_direct Gamma) (ilz_direct_root_state Gamma)
    (ilz_direct_root_counters Gamma) mell_saturation_fuel answer Hanswer)
    as Hsound.
  assert (Hfree : zero_test_freeb (compile_ilz_runtime_goal Gamma) = true).
  { unfold zero_test_freeb. now rewrite Htests. }
  destruct answer; cbn in Hsound |- *.
  - apply (proj2 (ilz_direct_machine_correct Gamma Hfree)). exact Hsound.
  - intro Hprovable. apply Hsound.
    apply (proj1 (ilz_direct_machine_correct Gamma Hfree)). exact Hprovable.
Qed.

Theorem mell_reach_saturation_decide_sound : forall Gamma answer,
  mell_reach_saturation_decide Gamma = Some answer ->
  if answer then Provable Gamma else ~ Provable Gamma.
Proof.
  intros Gamma answer Hanswer. unfold mell_reach_saturation_decide in Hanswer.
  destruct (mell_goal_saturation_decide Gamma) as [goal_answer|] eqn:Hgoal.
  - destruct goal_answer.
    + inversion Hanswer; subst. apply mell_goal_saturation_decide_sound.
      exact Hgoal.
    + eapply mell_full_saturation_decide_sound. exact Hanswer.
  - eapply mell_full_saturation_decide_sound. exact Hanswer.
Qed.

Theorem mell_saturation_decide_sound : forall Gamma answer,
  mell_saturation_decide Gamma = Some answer ->
  if answer then Provable Gamma else ~ Provable Gamma.
Proof.
  intros Gamma answer Hanswer. unfold mell_saturation_decide in Hanswer.
  destruct (unit_sequent_provableb Gamma) eqn:Hunit.
  - inversion Hanswer; subst. cbn. now apply unit_sequent_provableb_sound.
  - destruct (multiplicative_weight_refutes Gamma) eqn:Hweight.
    + inversion Hanswer; subst. cbn.
      now apply multiplicative_weight_refutes_sound.
    + eapply mell_reach_saturation_decide_sound. exact Hanswer.
Qed.

Theorem reach_instance_decide_true_iff : forall instance,
  reach_instance_decide instance = true <-> Holds instance.
Proof.
  intros [d system target]. unfold reach_instance_decide, Holds. cbn.
  apply bvas_decide_true_iff.
Qed.

Theorem reach_instance_decide_false_iff : forall instance,
  reach_instance_decide instance = false <-> ~ Holds instance.
Proof.
  intros [d system target]. unfold reach_instance_decide, Holds. cbn.
  apply bvas_decide_false_iff.
Qed.

Theorem mell_decide_true_iff : forall Gamma,
  mell_decide Gamma = true <-> Provable Gamma.
Proof.
  intro Gamma. unfold mell_decide.
  destruct (mell_saturation_decide Gamma) as [answer|] eqn:Hfast.
  - destruct answer.
    + split.
      * intro Htrue. exact (mell_saturation_decide_sound Gamma true Hfast).
      * intro Hprovable. reflexivity.
    + split; [discriminate|]. intro Hprovable.
      exfalso. exact ((mell_saturation_decide_sound Gamma false Hfast) Hprovable).
  - unfold mell_decide_reference. rewrite reach_instance_decide_true_iff.
    symmetry. apply reduce_mell_correct.
Qed.

Theorem mell_decide_false_iff : forall Gamma,
  mell_decide Gamma = false <-> ~ Provable Gamma.
Proof.
  intro Gamma. destruct (mell_decide Gamma) eqn:Hdecide.
  - split; [discriminate|]. intro Hnot.
    exfalso. apply Hnot. exact (proj1 (mell_decide_true_iff Gamma) Hdecide).
  - split.
    + intro Hfalse. intro Hprovable.
      pose proof (proj2 (mell_decide_true_iff Gamma) Hprovable) as Htrue.
      congruence.
    + intro Hnot. reflexivity.
Qed.

Theorem mell_decide_with_cut : forall Gamma,
  mell_decide Gamma = true <-> ProvableWithCut Gamma.
Proof.
  intro Gamma. rewrite mell_decide_true_iff.
  symmetry. apply provable_cut_iff.
Qed.

Theorem mell_stage_sound_true : forall Gamma stage,
  mell_stage Gamma stage = Some true -> Provable Gamma.
Proof.
  intros Gamma stage Hstage. unfold mell_stage in Hstage.
  destruct (mell_saturation_decide Gamma) as [answer|] eqn:Hfast.
  - inversion Hstage; subst.
    exact (mell_saturation_decide_sound Gamma true Hfast).
  - unfold mell_stage_reference, reach_instance_stage in Hstage.
    destruct (reduce_mell Gamma) as [d system target] eqn:Hinstance; cbn in Hstage.
    apply reduce_mell_correct. rewrite Hinstance. unfold Holds. cbn.
    exact (bvas_stage_sound d system target stage true Hstage).
Qed.

Theorem mell_stage_sound_false : forall Gamma stage,
  mell_stage Gamma stage = Some false -> ~ Provable Gamma.
Proof.
  intros Gamma stage Hstage Hprovable.
  unfold mell_stage in Hstage.
  destruct (mell_saturation_decide Gamma) as [answer|] eqn:Hfast.
  - inversion Hstage; subst.
    exact ((mell_saturation_decide_sound Gamma false Hfast) Hprovable).
  - unfold mell_stage_reference, reach_instance_stage in Hstage.
    destruct (reduce_mell Gamma) as [d system target] eqn:Hinstance; cbn in Hstage.
    pose proof (bvas_stage_sound d system target stage false Hstage) as Hnot.
    simpl in Hnot. apply Hnot.
    assert (Hholds : Holds (reduce_mell Gamma)).
    { apply reduce_mell_correct. exact Hprovable. }
    rewrite Hinstance in Hholds. exact Hholds.
Qed.

Theorem mell_search_fuel_sound_true : forall Gamma fuel,
  mell_search_fuel Gamma fuel = Some true -> Provable Gamma.
Proof.
  intros Gamma fuel Hfuel. unfold mell_search_fuel in Hfuel.
  destruct (search_fuel_sound mell_stage Gamma
    fuel true Hfuel) as [stage [_ Hstage]].
  exact (mell_stage_sound_true Gamma stage Hstage).
Qed.

Theorem mell_search_fuel_sound_false : forall Gamma fuel,
  mell_search_fuel Gamma fuel = Some false -> ~ Provable Gamma.
Proof.
  intros Gamma fuel Hfuel. unfold mell_search_fuel in Hfuel.
  destruct (search_fuel_sound mell_stage Gamma
    fuel false Hfuel) as [stage [_ Hstage]].
  exact (mell_stage_sound_false Gamma stage Hstage).
Qed.

Theorem mell_search_halts : forall Gamma,
  exists fuel answer, mell_search_fuel Gamma fuel = Some answer.
Proof.
  intro Gamma. unfold mell_search_fuel.
  destruct (mell_saturation_decide Gamma) as [answer|] eqn:Hfast.
  - exists 1, answer. cbn. unfold mell_stage. now rewrite Hfast.
  - destruct (reduce_mell Gamma) as [d system target] eqn:Hinstance.
    destruct (bvas_stage_eventual_of_separator proved_singleton_separator
      d system target) as [stage Hhit].
    destruct (bvas_stage system target stage) as [answer|] eqn:Hstage.
    + assert (Hmell_stage : mell_stage Gamma stage = Some answer).
      { unfold mell_stage, mell_stage_reference, reach_instance_stage.
        rewrite Hfast, Hinstance. exact Hstage. }
      destruct (search_fuel_eventually_hits mell_stage Gamma
        stage answer Hmell_stage) as [result Hresult].
      exists (S stage), result. exact Hresult.
    + exfalso. apply Hhit. reflexivity.
Qed.

Theorem mell_search_fuel_agrees : forall Gamma fuel answer,
  mell_search_fuel Gamma fuel = Some answer -> answer = mell_decide Gamma.
Proof.
  intros Gamma fuel answer Hanswer.
  destruct answer, (mell_decide Gamma) eqn:Hdecide; try reflexivity.
  - exfalso. apply (proj1 (mell_decide_false_iff Gamma) Hdecide).
    exact (mell_search_fuel_sound_true Gamma fuel Hanswer).
  - exfalso. apply (mell_search_fuel_sound_false Gamma fuel Hanswer).
    exact (proj1 (mell_decide_true_iff Gamma) Hdecide).
Qed.

Theorem decode_encode_sequent : forall Gamma,
  decode_sequent (encode_sequent Gamma) = Some Gamma.
Proof. apply decode_sequent_encode. Qed.

Definition decide_code (code : nat) : bool :=
  match decode_sequent code with
  | Some Gamma => mell_decide Gamma
  | None => false
  end.

Theorem decide_code_invalid : forall code,
  decode_sequent code = None -> decide_code code = false.
Proof. intros code Hdecode. unfold decide_code. now rewrite Hdecode. Qed.

Theorem decide_code_correct : forall code,
  decide_code code = true <->
  exists Gamma, decode_sequent code = Some Gamma /\ Provable Gamma.
Proof.
  intro code. unfold decide_code.
  destruct (decode_sequent code) as [Gamma|] eqn:Hdecode.
  - rewrite mell_decide_true_iff. split.
    + intro H. exists Gamma. auto.
    + intros [Gamma' [Heq Hprovable]]. inversion Heq; subst. exact Hprovable.
  - split; [discriminate|]. intros [Gamma [Heq _]]. congruence.
Qed.

Theorem decide_code_encode : forall Gamma,
  decide_code (encode_sequent Gamma) = mell_decide Gamma.
Proof.
  intro Gamma. unfold decide_code. now rewrite decode_sequent_encode.
Qed.
