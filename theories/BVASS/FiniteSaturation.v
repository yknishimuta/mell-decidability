From Coq Require Import List Vector ZArith Bool Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVASS Require Import Stateful.

Import ListNotations.

Definition sconfig_eq_dec {d q} :
    forall left right : SConfig d q, {left = right} + {left <> right}.
Proof.
  decide equality; [apply nvec_eq_dec | apply Fin.eq_dec].
Defined.

Fixpoint config_choices_for_states {d q}
    (states : list (Fin.t q)) (known : list (SConfig d q))
    : list (list (SConfig d q)) :=
  match states with
  | [] => [[]]
  | state :: states' =>
      List.flat_map
        (fun config =>
           if Fin.eq_dec (fst config) state
           then List.map (List.cons config)
                  (config_choices_for_states states' known)
           else [])
        known
  end.

Lemma config_choices_for_states_spec : forall d q
    (states : list (Fin.t q)) (known : list (SConfig d q)) configs,
  List.In configs (config_choices_for_states states known) <->
  List.map fst configs = states /\
  List.Forall (fun config => List.In config known) configs.
Proof.
  intros d q states; induction states as [|state states IH];
    intros known configs; cbn.
  - split.
    + intros [Heq|Hbad]; [subst configs; split; constructor|contradiction].
    + intros [Hmap _]. destruct configs; [now left|discriminate].
  - rewrite in_flat_map. split.
    + intros [config [Hknown Hchosen]].
      destruct (Fin.eq_dec (fst config) state) as [Hstate|Hstate];
        [|contradiction].
      apply in_map_iff in Hchosen.
      destruct Hchosen as [tail [<- Htail]].
      apply IH in Htail. destruct Htail as [Hmap Hforall].
      cbn. subst state. split; [now rewrite Hmap|constructor; assumption].
    + intros [Hmap Hforall].
      destruct configs as [|config tail]; [discriminate|].
      cbn in Hmap.
      assert (Hstate : fst config = state) by congruence.
      assert (Htailmap : List.map fst tail = states) by congruence.
      pose proof (Forall_inv Hforall) as Hknown.
      pose proof (Forall_inv_tail Hforall) as Htailforall.
      exists config. split; [exact Hknown|].
      destruct (Fin.eq_dec (fst config) state) as [Heq|Hbad];
        [|contradiction].
      apply in_map_iff. exists tail. split; [reflexivity|].
      apply IH. split; [exact Htailmap|exact Htailforall].
Qed.

Definition rule_results {d q} (rule : SRule d q)
    (known : list (SConfig d q)) : list (SConfig d q) :=
  List.flat_map
    (fun children =>
       match add_displacement (rule_delta rule) (List.map snd children) with
       | Some result => [(output_state rule, result)]
       | None => []
       end)
    (config_choices_for_states (input_states rule) known).

Definition saturation_one_step {d q} (system : SBVAS d q)
    (known : list (SConfig d q)) : list (SConfig d q) :=
  List.flat_map (fun rule => rule_results rule known)
    (stateful_rules system).

Definition saturation_step {d q} (system : SBVAS d q)
    (known : list (SConfig d q)) : list (SConfig d q) :=
  List.nodup sconfig_eq_dec (known ++ saturation_one_step system known).

Fixpoint saturation_configs {d q} (system : SBVAS d q) (fuel : nat)
    : list (SConfig d q) :=
  match fuel with
  | 0 => List.nodup sconfig_eq_dec (initial_configs system)
  | S fuel' => saturation_step system (saturation_configs system fuel')
  end.

Lemma in_saturation_step_iff : forall d q (system : SBVAS d q) known config,
  List.In config (saturation_step system known) <->
  List.In config known \/ List.In config (saturation_one_step system known).
Proof.
  intros. unfold saturation_step. rewrite nodup_In, in_app_iff. reflexivity.
Qed.

Lemma saturation_configs_monotone : forall d q (system : SBVAS d q) fuel config,
  List.In config (saturation_configs system fuel) ->
  List.In config (saturation_configs system (S fuel)).
Proof.
  intros. apply in_saturation_step_iff. now left.
Qed.

Lemma saturation_configs_initial : forall d q (system : SBVAS d q)
    fuel config,
  List.In config (initial_configs system) ->
  List.In config (saturation_configs system fuel).
Proof.
  intros d q system fuel. induction fuel as [|fuel IH]; intros config Hin; cbn.
  - now apply nodup_In.
  - apply saturation_configs_monotone. now apply IH.
Qed.

Lemma rule_results_sound : forall d q (system : SBVAS d q) known rule config,
  List.In rule (stateful_rules system) ->
  (forall child, List.In child known ->
     SReach system (fst child) (snd child)) ->
  List.In config (rule_results rule known) ->
  SReach system (fst config) (snd config).
Proof.
  intros d q system known rule config Hrule Hknown Hin.
  unfold rule_results in Hin. apply in_flat_map in Hin.
  destruct Hin as [children [Hchoices Hresult]].
  apply config_choices_for_states_spec in Hchoices.
  destruct Hchoices as [Hstates Hchildren].
  destruct (add_displacement (rule_delta rule) (List.map snd children))
    as [result|] eqn:Happly; [|contradiction].
  destruct Hresult as [Hconfig|[]]. subst config. cbn.
  eapply sreach_rule with (rule := rule) (child_configs := children).
  - exact Hrule.
  - apply sreach_children_forall. apply List.Forall_forall.
    intros child Hchild. apply Hknown.
    now apply (proj1 (List.Forall_forall _ _ ) Hchildren).
  - rewrite Hstates. apply Permutation_refl.
  - exact Happly.
Qed.

Lemma saturation_one_step_sound : forall d q (system : SBVAS d q) known config,
  (forall child, List.In child known ->
     SReach system (fst child) (snd child)) ->
  List.In config (saturation_one_step system known) ->
  SReach system (fst config) (snd config).
Proof.
  intros d q system known config Hknown Hin.
  unfold saturation_one_step in Hin. apply in_flat_map in Hin.
  destruct Hin as [rule [Hrule Hresult]].
  eapply rule_results_sound; eauto.
Qed.

Theorem saturation_configs_sound : forall d q (system : SBVAS d q) fuel config,
  List.In config (saturation_configs system fuel) ->
  SReach system (fst config) (snd config).
Proof.
  intros d q system fuel. induction fuel as [|fuel IH]; intros config Hin; cbn in Hin.
  - apply nodup_In in Hin. destruct config. cbn. now apply sreach_initial.
  - apply in_saturation_step_iff in Hin. destruct Hin as [Hin|Hin].
    + now apply IH.
    + eapply saturation_one_step_sound; [|exact Hin].
      intros child Hchild. now apply IH.
Qed.

Lemma reorder_configs_by_states : forall q d (configs : list (SConfig d q)) states,
  Permutation (List.map fst configs) states ->
  exists ordered,
    Permutation ordered configs /\ List.map fst ordered = states.
Proof.
  intros q d configs states Hperm.
  induction states as [|state states IH] in configs, Hperm |- *.
  - apply Permutation_length in Hperm. destruct configs; [|discriminate].
    exists []; split; reflexivity.
  - assert (Hin : List.In state (List.map fst configs)).
    { eapply Permutation_in.
      - apply Permutation_sym. exact Hperm.
      - now left. }
    apply in_map_iff in Hin. destruct Hin as [config [Hfst Hin]].
    apply in_split in Hin. destruct Hin as [left [right Hconfigs]].
    subst configs.
    assert (Hrest : Permutation (List.map fst (left ++ right)) states).
    { apply Permutation_cons_inv with (a := state).
      eapply Permutation_trans.
      - rewrite !List.map_app. cbn.
        apply Permutation_middle.
      - rewrite List.map_app in Hperm. cbn in Hperm.
        rewrite Hfst in Hperm. exact Hperm. }
    destruct (IH (left ++ right) Hrest) as [ordered [Hordered Hmap]].
    exists (config :: ordered). split.
    + eapply Permutation_trans.
      * constructor. exact Hordered.
      * apply Permutation_middle.
    + cbn. now rewrite Hfst, Hmap.
Qed.

Lemma rule_results_complete : forall d q (system : SBVAS d q) known
    rule children result,
  List.In rule (stateful_rules system) ->
  List.Forall (fun child => List.In child known) children ->
  Permutation (List.map fst children) (input_states rule) ->
  add_displacement (rule_delta rule) (List.map snd children) = Some result ->
  List.In (output_state rule, result) (rule_results rule known).
Proof.
  intros d q system known rule children result Hrule Hknown Hstates Happly.
  destruct (reorder_configs_by_states q d children (input_states rule) Hstates)
    as [ordered [Hordered Hordered_states]].
  unfold rule_results. apply in_flat_map.
  exists ordered. split.
  - apply config_choices_for_states_spec. split; [exact Hordered_states|].
    apply List.Forall_forall. intros child Hchild.
    apply (proj1 (List.Forall_forall _ _) Hknown).
    eapply Permutation_in; eauto.
  - assert (Hordered_apply :
        add_displacement (rule_delta rule) (List.map snd ordered) =
        Some result).
    { rewrite <- Happly. apply add_displacement_permutation.
      apply Permutation_map. exact Hordered. }
    rewrite Hordered_apply. now left.
Qed.

Lemma saturation_one_step_complete : forall d q (system : SBVAS d q) known
    rule children result,
  List.In rule (stateful_rules system) ->
  List.Forall (fun child => List.In child known) children ->
  Permutation (List.map fst children) (input_states rule) ->
  add_displacement (rule_delta rule) (List.map snd children) = Some result ->
  List.In (output_state rule, result) (saturation_one_step system known).
Proof.
  intros. unfold saturation_one_step. apply in_flat_map.
  exists rule. split; [assumption|]. eapply rule_results_complete; eauto.
Qed.

Lemma saturation_fixed_point_complete : forall d q (system : SBVAS d q) fuel,
  saturation_configs system (S fuel) = saturation_configs system fuel ->
  forall state counters,
    SReach system state counters ->
    List.In (state, counters) (saturation_configs system fuel).
Proof.
  intros d q system fuel Hfixed.
  assert (Hmut :
    (forall state counters, SReach system state counters ->
       List.In (state, counters) (saturation_configs system fuel)) /\
    (forall configs, SReachChildren system configs ->
       List.Forall (fun child =>
         List.In child (saturation_configs system fuel)) configs)).
  { apply SReach_mutind.
    - intros state counters Hinitial.
      now apply saturation_configs_initial.
    - intros rule children result Hrule Hchildren IHchildren Hstates Happly.
      rewrite <- Hfixed. apply in_saturation_step_iff. right.
      eapply saturation_one_step_complete; eauto.
    - constructor.
    - intros state counters children Hreach IHreach Hchildren IHchildren.
      constructor; assumption. }
  exact (proj1 Hmut).
Qed.

Definition saturation_decide {d q} (system : SBVAS d q)
    (state : Fin.t q) (counters : NVec d) (fuel : nat) : option bool :=
  let current := saturation_configs system fuel in
  if in_dec sconfig_eq_dec (state, counters) current then Some true
  else
    match fuel with
    | 0 => None
    | S previous_fuel =>
        if list_eq_dec sconfig_eq_dec current
             (saturation_configs system previous_fuel)
        then Some false
        else None
    end.

Theorem saturation_decide_sound : forall d q (system : SBVAS d q)
    state counters fuel answer,
  saturation_decide system state counters fuel = Some answer ->
  if answer then SReach system state counters
  else ~ SReach system state counters.
Proof.
  intros d q system state counters fuel answer Hdecide.
  unfold saturation_decide in Hdecide.
  destruct (in_dec sconfig_eq_dec (state, counters)
      (saturation_configs system fuel)) as [Hin|Hout].
  - inversion Hdecide; subst.
    pose proof (saturation_configs_sound d q system fuel
      (state, counters) Hin) as Hreach. exact Hreach.
  - destruct fuel as [|previous_fuel]; [discriminate|].
    destruct (list_eq_dec sconfig_eq_dec
        (saturation_configs system (S previous_fuel))
        (saturation_configs system previous_fuel)) as [Hfixed|Hnotfixed];
      [|discriminate].
    inversion Hdecide; subst. cbn. intro Hreach.
    apply Hout. rewrite Hfixed.
    eapply saturation_fixed_point_complete; eauto.
Qed.

(** A bounded backwards slice is used only as a YES precheck.  Since the
    sliced system is literally a sub-system, every discovered derivation is a
    derivation of the original system.  A negative answer from the slice is
    intentionally discarded. *)
Definition state_mem {q} (state : Fin.t q) (states : list (Fin.t q)) : bool :=
  if in_dec Fin.eq_dec state states then true else false.

Definition needed_state_step {d q} (system : SBVAS d q)
    (states : list (Fin.t q)) : list (Fin.t q) :=
  List.nodup Fin.eq_dec
    (states ++
     List.flat_map
       (fun rule =>
          if state_mem (output_state rule) states
          then input_states rule
          else [])
       (stateful_rules system)).

Fixpoint needed_states {d q} (system : SBVAS d q) (root : Fin.t q)
    (fuel : nat) : list (Fin.t q) :=
  match fuel with
  | 0 => [root]
  | S fuel' => needed_state_step system (needed_states system root fuel')
  end.

Definition slice_system {d q} (system : SBVAS d q)
    (states : list (Fin.t q)) : SBVAS d q :=
  {| initial_configs :=
       List.filter (fun config => state_mem (fst config) states)
         (initial_configs system);
     stateful_rules :=
       List.filter (fun rule => state_mem (output_state rule) states)
         (stateful_rules system) |}.

Lemma slice_initial_in : forall d q (system : SBVAS d q) states config,
  List.In config (initial_configs (slice_system system states)) ->
  List.In config (initial_configs system).
Proof.
  intros. cbn in H. now apply filter_In in H.
Qed.

Lemma slice_rule_in : forall d q (system : SBVAS d q) states rule,
  List.In rule (stateful_rules (slice_system system states)) ->
  List.In rule (stateful_rules system).
Proof.
  intros. cbn in H. now apply filter_In in H.
Qed.

Theorem slice_sreach_sound : forall d q (system : SBVAS d q) states,
  (forall state counters,
     SReach (slice_system system states) state counters ->
     SReach system state counters) /\
  (forall configs,
     SReachChildren (slice_system system states) configs ->
     SReachChildren system configs).
Proof.
  intros d q system states. apply SReach_mutind.
  - intros state counters Hinitial. apply sreach_initial.
    eapply slice_initial_in; eauto.
  - intros rule children result Hrule Hchildren IHchildren Hstates Happly.
    eapply sreach_rule with (rule := rule) (child_configs := children); eauto.
    eapply slice_rule_in; eauto.
  - constructor.
  - intros state counters children Hreach IHreach Hchildren IHchildren.
    constructor; assumption.
Qed.

Definition goal_saturation_decide {d q} (system : SBVAS d q)
    (root : Fin.t q) (counters : NVec d) (slice_fuel saturation_fuel : nat)
    : option bool :=
  match saturation_decide
    (slice_system system (needed_states system root slice_fuel))
    root counters saturation_fuel with
  | Some true => Some true
  | _ => None
  end.

Theorem goal_saturation_decide_sound : forall d q (system : SBVAS d q)
    root counters slice_fuel saturation_fuel,
  goal_saturation_decide system root counters slice_fuel saturation_fuel =
    Some true ->
  SReach system root counters.
Proof.
  intros d q system root counters slice_fuel saturation_fuel Hdecide.
  unfold goal_saturation_decide in Hdecide.
  destruct (saturation_decide
    (slice_system system (needed_states system root slice_fuel))
    root counters saturation_fuel) as [answer|] eqn:Hslice;
    [|discriminate].
  destruct answer; [|discriminate].
  pose proof (saturation_decide_sound _ _
    (slice_system system (needed_states system root slice_fuel))
    root counters saturation_fuel true Hslice) as Hreach.
  exact (proj1 (slice_sreach_sound d q system
    (needed_states system root slice_fuel)) root counters Hreach).
Qed.
