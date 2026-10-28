From Coq Require Import List Vector ZArith Lia Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.BVASS Require Import Stateful.

Import ListNotations.

(** A positional omission certificate.  The first output list contains exactly
    the retained input-state occurrences, in order; the second contains the
    configurations used to discharge omitted occurrences, also in order. *)
Inductive OmissionSelection {d q} (available : list (SConfig d q)) :
    list (Fin.t q) -> list (Fin.t q) -> list (SConfig d q) -> Prop :=
| omission_selection_nil : OmissionSelection available [] [] []
| omission_selection_keep : forall state inputs retained omitted,
    OmissionSelection available inputs retained omitted ->
    OmissionSelection available (state :: inputs) (state :: retained) omitted
| omission_selection_omit : forall state counters inputs retained omitted,
    List.In (state, counters) available ->
    OmissionSelection available inputs retained omitted ->
    OmissionSelection available (state :: inputs) retained
      ((state, counters) :: omitted).

Definition configurations_at_state {d q} (state : Fin.t q)
    (available : list (SConfig d q)) : list (SConfig d q) :=
  List.filter
    (fun config => if Fin.eq_dec (fst config) state then true else false)
    available.

Fixpoint enumerate_omissions {d q} (available : list (SConfig d q))
    (inputs : list (Fin.t q)) :
    list (list (Fin.t q) * list (SConfig d q)) :=
  match inputs with
  | [] => [([], [])]
  | state :: tail =>
      let tails := enumerate_omissions available tail in
      List.map (fun result => (state :: fst result, snd result)) tails ++
      List.flat_map
        (fun config =>
          List.map (fun result => (fst result, config :: snd result)) tails)
        (configurations_at_state state available)
  end.

Lemma configurations_at_state_spec : forall d q state
    (available : list (SConfig d q)) config,
    List.In config (configurations_at_state state available) <->
    List.In config available /\ fst config = state.
Proof.
  intros d q state available config. unfold configurations_at_state.
  rewrite filter_In. split.
  - intros [Hin Htest]. split; [exact Hin|].
    destruct (Fin.eq_dec (fst config) state) as [Heq|Hneq];
      [exact Heq|discriminate].
  - intros [Hin Hstate]. split; [exact Hin|].
    destruct (Fin.eq_dec (fst config) state) as [Heq|Hneq];
      [reflexivity|contradiction].
Qed.

Lemma enumerate_omissions_sound : forall d q
    (available : list (SConfig d q)) inputs retained omitted,
    List.In (retained, omitted) (enumerate_omissions available inputs) ->
    OmissionSelection available inputs retained omitted.
Proof.
  intros d q available inputs. induction inputs as [|state tail IH];
    intros retained omitted; cbn.
  - intros [H|H]; [inversion H; constructor|contradiction].
  - rewrite in_app_iff. intros [Hkeep|Homit].
    + apply in_map_iff in Hkeep.
      destruct Hkeep as [[retained' omitted'] [Heq Hin]]. cbn in Heq.
      inversion Heq; subst. constructor. now apply IH.
    + apply in_flat_map in Homit.
      destruct Homit as [config [Hconfig Hmap]].
      apply in_map_iff in Hmap.
      destruct Hmap as [[retained' omitted'] [Heq Hin]]. cbn in Heq.
      inversion Heq; subst.
      destruct config as [config_state counters].
      apply configurations_at_state_spec in Hconfig.
      destruct Hconfig as [Havailable Hstate]. cbn in Hstate. subst config_state.
      constructor; [exact Havailable|now apply IH].
Qed.

Lemma enumerate_omissions_complete : forall d q
    (available : list (SConfig d q)) inputs retained omitted,
    OmissionSelection available inputs retained omitted ->
    List.In (retained, omitted) (enumerate_omissions available inputs).
Proof.
  intros d q available inputs retained omitted Hselection.
  induction Hselection; cbn.
  - auto.
  - apply in_app_iff. left. apply in_map_iff.
    exists (retained, omitted). auto.
  - apply in_app_iff. right. apply in_flat_map.
    exists (state, counters). split.
    + apply configurations_at_state_spec. auto.
    + apply in_map_iff. exists (retained, omitted). auto.
Qed.

Lemma enumerate_omissions_spec : forall d q
    (available : list (SConfig d q)) inputs retained omitted,
    List.In (retained, omitted) (enumerate_omissions available inputs) <->
    OmissionSelection available inputs retained omitted.
Proof.
  intros. split; [apply enumerate_omissions_sound|apply enumerate_omissions_complete].
Qed.

Definition shifted_rule_delta {d q} (rule : SRule d q)
    (omitted : list (SConfig d q)) : ZVec d :=
  zvec_add (rule_delta rule)
    (nvec_to_zvec (nvec_sum (List.map snd omitted))).

Definition make_extended_rule {d q} (rule : SRule d q)
    (retained : list (Fin.t q)) (omitted : list (SConfig d q))
    : option (SRule d q) :=
  match retained with
  | [] => None
  | state :: tail =>
      Some {| input_states := state :: tail;
              input_nonempty := fun Hnil =>
                List.nil_cons (eq_sym Hnil);
              output_state := output_state rule;
              rule_delta := shifted_rule_delta rule omitted |}
  end.

Definition make_extended_initial {d q} (rule : SRule d q)
    (retained : list (Fin.t q)) (omitted : list (SConfig d q))
    : option (SConfig d q) :=
  match retained with
  | _ :: _ => None
  | [] =>
      match zvec_to_nvec (shifted_rule_delta rule omitted) with
      | Some counters => Some (output_state rule, counters)
      | None => None
      end
  end.

Definition option_to_list {A : Type} (value : option A) : list A :=
  match value with Some x => [x] | None => [] end.

Lemma in_option_to_list : forall A (value : option A) x,
    List.In x (option_to_list value) <-> value = Some x.
Proof.
  intros A [value|] x; cbn.
  - split.
    + intros [Heq|Hfalse]; [now subst value|contradiction].
    + intro Heq. inversion Heq. auto.
  - split; intro H; [contradiction|discriminate].
Qed.

Definition extended_rules_for {d q} (available : list (SConfig d q))
    (rule : SRule d q) : list (SRule d q) :=
  List.flat_map
    (fun result => option_to_list
      (make_extended_rule rule (fst result) (snd result)))
    (enumerate_omissions available (input_states rule)).

Definition extended_initials_for {d q} (available : list (SConfig d q))
    (rule : SRule d q) : list (SConfig d q) :=
  List.flat_map
    (fun result => option_to_list
      (make_extended_initial rule (fst result) (snd result)))
    (enumerate_omissions available (input_states rule)).

Definition extend_bvass {d q} (B : SBVAS d q)
    (available : list (SConfig d q)) : SBVAS d q :=
  {| initial_configs := initial_configs B ++
       List.flat_map (extended_initials_for available) (stateful_rules B);
     stateful_rules := stateful_rules B ++
       List.flat_map (extended_rules_for available) (stateful_rules B) |}.

Definition ReachableConfigurations {d q} (B : SBVAS d q)
    (available : list (SConfig d q)) : Prop :=
  forall config, List.In config available ->
    SReach B (fst config) (snd config).

Lemma omission_selection_permutation : forall d q available inputs retained omitted,
    @OmissionSelection d q available inputs retained omitted ->
    Permutation (retained ++ List.map fst omitted) inputs.
Proof.
  intros d q available inputs retained omitted Hselection.
  induction Hselection; cbn.
  - constructor.
  - now constructor.
  - eapply Permutation_trans.
    + apply Permutation_sym. apply Permutation_middle.
    + constructor. exact IHHselection.
Qed.

Lemma omission_selection_length : forall d q available inputs retained omitted,
    @OmissionSelection d q available inputs retained omitted ->
    length retained + length omitted = length inputs.
Proof. intros d q available inputs retained omitted H; induction H; cbn; lia. Qed.

Lemma omission_selection_all_keep : forall d q available inputs,
    @OmissionSelection d q available inputs inputs [].
Proof. intros d q available inputs; induction inputs; constructor; assumption. Qed.

Definition ExtendedRuleWitness {d q} (available : list (SConfig d q))
    (original generated : SRule d q) : Prop :=
  exists retained omitted,
    OmissionSelection available (input_states original) retained omitted /\
    make_extended_rule original retained omitted = Some generated.

Definition ExtendedInitialWitness {d q} (available : list (SConfig d q))
    (original : SRule d q) (generated : SConfig d q) : Prop :=
  exists retained omitted,
    OmissionSelection available (input_states original) retained omitted /\
    make_extended_initial original retained omitted = Some generated.

Lemma extended_rules_for_spec : forall d q available
    (original generated : SRule d q),
    List.In generated (extended_rules_for available original) <->
    ExtendedRuleWitness available original generated.
Proof.
  intros d q available original generated. unfold extended_rules_for,
    ExtendedRuleWitness. rewrite in_flat_map. split.
  - intros [[retained omitted] [Henum Hoption]].
    exists retained, omitted. split.
    + now apply enumerate_omissions_spec.
    + now apply in_option_to_list in Hoption.
  - intros [retained [omitted [Hselection Hmake]]].
    exists (retained, omitted). split.
    + now apply enumerate_omissions_spec.
    + now apply in_option_to_list.
Qed.

Lemma extended_initials_for_spec : forall d q available
    (original : SRule d q) generated,
    List.In generated (extended_initials_for available original) <->
    ExtendedInitialWitness available original generated.
Proof.
  intros d q available original generated. unfold extended_initials_for,
    ExtendedInitialWitness. rewrite in_flat_map. split.
  - intros [[retained omitted] [Henum Hoption]].
    exists retained, omitted. split.
    + now apply enumerate_omissions_spec.
    + now apply in_option_to_list in Hoption.
  - intros [retained [omitted [Hselection Hmake]]].
    exists (retained, omitted). split.
    + now apply enumerate_omissions_spec.
    + now apply in_option_to_list.
Qed.

Lemma extend_rule_membership_spec : forall d q (B : SBVAS d q) available generated,
    List.In generated (stateful_rules (extend_bvass B available)) <->
    List.In generated (stateful_rules B) \/
    exists original,
      List.In original (stateful_rules B) /\
      ExtendedRuleWitness available original generated.
Proof.
  intros. unfold extend_bvass; cbn. rewrite in_app_iff, in_flat_map. split.
  - intros [Hin|[original [Hin Hgenerated]]]; [now left|right].
    exists original. split; [exact Hin|]. now apply extended_rules_for_spec.
  - intros [Hin|[original [Hin Hgenerated]]]; [now left|right].
    exists original. split; [exact Hin|]. now apply extended_rules_for_spec.
Qed.

Lemma extend_initial_membership_spec : forall d q (B : SBVAS d q)
    available generated,
    List.In generated (initial_configs (extend_bvass B available)) <->
    List.In generated (initial_configs B) \/
    exists original,
      List.In original (stateful_rules B) /\
      ExtendedInitialWitness available original generated.
Proof.
  intros. unfold extend_bvass; cbn. rewrite in_app_iff, in_flat_map. split.
  - intros [Hin|[original [Hin Hgenerated]]]; [now left|right].
    exists original. split; [exact Hin|]. now apply extended_initials_for_spec.
  - intros [Hin|[original [Hin Hgenerated]]]; [now left|right].
    exists original. split; [exact Hin|]. now apply extended_initials_for_spec.
Qed.

Lemma original_rule_in_extension : forall d q (B : SBVAS d q) available rule,
    List.In rule (stateful_rules B) ->
    List.In rule (stateful_rules (extend_bvass B available)).
Proof.
  intros. apply extend_rule_membership_spec. now left.
Qed.

Lemma original_initial_in_extension : forall d q (B : SBVAS d q) available config,
    List.In config (initial_configs B) ->
    List.In config (initial_configs (extend_bvass B available)).
Proof. intros. apply extend_initial_membership_spec. auto. Qed.

Lemma nvec_sum_app_extend : forall d (left right : list (NVec d)),
    nvec_sum (left ++ right) = nvec_add (nvec_sum left) (nvec_sum right).
Proof.
  intros d left right. repeat rewrite nvec_sum_rsum_stateful.
  induction left as [|head tail IH]; cbn.
  - symmetry. apply nvec_add_zero_left_stateful.
  - rewrite IH. symmetry. apply nvec_add_assoc_stateful.
Qed.

Lemma add_displacement_shifted_rule : forall d q (rule : SRule d q)
    retained omitted result,
    add_displacement (shifted_rule_delta rule omitted) retained = Some result <->
    add_displacement (rule_delta rule)
      (retained ++ List.map snd omitted) = Some result.
Proof.
  intros d q rule retained omitted result. unfold add_displacement,
    shifted_rule_delta. rewrite nvec_sum_app_extend.
  assert (Heq :
      zvec_add
        (zvec_add (rule_delta rule)
          (nvec_to_zvec (nvec_sum (List.map snd omitted))))
        (nvec_to_zvec (nvec_sum retained)) =
      zvec_add (rule_delta rule)
        (nvec_to_zvec
          (nvec_add (nvec_sum retained) (nvec_sum (List.map snd omitted))))).
  { rewrite nvec_to_zvec_add.
    apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros index index' Hindex; subst index'. unfold zvec_add.
    repeat rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl). lia. }
  now rewrite Heq.
Qed.

Lemma original_valid_run_in_extension_mut : forall d q (B : SBVAS d q) available,
  (forall run, ValidSRun B run -> ValidSRun (extend_bvass B available) run) /\
  (forall runs, ValidSRuns B runs -> ValidSRuns (extend_bvass B available) runs).
Proof.
  intros d q B available. apply ValidSRun_mutind.
  - intros config Hinitial. constructor. now apply original_initial_in_extension.
  - intros rule children result Hrule Hchildren IHchildren Hstates Happly Houtput.
    econstructor; eauto using original_rule_in_extension.
  - constructor.
  - intros run runs Hrun IHrun Hruns IHruns. constructor; assumption.
Qed.

Lemma original_valid_run_in_extension : forall d q (B : SBVAS d q) available run,
    ValidSRun B run -> ValidSRun (extend_bvass B available) run.
Proof.
  intros. eapply (proj1 (original_valid_run_in_extension_mut d q B available)); eauto.
Qed.

Theorem extend_original_reach : forall d q (B : SBVAS d q) available state counters,
    SReach B state counters -> SReach (extend_bvass B available) state counters.
Proof.
  intros d q B available state counters Hreach.
  apply stateful_run_reach_iff in Hreach.
  destruct Hreach as [run [Hvalid Hroot]]. apply stateful_run_reach_iff.
  exists run. split; [now apply original_valid_run_in_extension|exact Hroot].
Qed.

Lemma make_extended_rule_spec : forall d q (original generated : SRule d q)
    retained omitted,
    make_extended_rule original retained omitted = Some generated ->
    retained <> [] /\
    input_states generated = retained /\
    output_state generated = output_state original /\
    rule_delta generated = shifted_rule_delta original omitted.
Proof.
  intros d q original generated retained omitted Hmake.
  destruct retained as [|state tail]; cbn in Hmake; [discriminate|].
  inversion Hmake; subst. repeat split; cbn; try reflexivity; discriminate.
Qed.

Lemma make_extended_initial_spec : forall d q (original : SRule d q)
    retained omitted state counters,
    make_extended_initial original retained omitted = Some (state, counters) ->
    retained = [] /\ state = output_state original /\
    zvec_to_nvec (shifted_rule_delta original omitted) = Some counters.
Proof.
  intros d q original retained omitted state counters Hmake.
  destruct retained as [|head tail]; cbn in Hmake; [|discriminate].
  destruct (zvec_to_nvec (shifted_rule_delta original omitted)) as [value|]
    eqn:Hvalue; inversion Hmake; subst. auto.
Qed.

Lemma sreach_children_app : forall d q (B : SBVAS d q) left right,
    SReachChildren B left -> SReachChildren B right ->
    SReachChildren B (left ++ right).
Proof.
  intros d q B left right Hleft Hright. induction Hleft; cbn.
  - exact Hright.
  - constructor; auto.
Qed.

Lemma reachable_configurations_children : forall d q (B : SBVAS d q)
    available omitted,
    ReachableConfigurations B available ->
    List.Forall (fun config => List.In config available) omitted ->
    SReachChildren B omitted.
Proof.
  intros d q B available omitted Hreachable Hall.
  apply sreach_children_forall. eapply List.Forall_impl; [|exact Hall].
  intros config Hin. now apply Hreachable.
Qed.

Lemma omission_selection_omitted_available : forall d q available inputs retained omitted,
    @OmissionSelection d q available inputs retained omitted ->
    List.Forall (fun config => List.In config available) omitted.
Proof.
  intros d q available inputs retained omitted Hselection.
  induction Hselection; cbn; auto using List.Forall.
Qed.

Lemma omission_selection_states_with_children : forall d q available
    inputs retained omitted (children : list (SConfig d q)),
    @OmissionSelection d q available inputs retained omitted ->
    Permutation (List.map fst children) retained ->
    Permutation (List.map fst (children ++ omitted)) inputs.
Proof.
  intros d q available inputs retained omitted children Hselection Hchildren.
  rewrite map_app. eapply Permutation_trans.
  - apply Permutation_app_tail. exact Hchildren.
  - now apply omission_selection_permutation in Hselection.
Qed.

Lemma extend_reach_original_mut : forall d q (B : SBVAS d q) available,
    ReachableConfigurations B available ->
  (forall state counters, SReach (extend_bvass B available) state counters ->
    SReach B state counters) /\
  (forall configs, SReachChildren (extend_bvass B available) configs ->
    SReachChildren B configs).
Proof.
  intros d q B available Hreachable. apply SReach_mutind.
  - intros state counters Hinitial.
    apply extend_initial_membership_spec in Hinitial.
    destruct Hinitial as [Horiginal|
      [original [Hrule [retained [omitted [Hselection Hmake]]]]]].
    + now constructor.
    + apply make_extended_initial_spec in Hmake.
      destruct Hmake as [Hretained [Hstate Hdecode]]. subst retained state.
      eapply sreach_rule with (rule := original) (child_configs := omitted).
      * exact Hrule.
      * apply reachable_configurations_children with (available := available);
          [exact Hreachable|].
        now apply omission_selection_omitted_available in Hselection.
      * pose proof (omission_selection_permutation _ _ _ _ _ _ Hselection)
          as Hperm. cbn in Hperm. exact Hperm.
      * unfold add_displacement, shifted_rule_delta in *.
        exact Hdecode.
  - intros generated child_configs result Hgenerated Hchildren IHchildren
      Hstates Happly.
    apply extend_rule_membership_spec in Hgenerated.
    destruct Hgenerated as [Horiginal|Hgenerated].
    + eapply sreach_rule with (rule := generated) (child_configs := child_configs);
        eauto.
    + destruct Hgenerated as [original [Hrule Hgenerated]].
      destruct Hgenerated as [retained [omitted [Hselection Hmake]]].
    apply make_extended_rule_spec in Hmake.
    destruct Hmake as [Hnonempty [Hinputs [Houtput Hdelta]]].
    rewrite Houtput.
    eapply sreach_rule with (rule := original)
      (child_configs := child_configs ++ omitted).
    * exact Hrule.
    * apply sreach_children_app; [exact IHchildren|].
      apply reachable_configurations_children with (available := available);
        [exact Hreachable|].
      now apply omission_selection_omitted_available in Hselection.
    * apply omission_selection_states_with_children with (retained := retained)
        (available := available).
      -- exact Hselection.
      -- rewrite <- Hinputs. exact Hstates.
    * rewrite map_app.
      apply (proj1 (add_displacement_shifted_rule d q original
        (List.map snd child_configs) omitted result)).
      rewrite <- Hdelta. exact Happly.
  - constructor.
  - intros state counters configs Hhead IHhead Htail IHtail.
    constructor; assumption.
Qed.

Theorem extend_reach_original : forall d q (B : SBVAS d q) available,
    ReachableConfigurations B available ->
    forall state counters,
      SReach (extend_bvass B available) state counters ->
      SReach B state counters.
Proof.
  intros. eapply (proj1 (extend_reach_original_mut d q B available H)); eauto.
Qed.

Theorem extend_bvass_reach_iff : forall d q
    (B : SBVAS d q) (available : list (SConfig d q)),
    ReachableConfigurations B available ->
    forall state counters,
      SReach (extend_bvass B available) state counters <->
      SReach B state counters.
Proof.
  intros d q B available Hreachable state counters. split.
  - now apply extend_reach_original.
  - now apply extend_original_reach.
Qed.

Definition RetainedChildrenOccurrence {d q} (retained : list (Fin.t q))
    (children : SRuns d q) (run : SRun d q) : Prop :=
  match retained with
  | [] => exists config, run = srun_leaf config
  | _ :: _ => exists rule config, run = srun_node rule children config
  end.

Lemma make_extended_initial_from_original_apply : forall d q
    (rule : SRule d q) omitted result,
    add_displacement (rule_delta rule) (List.map snd omitted) = Some result ->
    make_extended_initial rule [] omitted =
      Some (output_state rule, result).
Proof.
  intros d q rule omitted result Happly.
  unfold make_extended_initial, shifted_rule_delta, add_displacement in *; cbn.
  now rewrite Happly.
Qed.

Theorem extend_local_root_shortening : forall d q (B : SBVAS d q)
    available (original : SRule d q) retained omitted
    (children : SRuns d q) result,
    List.In original (stateful_rules B) ->
    OmissionSelection available (input_states original) retained omitted ->
    ValidSRuns (extend_bvass B available) children ->
    Permutation (List.map fst (sruns_configs children)) retained ->
    add_displacement (rule_delta original)
      (List.map snd (sruns_configs children) ++ List.map snd omitted) =
      Some result ->
    exists shortened : SRun d q,
      ValidSRun (extend_bvass B available) shortened /\
      root_config shortened = (output_state original, result) /\
      RetainedChildrenOccurrence retained children shortened /\
      length retained + length omitted = length (input_states original) /\
      (ReachableConfigurations B available -> SReachChildren B omitted).
Proof.
  intros d q B available original retained omitted children result
    Horiginal Hselection Hchildren Hstates Happly.
  assert (Hlength : length retained + length omitted =
      length (input_states original)).
  { now apply omission_selection_length in Hselection. }
  assert (Homitted : ReachableConfigurations B available ->
      SReachChildren B omitted).
  { intro Hreachable. apply reachable_configurations_children with
      (available := available); [exact Hreachable|].
    now apply omission_selection_omitted_available in Hselection. }
  destruct retained as [|state tail].
  - assert (Hconfigs : sruns_configs children = []).
    { pose proof (Permutation_length Hstates) as Hlen.
      destruct (sruns_configs children) as [|config configs] eqn:Hconfigs;
        [reflexivity|cbn in Hlen; lia]. }
    assert (Hinitial : make_extended_initial original [] omitted =
        Some (output_state original, result)).
    { apply make_extended_initial_from_original_apply.
      rewrite Hconfigs in Happly. cbn in Happly. exact Happly. }
    exists (srun_leaf (output_state original, result)). split.
    + constructor. apply extend_initial_membership_spec. right.
      exists original. split; [exact Horiginal|].
      exists [], omitted. auto.
    + split; [reflexivity|]. split.
      * cbn. eauto.
      * split; [exact Hlength|exact Homitted].
  - destruct (make_extended_rule original (state :: tail) omitted)
      as [generated|] eqn:Hgenerated.
    2: { cbn in Hgenerated. discriminate. }
    pose proof (make_extended_rule_spec d q original generated
      (state :: tail) omitted Hgenerated)
      as [_ [Hinputs [Houtput Hdelta]]].
    exists (srun_node generated children (output_state original, result)).
    split.
    + econstructor.
      * apply extend_rule_membership_spec. right. exists original. split;
          [exact Horiginal|].
        exists (state :: tail), omitted. auto.
      * exact Hchildren.
      * rewrite Hinputs. exact Hstates.
      * rewrite Hdelta. apply (proj2 (add_displacement_shifted_rule d q
          original (List.map snd (sruns_configs children)) omitted result)).
        exact Happly.
      * cbn. symmetry. exact Houtput.
    + split; [reflexivity|]. split.
      * cbn. eauto.
      * split; [exact Hlength|exact Homitted].
Qed.

Definition basis_root_configs {d q} (basis : list (SRun d q)) :
    list (SConfig d q) := List.map root_config basis.

Theorem basis_root_configs_reachable : forall d q (B : SBVAS d q) basis,
    (forall run, List.In run basis -> ValidSRun B run) ->
    ReachableConfigurations B (basis_root_configs basis).
Proof.
  intros d q B basis Hvalid config Hconfig. unfold basis_root_configs in Hconfig.
  apply in_map_iff in Hconfig. destruct Hconfig as [run [Hroot Hin]].
  subst config. eapply (proj1 (valid_srun_reach_mut d q B)); eauto.
Qed.
