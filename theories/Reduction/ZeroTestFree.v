From Coq Require Import List Vector ZArith Lia Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVASS Require Import Stateful BoundedVASSSection.
From Mell.VAS Require Import Runs.
From Mell.Reduction Require Import FullZeroSystem MELLToABVASS ZeroTest.

Import ListNotations.

Definition zero_test_freeb {d State}
    (system : FullZeroBVASS d State) : bool :=
  match full_zero_test_rules system with
  | [] => true
  | _ :: _ => false
  end.

Lemma zero_test_freeb_spec : forall d State
    (system : FullZeroBVASS d State),
  zero_test_freeb system = true <-> full_zero_test_rules system = [].
Proof.
  intros d State [leaves unary split tests]. destruct tests; cbn; split;
    intro H; try reflexivity; discriminate.
Qed.

Definition direct_state {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) (state : State) :
    Fin.t (full_zero_state_count system) :=
  state_index eq_dec (full_zero_states system) state.

Definition direct_initials {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) :=
  List.map (fun state =>
    (direct_state eq_dec system state, nvec_zero d))
    (full_zero_leaves system).

Definition direct_unary_rule {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) (rule : UnaryZeroRule d State) :
    SRule d (full_zero_state_count system) :=
  {| input_states :=
       [direct_state eq_dec system (unary_zero_target d State rule)];
     input_nonempty := fun H => match H with end;
     output_state :=
       direct_state eq_dec system (unary_zero_source d State rule);
     rule_delta := zvec_opp (unary_zero_delta d State rule) |}.

Definition direct_split_rule {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) (rule : SplitZeroRule State) :
    SRule d (full_zero_state_count system) :=
  {| input_states :=
       [direct_state eq_dec system (split_zero_left State rule);
        direct_state eq_dec system (split_zero_right State rule)];
     input_nonempty := fun H => match H with end;
     output_state := direct_state eq_dec system (split_zero_source State rule);
     rule_delta := zvec_zero d |}.

Definition direct_bottom_up {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) :
    SBVAS d (full_zero_state_count system) :=
  {| initial_configs := direct_initials eq_dec system;
     stateful_rules :=
       List.map (direct_unary_rule eq_dec system)
         (full_zero_unary_rules system) ++
       List.map (direct_split_rule eq_dec system)
         (full_zero_split_rules system) |}.

Definition direct_root_state {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) (state : State) :=
  direct_state eq_dec system state.

Lemma direct_state_injective : forall d State eq_dec
    (system : FullZeroBVASS d State) left right,
  List.In left (full_zero_states system) ->
  List.In right (full_zero_states system) ->
  direct_state eq_dec system left = direct_state eq_dec system right ->
  left = right.
Proof.
  intros d State eq_dec system left right Hleft Hright Heq.
  apply state_index_injective_on_list with
    (eq_dec := eq_dec) (values := full_zero_states system);
    try assumption.
  rewrite <- !state_index_value.
  exact (f_equal (fun index => proj1_sig (Fin.to_nat index)) Heq).
Qed.

Lemma direct_unary_apply : forall d (delta : ZVec d) source target,
  add_displacement delta [source] = Some target ->
  add_displacement (zvec_opp delta) [target] = Some source.
Proof.
  intros d delta source target Happly.
  apply displacement_singleton_step_action in Happly.
  apply unary_add_displacement_of_action.
  now rewrite Happly, zvec_opp_step_action.
Qed.

Lemma direct_unary_apply_reverse : forall d (delta : ZVec d) source target,
  add_displacement (zvec_opp delta) [target] = Some source ->
  add_displacement delta [source] = Some target.
Proof.
  intros d delta source target Happly.
  apply displacement_singleton_step_action in Happly.
  assert (Hdelta : delta = StepAction source target).
  { pose proof (f_equal (@zvec_opp d) Happly) as Hopp.
    now rewrite zvec_opp_involutive, zvec_opp_step_action in Hopp. }
  apply add_displacement_of_exact_reduction.
  rewrite nvec_sum_singleton_reduction, Hdelta.
  unfold StepAction, zvec_sub_run, zvec_add, nvec_to_zvec.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
  repeat rewrite (nth_map _ _ index index eq_refl). lia.
Qed.

Lemma direct_initial_in : forall d State eq_dec
    (system : FullZeroBVASS d State) state,
  List.In state (full_zero_leaves system) ->
  List.In (direct_state eq_dec system state, nvec_zero d)
    (initial_configs (direct_bottom_up eq_dec system)).
Proof.
  intros. apply in_map_iff. exists state. now split.
Qed.

Lemma direct_unary_rule_in : forall d State eq_dec
    (system : FullZeroBVASS d State) rule,
  List.In rule (full_zero_unary_rules system) ->
  List.In (direct_unary_rule eq_dec system rule)
    (stateful_rules (direct_bottom_up eq_dec system)).
Proof.
  intros. apply in_or_app. left. apply in_map_iff.
  exists rule. now split.
Qed.

Lemma direct_split_rule_in : forall d State eq_dec
    (system : FullZeroBVASS d State) rule,
  List.In rule (full_zero_split_rules system) ->
  List.In (direct_split_rule eq_dec system rule)
    (stateful_rules (direct_bottom_up eq_dec system)).
Proof.
  intros. apply in_or_app. right. apply in_map_iff.
  exists rule. now split.
Qed.

Lemma direct_bottom_up_forward : forall d State eq_dec
    (system : FullZeroBVASS d State) state counters,
  full_zero_test_rules system = [] ->
  FullZeroReach system state counters ->
  SReach (direct_bottom_up eq_dec system)
    (direct_state eq_dec system state) counters.
Proof.
  intros d State eq_dec system state counters Hfree Hreach.
  induction Hreach as
    [state Hleaf
    |rule source target Hrule Happly Hchild IH
    |rule source left right Hrule Hsum Hleft IHleft Hright IHright
    |rule Hrule Hchild IH].
  - apply sreach_initial. now apply direct_initial_in.
  - eapply sreach_rule with
      (rule := direct_unary_rule eq_dec system rule)
      (child_configs :=
        [(direct_state eq_dec system (unary_zero_target d State rule),
          target)]).
    + now apply direct_unary_rule_in.
    + constructor; [exact IH|constructor].
    + reflexivity.
    + now apply direct_unary_apply.
  - subst source. eapply sreach_rule with
      (rule := direct_split_rule eq_dec system rule)
      (child_configs :=
        [(direct_state eq_dec system (split_zero_left State rule), left);
         (direct_state eq_dec system (split_zero_right State rule), right)]).
    + now apply direct_split_rule_in.
    + constructor; [exact IHleft|]. constructor; [exact IHright|constructor].
    + reflexivity.
    + apply zero_displacement_two.
  - rewrite Hfree in Hrule. contradiction.
Qed.

Lemma direct_initials_spec : forall d State eq_dec
    (system : FullZeroBVASS d State) config,
  List.In config (direct_initials eq_dec system) ->
  exists state,
    List.In state (full_zero_leaves system) /\
    config = (direct_state eq_dec system state, nvec_zero d).
Proof.
  intros d State eq_dec system config Hin.
  apply in_map_iff in Hin. destruct Hin as [state [<- Hstate]]. eauto.
Qed.

Lemma direct_rule_spec : forall d State eq_dec
    (system : FullZeroBVASS d State) generated,
  List.In generated (stateful_rules (direct_bottom_up eq_dec system)) ->
  (exists rule,
      List.In rule (full_zero_unary_rules system) /\
      generated = direct_unary_rule eq_dec system rule) \/
  (exists rule,
      List.In rule (full_zero_split_rules system) /\
      generated = direct_split_rule eq_dec system rule).
Proof.
  intros d State eq_dec system generated Hin.
  apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - left. apply in_map_iff in Hin. destruct Hin as [rule [<- Hrule]]. eauto.
  - right. apply in_map_iff in Hin. destruct Hin as [rule [<- Hrule]]. eauto.
Qed.

Definition DirectReachProperty {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State)
    (state : Fin.t (full_zero_state_count system))
    (counters : NVec d) : Prop :=
  forall original,
    List.In original (full_zero_states system) ->
    state = direct_state eq_dec system original ->
    FullZeroReach system original counters.

Definition DirectChildrenProperty {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State)
    (configs : list (SConfig d (full_zero_state_count system))) : Prop :=
  List.Forall (fun config =>
    DirectReachProperty eq_dec system (fst config) (snd config)) configs.

Lemma direct_bottom_up_backward_mut : forall d State eq_dec
    (system : FullZeroBVASS d State),
  (forall state counters,
    SReach (direct_bottom_up eq_dec system) state counters ->
    DirectReachProperty eq_dec system state counters) /\
  (forall configs,
    SReachChildren (direct_bottom_up eq_dec system) configs ->
    DirectChildrenProperty eq_dec system configs).
Proof.
  intros d State eq_dec system. apply SReach_mutind.
  - intros state counters Hinitial original Horiginal Hstate.
    apply direct_initials_spec in Hinitial.
    destruct Hinitial as [leaf [Hleaf Hconfig]].
    injection Hconfig as Hencoded Hcounters. subst counters.
    assert (leaf = original).
    { apply direct_state_injective with (system := system) (eq_dec := eq_dec).
      - now apply full_zero_leaf_in_states.
      - exact Horiginal.
      - congruence. }
    subst original. constructor. exact Hleaf.
  - intros generated child_configs result Hgenerated Hchildren IHchildren
      Hstates Happly original Horiginal Houtput.
    apply direct_rule_spec in Hgenerated.
    destruct Hgenerated as
      [[rule [Hrule ->]]|[rule [Hrule ->]]].
    + cbn [output_state] in Houtput.
      assert (Hsource : unary_zero_source d State rule = original).
      { apply direct_state_injective with (system := system) (eq_dec := eq_dec).
        - now apply unary_zero_source_in_states with (rule := rule).
        - exact Horiginal.
        - exact Houtput. }
      subst original.
      destruct child_configs as [|child rest].
      { apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      destruct rest as [|extra rest].
      2:{ apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      inversion IHchildren as [|? ? Hchild _]; subst.
      apply Permutation_sym, Permutation_length_1_inv in Hstates.
      inversion Hstates; subst.
      eapply full_zero_reach_unary with (target_counters := snd child).
      * exact Hrule.
      * apply direct_unary_apply_reverse. exact Happly.
      * apply Hchild.
        -- now apply unary_zero_target_in_states with (rule := rule).
        -- exact H0.
    + cbn [output_state] in Houtput.
      destruct (split_zero_states_in d State system rule Hrule)
        as [Hsource [Hleft Hright]].
      assert (split_zero_source State rule = original).
      { apply direct_state_injective with (system := system) (eq_dec := eq_dec);
          assumption. }
      subst original.
      destruct child_configs as [|first rest].
      { apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      destruct rest as [|second rest].
      { apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      destruct rest as [|extra rest].
      2:{ apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      inversion IHchildren as [|? ? Hfirst Htail]; subst.
      inversion Htail as [|? ? Hsecond _]; subst.
      apply Permutation_sym, Permutation_length_2_inv in Hstates.
      destruct Hstates as [Horder|Horder]; inversion Horder; subst.
      * eapply full_zero_reach_split with
          (left_counters := snd first) (right_counters := snd second).
        -- exact Hrule.
        -- symmetry. now apply zero_displacement_pair_eq in Happly.
        -- apply Hfirst; assumption.
        -- apply Hsecond; assumption.
      * eapply full_zero_reach_split with
          (left_counters := snd second) (right_counters := snd first).
        -- exact Hrule.
        -- rewrite nvec_add_comm_stateful. symmetry.
           now apply zero_displacement_pair_eq in Happly.
        -- apply Hsecond; assumption.
        -- apply Hfirst; assumption.
  - constructor.
  - intros state counters configs Hhead IHhead Htail IHtail.
    constructor; assumption.
Qed.

Lemma direct_bottom_up_backward : forall d State eq_dec
    (system : FullZeroBVASS d State) state counters,
  List.In state (full_zero_states system) ->
  SReach (direct_bottom_up eq_dec system)
    (direct_state eq_dec system state) counters ->
  FullZeroReach system state counters.
Proof.
  intros d State eq_dec system state counters Hstate Hreach.
  pose proof ((proj1 (direct_bottom_up_backward_mut
    d State eq_dec system)) _ _ Hreach) as Hmeaning.
  apply Hmeaning; [exact Hstate|reflexivity].
Qed.

Theorem direct_zero_test_free_correct : forall d State eq_dec
    (system : FullZeroBVASS d State) state counters,
  zero_test_freeb system = true ->
  List.In state (full_zero_states system) ->
  (FullZeroReach system state counters <->
   SReach (direct_bottom_up eq_dec system)
     (direct_root_state eq_dec system state) counters).
Proof.
  intros d State eq_dec system state counters Hfree Hstate.
  apply zero_test_freeb_spec in Hfree. split.
  - now apply direct_bottom_up_forward.
  - now apply direct_bottom_up_backward.
Qed.
