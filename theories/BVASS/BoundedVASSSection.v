From Coq Require Import List Vector Arith ZArith Bool Lia Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Order Require Import PeriodicOrder.
From Mell.Reduction Require Import StateErasure.
From Mell.BVASS Require Import Stateful StatefulAmalgamation BoundedBranching
  VASSSection.
From Mell.VAS Require Import Runs StatefulVAS.

Import ListNotations.

(** The semantic target of the compiler. *)
Definition ReachDepth {d q} (B : SBVAS d q) (bound : nat)
    (state : Fin.t q) (counters : NVec d) : Prop :=
  exists run,
    ValidSRun B run /\
    root_config run = (state, counters) /\
    (branching_depth run <= bound)%nat.

(** Application of one genuinely branching rule to configurations drawn
    from a relation.  The list retains occurrences and multiplicities. *)
Definition RuleImage {d q} (B : SBVAS d q) (rule : SRule d q)
    (relation : Fin.t q -> NVec d -> Prop)
    (state : Fin.t q) (counters : NVec d) : Prop :=
  List.In rule (stateful_rules B) /\
  (2 <= List.length (input_states rule))%nat /\
  exists children : list (Mell.BVASS.Stateful.SConfig d q),
    List.Forall (fun child => relation (fst child) (snd child)) children /\
    Permutation (List.map fst children) (input_states rule) /\
    add_displacement (rule_delta rule) (List.map snd children) = Some counters /\
    state = output_state rule.

Definition BranchingImages {d q} (B : SBVAS d q)
    (relation : Fin.t q -> NVec d -> Prop)
    (state : Fin.t q) (counters : NVec d) : Prop :=
  exists rule,
    RuleImage B rule relation state counters.

Definition BoundedSeed {d q} (B : SBVAS d q) (bound : nat)
    (state : Fin.t q) (counters : NVec d) : Prop :=
  List.In (state, counters) (initial_configs B) \/
  BranchingImages B (ReachDepth B bound) state counters.

(** A convenient relational form of the final contract. *)
Definition BoundedSectionCorrect {d q} (B : SBVAS d q) (bound : nat)
    (W : VASSSection d q) : Prop :=
  forall state counters,
    VASSSectionReach W state counters <-> ReachDepth B bound state counters.

Lemma unary_rule_application : forall d q (B : SBVAS d q)
    rule source_state source target,
    List.In rule (stateful_rules B) ->
    input_states rule = [source_state] ->
    add_displacement (rule_delta rule) [source] = Some target ->
    DirectVASReach (unary_vas B)
      source_state source (output_state rule) target.
Proof.
  intros d q B rule source_state source target Hrule Hinputs Happly.
  eapply direct_vas_reach_step with
      (transition :=
        {| VASTransitionSource := source_state;
           VASTransitionAction := rule_delta rule;
           VASTransitionTarget := output_state rule |})
      (target := target).
  - apply unary_vas_in_iff. exists rule, source_state. auto.
  - assert (Hsum : nvec_sum [source] = source).
    { rewrite nvec_sum_rsum_stateful. cbn.
      rewrite nvec_add_comm_stateful. apply nvec_add_zero_left_stateful. }
    apply step_equation_action.
    apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros index index' Hindex; subst index'.
    unfold add_displacement in Happly. rewrite Hsum in Happly.
    pose proof (zvec_to_nvec_sound d _ _ Happly index) as Hsound.
    unfold zvec_add, nvec_to_zvec in Hsound |- *.
    rewrite (nth_map Z.of_nat target index index eq_refl).
    rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl) in Hsound.
    rewrite (nth_map Z.of_nat source index index eq_refl) in Hsound.
    rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
      (nth_map Z.of_nat source index index eq_refl).
    cbn in Hsound |- *. lia.
  - constructor.
Qed.

Lemma unary_add_displacement_of_action : forall d (delta : ZVec d)
    source target,
    delta = StepAction source target ->
    add_displacement delta [source] = Some target.
Proof.
  intros d delta source target ->.
  assert (Hsum : nvec_sum [source] = source).
  { rewrite nvec_sum_rsum_stateful. cbn.
    rewrite nvec_add_comm_stateful. apply nvec_add_zero_left_stateful. }
  unfold add_displacement. rewrite Hsum.
  replace (zvec_add (StepAction source target) (nvec_to_zvec source))
    with (nvec_to_zvec target).
  - apply zvec_to_nvec_of_nvec.
  - rewrite (zvec_add_comm d (StepAction source target) (nvec_to_zvec source)).
    apply step_action_equation.
Qed.

Lemma unary_transition_rule : forall d q (B : SBVAS d q)
    transition source target,
    List.In transition (unary_vas B) ->
    VASTransitionAction transition = StepAction source target ->
    exists rule,
      List.In rule (stateful_rules B) /\
      input_states rule = [VASTransitionSource transition] /\
      output_state rule = VASTransitionTarget transition /\
      add_displacement (rule_delta rule) [source] = Some target.
Proof.
  intros d q B transition source target Hin Haction.
  apply unary_vas_in_iff in Hin as [rule [source_state
    [Hrule [Hinputs ->]]]].
  exists rule. cbn in Haction |- *. repeat split; auto.
  now apply unary_add_displacement_of_action.
Qed.

Definition unary_parent_run {d q} (rule : SRule d q)
    (child : SRun d q) (target : NVec d) : SRun d q :=
  srun_node rule (sruns_cons child sruns_nil) (output_state rule, target).

Lemma unary_parent_valid : forall d q (B : SBVAS d q) rule child target,
    ValidSRun B child ->
    List.In rule (stateful_rules B) ->
    input_states rule = [fst (root_config child)] ->
    add_displacement (rule_delta rule) [snd (root_config child)] = Some target ->
    ValidSRun B (unary_parent_run rule child target).
Proof.
  intros d q B rule child target Hchild Hrule Hinputs Happly.
  unfold unary_parent_run. econstructor; cbn.
  - exact Hrule.
  - constructor; [exact Hchild|constructor].
  - rewrite Hinputs. apply Permutation_refl.
  - exact Happly.
  - reflexivity.
Qed.

Lemma unary_direct_reach_wrap : forall d q (B : SBVAS d q)
    source_state source target_state target run,
    ValidSRun B run ->
    root_config run = (source_state, source) ->
    DirectVASReach (unary_vas B) source_state source target_state target ->
    exists wrapped,
      ValidSRun B wrapped /\
      root_config wrapped = (target_state, target) /\
      branching_depth wrapped = branching_depth run.
Proof.
  intros d q B source_state source target_state target run Hvalid Hroot Hreach.
  revert run Hvalid Hroot. induction Hreach; intros run Hvalid Hroot.
  - exists run. auto.
  - destruct (unary_transition_rule d q B transition source target H H0)
      as [rule [Hrule [Hinputs [Houtput Happly]]]].
    assert (Hparent : ValidSRun B (unary_parent_run rule run target)).
    { eapply unary_parent_valid.
      - exact Hvalid.
      - exact Hrule.
      - rewrite Hroot. cbn. exact Hinputs.
      - rewrite Hroot. cbn. exact Happly. }
    specialize (IHHreach (unary_parent_run rule run target) Hparent).
    cbn in IHHreach. rewrite Houtput in IHHreach.
    specialize (IHHreach eq_refl).
    destruct IHHreach as [wrapped [Hwrapped [Htarget Hdepth]]].
    exists wrapped. split; [exact Hwrapped|].
    split; [exact Htarget|]. cbn in Hdepth. exact Hdepth.
Qed.

Lemma unary_closure_reach_depth : forall d q (B : SBVAS d q) bound state counters,
    UnaryClosure B (ReachDepth B bound) state counters ->
    ReachDepth B bound state counters.
Proof.
  intros d q B bound state counters
    [source_state [source [[run [Hvalid [Hroot Hdepth]]] Hreach]]].
  destruct (unary_direct_reach_wrap d q B source_state source state counters
    run Hvalid Hroot Hreach) as [wrapped [Hwrapped [Htarget Hsame]]].
  exists wrapped. repeat split; auto. now rewrite Hsame.
Qed.

Lemma initial_reach_depth : forall d q (B : SBVAS d q) bound state counters,
    List.In (state, counters) (initial_configs B) ->
    ReachDepth B bound state counters.
Proof.
  intros d q B bound state counters Hinitial.
  exists (srun_leaf (state, counters)). split.
  - constructor. exact Hinitial.
  - split; [reflexivity|]. cbn. lia.
Qed.

Lemma reach_depth_children_runs : forall d q (B : SBVAS d q) bound children,
    List.Forall (fun child => ReachDepth B bound (fst child) (snd child))
      children ->
    exists runs,
      ValidSRuns B runs /\
      sruns_configs runs = children /\
      (runs_max_branching_depth runs <= bound)%nat.
Proof.
  intros d q B bound children Hchildren. induction Hchildren.
  - exists sruns_nil. split; [constructor|].
    split; [reflexivity|]. cbn. lia.
  - destruct x as [state counters].
    destruct H as [run [Hrun [Hroot Hdepth]]].
    destruct IHHchildren as [runs [Hruns [Hconfigs Hmax]]].
    exists (sruns_cons run runs). split.
    + constructor; assumption.
    + split.
      * cbn. f_equal; assumption.
      * cbn. apply Nat.max_lub; assumption.
Qed.

Lemma branching_image_reach_depth : forall d q (B : SBVAS d q)
    bound state counters,
    BranchingImages B (ReachDepth B bound) state counters ->
    ReachDepth B (S bound) state counters.
Proof.
  intros d q B bound state counters [rule
    [Hrule [Harity [children [Hchildren [Hstates [Happly Hstate]]]]]]].
  destruct (reach_depth_children_runs d q B bound children Hchildren)
    as [runs [Hruns [Hconfigs Hmax]]].
  exists (srun_node rule runs (state, counters)). split.
  - econstructor; cbn; eauto; now rewrite Hconfigs.
  - split; [reflexivity|]. rewrite branching_depth_node_formula.
    rewrite Hconfigs.
    pose proof (Permutation_length Hstates) as Hlength.
    rewrite List.length_map in Hlength.
    assert (Hchildren_arity : (2 <= List.length children)%nat).
    { eapply Nat.le_trans; [exact Harity|].
      destruct Hlength. apply Nat.le_refl. }
    assert (Hleb : Nat.leb 2 (List.length children) = true).
    { apply Nat.leb_le. exact Hchildren_arity. }
    rewrite Hleb. cbn. lia.
Qed.

Lemma bounded_seed_reach_depth : forall d q (B : SBVAS d q)
    bound state counters,
    BoundedSeed B bound state counters ->
    ReachDepth B (S bound) state counters.
Proof.
  intros d q B bound state counters [Hinitial|Hbranch].
  - apply initial_reach_depth. exact Hinitial.
  - now apply branching_image_reach_depth.
Qed.

Lemma unary_closure_bounded_seed_sound : forall d q (B : SBVAS d q)
    bound state counters,
    UnaryClosure B (BoundedSeed B bound) state counters ->
    ReachDepth B (S bound) state counters.
Proof.
  intros d q B bound state counters
    [source_state [source [Hseed Hreach]]].
  apply unary_closure_reach_depth.
  exists source_state, source. split; [now apply bounded_seed_reach_depth|exact Hreach].
Qed.

(** Counter-block primitives used by the rule-image compiler.  The list
    order is the child-occurrence order; equal states are never quotiented. *)
Fixpoint repeated_nvec {width} (count : nat) (value : NVec width) :
    NVec (count * width) :=
  match count with
  | O => @Vector.nil nat
  | S tail => Vector.append value (repeated_nvec tail value)
  end.

Fixpoint repeated_zvec {width} (count : nat) (value : ZVec width) :
    ZVec (count * width) :=
  match count with
  | O => @Vector.nil Z
  | S tail => Vector.append value (repeated_zvec tail value)
  end.

Fixpoint block_lifts_z {width} (count : nat) (value : ZVec width) :
    list (ZVec (count * width)) :=
  match count with
  | O => []
  | S tail =>
      Vector.append value (zvec_zero (tail * width)) ::
      List.map (fun lifted => Vector.append (zvec_zero width) lifted)
        (block_lifts_z tail value)
  end.

Lemma block_lifts_z_length : forall width count (value : ZVec width),
    List.length (block_lifts_z count value) = count.
Proof.
  intros width count. induction count; intro value; cbn; auto.
  now rewrite List.length_map, IHcount.
Qed.

Fixpoint block_lifts_n {width} (count : nat) (value : NVec width) :
    list (NVec (count * width)) :=
  match count with
  | O => []
  | S tail =>
      Vector.append value (nvec_zero (tail * width)) ::
      List.map (fun lifted => Vector.append (nvec_zero width) lifted)
        (block_lifts_n tail value)
  end.

Definition block_z_at {width} (count index : nat) (value : ZVec width) :
    ZVec (count * width) :=
  vector_of_function (count * width) (fun position =>
    let coordinate := proj1_sig (Fin.to_nat position) in
    if (Nat.leb (index * width) coordinate &&
        Nat.ltb coordinate ((S index) * width))%bool
    then List.nth (coordinate - index * width) (Vector.to_list value) 0%Z
    else 0%Z).

Definition block_n_at {width} (count index : nat) (value : NVec width) :
    NVec (count * width) :=
  vector_of_function (count * width) (fun position =>
    let coordinate := proj1_sig (Fin.to_nat position) in
    if (Nat.leb (index * width) coordinate &&
        Nat.ltb coordinate ((S index) * width))%bool
    then List.nth (coordinate - index * width) (Vector.to_list value) O
    else O).

Lemma block_lifts_n_length : forall width count (value : NVec width),
    List.length (block_lifts_n count value) = count.
Proof.
  intros width count. induction count; intro value; cbn; auto.
  now rewrite List.length_map, IHcount.
Qed.

Definition rule_block_width {d q} (W : VASSSection d q) : nat :=
  d + section_aux_dimension W.

Definition rule_child_count {d q} (rule : SRule d q) : nat :=
  List.length (input_states rule).

Definition rule_image_aux_dimension {d q} (rule : SRule d q)
    (W : VASSSection d q) : nat :=
  rule_child_count rule * rule_block_width W.

Definition rule_copy_state {d q} (rule : SRule d q) (W : VASSSection d q)
    (child : Fin.t (rule_child_count rule))
    (state : Fin.t (section_state_count W)) :
    Fin.t (rule_child_count rule * section_state_count W + (1 + q)).
Proof.
  refine (@Fin.L (rule_child_count rule * section_state_count W) (1 + q)
    (Fin.of_nat_lt (p :=
    proj1_sig (Fin.to_nat child) * section_state_count W +
    proj1_sig (Fin.to_nat state)) _)).
  pose proof (proj2_sig (Fin.to_nat child)).
  pose proof (proj2_sig (Fin.to_nat state)).
  destruct (section_state_count W); cbn in *; nia.
Defined.

Definition rule_collect_state {d q} (rule : SRule d q)
    (W : VASSSection d q) :
    Fin.t (rule_child_count rule * section_state_count W + (1 + q)) :=
  Fin.R (rule_child_count rule * section_state_count W) Fin.F1.

Definition rule_output_state {d q} (rule : SRule d q)
    (W : VASSSection d q) (state : Fin.t q) :
    Fin.t (rule_child_count rule * section_state_count W + (1 + q)) :=
  Fin.R (rule_child_count rule * section_state_count W) (Fin.FS state).

Lemma rule_copy_collect_distinct : forall d q (rule : SRule d q)
    (W : VASSSection d q) child state,
    rule_copy_state rule W child state <> rule_collect_state rule W.
Proof.
  intros. unfold rule_copy_state, rule_collect_state.
  apply Fin.L_R_neq.
Qed.

Lemma rule_copy_output_distinct : forall d q (rule : SRule d q)
    (W : VASSSection d q) child state output,
    rule_copy_state rule W child state <> rule_output_state rule W output.
Proof.
  intros. unfold rule_copy_state, rule_output_state.
  apply Fin.L_R_neq.
Qed.

Lemma rule_collect_output_distinct : forall d q (rule : SRule d q)
    (W : VASSSection d q) output,
    rule_collect_state rule W <> rule_output_state rule W output.
Proof.
  intros d q rule W output Heq. unfold rule_collect_state,
    rule_output_state in Heq. apply Fin.R_inj in Heq. inversion Heq.
Qed.

Definition rule_block_nvec {d q} (rule : SRule d q)
    (W : VASSSection d q) (child : nat)
    (value : NVec (rule_block_width W)) :
    NVec (d + rule_image_aux_dimension rule W) :=
  Vector.append (nvec_zero d)
    (block_n_at (rule_child_count rule) child value).

Definition rule_block_zvec {d q} (rule : SRule d q)
    (W : VASSSection d q) (child : nat)
    (value : ZVec (rule_block_width W)) :
    ZVec (d + rule_image_aux_dimension rule W) :=
  Vector.append (zvec_zero d)
    (block_z_at (rule_child_count rule) child value).

Definition rule_copy_transition {d q} (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule))
    (transition : VASTransition
      (rule_block_width W) (section_state_count W)) :
    VASTransition (d + rule_image_aux_dimension rule W)
      (rule_child_count rule * section_state_count W + (1 + q)) :=
  {| VASTransitionSource := rule_copy_state rule W child
       (VASTransitionSource transition);
     VASTransitionAction := rule_block_zvec rule W
       (proj1_sig (Fin.to_nat child)) (VASTransitionAction transition);
     VASTransitionTarget := rule_copy_state rule W child
       (VASTransitionTarget transition) |}.

Definition rule_copy_transitions {d q} (rule : SRule d q)
    (W : VASSSection d q) :=
  List.flat_map (fun child =>
    List.map (rule_copy_transition rule W child) (section_system W))
    (all_fin (rule_child_count rule)).

Definition fin_successor {n} (index : Fin.t n) : option (Fin.t n).
Proof.
  destruct (lt_dec (S (proj1_sig (Fin.to_nat index))) n) as [Hlt|Hnot].
  - exact (Some (Fin.of_nat_lt Hlt)).
  - exact None.
Defined.

Definition rule_required_state {d q} (rule : SRule d q)
    (child : Fin.t (rule_child_count rule)) : Fin.t q :=
  Vector.nth (Vector.of_list (input_states rule)) child.

Definition rule_advance_to_initial {d q} (rule : SRule d q)
    (W : VASSSection d q) (child next : Fin.t (rule_child_count rule))
    (config : Mell.VAS.StatefulVAS.SConfig
      (rule_block_width W) (section_state_count W)) :
    VASTransition (d + rule_image_aux_dimension rule W)
      (rule_child_count rule * section_state_count W + (1 + q)) :=
  {| VASTransitionSource := rule_copy_state rule W child
       (section_accept_state W (rule_required_state rule child));
     VASTransitionAction := rule_block_zvec rule W
       (proj1_sig (Fin.to_nat next)) (nvec_to_zvec (snd config));
     VASTransitionTarget := rule_copy_state rule W next (fst config) |}.

Definition rule_advance_to_collect {d q} (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule)) :
    VASTransition (d + rule_image_aux_dimension rule W)
      (rule_child_count rule * section_state_count W + (1 + q)) :=
  {| VASTransitionSource := rule_copy_state rule W child
       (section_accept_state W (rule_required_state rule child));
     VASTransitionAction := zvec_zero (d + rule_image_aux_dimension rule W);
     VASTransitionTarget := rule_collect_state rule W |}.

Definition rule_advance_transitions_for {d q} (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule)) :=
  match fin_successor child with
  | Some next =>
      List.map (rule_advance_to_initial rule W child next)
        (section_initial_configs W)
  | None => [rule_advance_to_collect rule W child]
  end.

Definition rule_advance_transitions {d q} (rule : SRule d q)
    (W : VASSSection d q) :=
  List.flat_map (rule_advance_transitions_for rule W)
    (all_fin (rule_child_count rule)).

Definition rule_transfer_action {d q} (rule : SRule d q)
    (W : VASSSection d q) (child coordinate : nat) :
    ZVec (d + rule_image_aux_dimension rule W) :=
  zvec_add
    (one_hot_z (d + rule_image_aux_dimension rule W) coordinate)
    (Vector.map Z.opp
      (one_hot_z (d + rule_image_aux_dimension rule W)
        (d + child * rule_block_width W + coordinate))).

Definition rule_transfer_transition {d q} (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule))
    (coordinate : Fin.t d) :
    VASTransition (d + rule_image_aux_dimension rule W)
      (rule_child_count rule * section_state_count W + (1 + q)) :=
  {| VASTransitionSource := rule_collect_state rule W;
     VASTransitionAction := rule_transfer_action rule W
       (proj1_sig (Fin.to_nat child)) (proj1_sig (Fin.to_nat coordinate));
     VASTransitionTarget := rule_collect_state rule W |}.

Definition rule_transfer_transitions {d q} (rule : SRule d q)
    (W : VASSSection d q) :=
  List.flat_map (fun child =>
    List.map (rule_transfer_transition rule W child) (all_fin d))
    (all_fin (rule_child_count rule)).

Definition rule_final_transition {d q} (rule : SRule d q)
    (W : VASSSection d q) :
    VASTransition (d + rule_image_aux_dimension rule W)
      (rule_child_count rule * section_state_count W + (1 + q)) :=
  {| VASTransitionSource := rule_collect_state rule W;
     VASTransitionAction := Vector.append (rule_delta rule)
       (zvec_zero (rule_image_aux_dimension rule W));
     VASTransitionTarget := rule_output_state rule W (output_state rule) |}.

Definition rule_image_system {d q} (rule : SRule d q)
    (W : VASSSection d q) :=
  rule_copy_transitions rule W ++
  rule_advance_transitions rule W ++
  rule_transfer_transitions rule W ++
  [rule_final_transition rule W].

Definition first_child {d q} (rule : SRule d q) :
    Fin.t (rule_child_count rule).
Proof.
  refine (Fin.of_nat_lt (p := 0) _).
  unfold rule_child_count.
  destruct (input_states rule) eqn:Hinputs.
  - exfalso. exact (input_nonempty rule Hinputs).
  - cbn. lia.
Defined.

Definition rule_image_initial {d q} (rule : SRule d q)
    (W : VASSSection d q)
    (config : Mell.VAS.StatefulVAS.SConfig
      (rule_block_width W) (section_state_count W)) :=
  (rule_copy_state rule W (first_child rule) (fst config),
   rule_block_nvec rule W 0 (snd config)).

Definition compile_rule_image {d q} (rule : SRule d q)
    (W : VASSSection d q) : VASSSection d q :=
  {| section_aux_dimension := rule_image_aux_dimension rule W;
     section_state_count :=
       rule_child_count rule * section_state_count W + (1 + q);
     section_system := rule_image_system rule W;
     section_initial_configs :=
       List.map (rule_image_initial rule W) (section_initial_configs W);
     section_accept_state := rule_output_state rule W |}.

Fixpoint map_with_index_from {A B} (start : nat) (f : nat -> A -> B)
    (values : list A) : list B :=
  match values with
  | [] => []
  | value :: tail =>
      f start value :: map_with_index_from (S start) f tail
  end.

Definition map_with_index {A B} (f : nat -> A -> B) (values : list A) :=
  map_with_index_from 0 f values.

Definition rule_blocks_counter {d q} (rule : SRule d q)
    (W : VASSSection d q) (blocks : list (NVec (rule_block_width W))) :
    NVec (rule_image_aux_dimension rule W) :=
  nvec_sum (map_with_index
    (fun index value => block_n_at (rule_child_count rule) index value)
    blocks).

Definition rule_machine_counter {d q} (rule : SRule d q)
    (W : VASSSection d q) (main : NVec d)
    (blocks : list (NVec (rule_block_width W))) :
    NVec (d + rule_image_aux_dimension rule W) :=
  Vector.append main (rule_blocks_counter rule W blocks).

Lemma map_with_index_length : forall A B start (f : nat -> A -> B) values,
    List.length (map_with_index_from start f values) = List.length values.
Proof.
  intros A B start f values. revert start.
  induction values; intros start; cbn; [reflexivity|].
  now rewrite IHvalues.
Qed.

Lemma rule_output_state_injective : forall d q (rule : SRule d q)
    (W : VASSSection d q) (left right : Fin.t q),
    rule_output_state rule W left = rule_output_state rule W right ->
    left = right.
Proof.
  intros d q rule W left right Heq. unfold rule_output_state in Heq.
  apply Fin.R_inj in Heq. now apply Fin.FS_inj in Heq.
Qed.

Lemma rule_image_transition_cases : forall d q (rule : SRule d q)
    (W : VASSSection d q) transition,
    List.In transition (rule_image_system rule W) ->
    List.In transition (rule_copy_transitions rule W) \/
    List.In transition (rule_advance_transitions rule W) \/
    List.In transition (rule_transfer_transitions rule W) \/
    transition = rule_final_transition rule W.
Proof.
  intros d q rule W transition Hin. unfold rule_image_system in Hin.
  repeat rewrite in_app_iff in Hin.
  destruct Hin as [Hcopy|[Hadvance|[Htransfer|Hfinal]]].
  - now left.
  - now right; left.
  - now right; right; left.
  - cbn in Hfinal. destruct Hfinal as [Heq|Hfalse]; [|contradiction].
    now right; right; right.
Qed.

Lemma rule_copy_transition_source_is_copy : forall d q
    (rule : SRule d q) (W : VASSSection d q) transition,
    List.In transition (rule_copy_transitions rule W) ->
    exists child original,
      List.In original (section_system W) /\
      transition = rule_copy_transition rule W child original.
Proof.
  intros d q rule W transition Hin. unfold rule_copy_transitions in Hin.
  apply in_flat_map in Hin as [child [Hchild Hin]].
  apply List.in_map_iff in Hin as [original [<- Horiginal]].
  eauto.
Qed.

Lemma rule_advance_transition_source_is_copy : forall d q
    (rule : SRule d q) (W : VASSSection d q) transition,
    List.In transition (rule_advance_transitions rule W) ->
    exists child,
      VASTransitionSource transition = rule_copy_state rule W child
        (section_accept_state W (rule_required_state rule child)).
Proof.
  intros d q rule W transition Hin. unfold rule_advance_transitions in Hin.
  apply in_flat_map in Hin as [child [Hchild Hin]].
  unfold rule_advance_transitions_for in Hin.
  destruct (fin_successor child) as [next|] eqn:Hnext.
  - apply List.in_map_iff in Hin as [config [<- _]].
    exists child. reflexivity.
  - cbn in Hin. destruct Hin as [<-|[]].
    exists child. reflexivity.
Qed.

Lemma rule_output_has_no_step : forall d q (rule : SRule d q)
    (W : VASSSection d q) state transition,
    List.In transition (rule_image_system rule W) ->
    VASTransitionSource transition = rule_output_state rule W state -> False.
Proof.
  intros d q rule W state transition Hin Hsource.
  destruct (rule_image_transition_cases d q rule W transition Hin)
    as [Hcopy|[Hadvance|[Htransfer|Hfinal]]].
  - destruct (rule_copy_transition_source_is_copy d q rule W transition Hcopy)
      as [child [original [_ ->]]]. cbn in Hsource.
    eapply rule_copy_output_distinct; exact Hsource.
  - destruct (rule_advance_transition_source_is_copy d q rule W transition Hadvance)
      as [child Hcopy]. rewrite Hcopy in Hsource.
    eapply rule_copy_output_distinct; exact Hsource.
  - unfold rule_transfer_transitions in Htransfer.
    apply in_flat_map in Htransfer as [child [_ Htransfer]].
    apply List.in_map_iff in Htransfer as [coordinate [<- _]].
    cbn in Hsource. eapply rule_collect_output_distinct; exact Hsource.
  - subst transition. cbn in Hsource.
    eapply rule_collect_output_distinct; exact Hsource.
Qed.

Lemma rule_output_reach_inv : forall d q (rule : SRule d q)
    (W : VASSSection d q) state counters final_state final,
    DirectVASReach (rule_image_system rule W)
      (rule_output_state rule W state) counters final_state final ->
    final_state = rule_output_state rule W state /\ final = counters.
Proof.
  intros d q rule W state counters final_state final Hreach.
  inversion Hreach; subst; [auto|].
  exfalso. eapply rule_output_has_no_step; eauto.
Qed.

Lemma block_z_at_step_action : forall width count index
    (source target : NVec width),
    block_z_at count index (StepAction source target) =
    StepAction (block_n_at count index source)
      (block_n_at count index target).
Proof.
  intros width count index source target.
  apply (proj1 (Vector.eq_nth_iff Z (count * width) _ _)).
  intros position position' Hposition; subst position'.
  unfold block_z_at, block_n_at.
  repeat rewrite nth_vector_of_function.
  set (coordinate := proj1_sig (Fin.to_nat position)).
  destruct (Nat.leb (index * width) coordinate &&
    Nat.ltb coordinate (S index * width))%bool eqn:Hinside.
  - pose proof Hinside as Hinside_true.
    apply andb_true_iff in Hinside_true as [Hlower Hupper].
    apply Nat.leb_le in Hlower. apply Nat.ltb_lt in Hupper.
    assert (Hoffset : (coordinate - index * width < width)%nat) by nia.
    unfold StepAction, zvec_sub_run, nvec_to_zvec.
    rewrite <- (to_list_nth_order Z width
      (Vector.map2 Z.sub (Vector.map Z.of_nat target)
        (Vector.map Z.of_nat source))
      (coordinate - index * width) Hoffset 0%Z).
    unfold Vector.nth_order.
    rewrite (nth_map2 Z.sub _ _
      (Fin.of_nat_lt Hoffset) (Fin.of_nat_lt Hoffset)
      (Fin.of_nat_lt Hoffset) eq_refl eq_refl).
    repeat rewrite (nth_map Z.of_nat _
      (Fin.of_nat_lt Hoffset) (Fin.of_nat_lt Hoffset) eq_refl).
    cbn [StepAction zvec_sub_run nvec_to_zvec].
    repeat rewrite nth_vector_of_function.
    cbn [StepAction zvec_sub_run nvec_to_zvec].
    rewrite (nth_map2 Z.sub _ _ position position position eq_refl eq_refl).
    repeat rewrite (nth_map Z.of_nat _ position position eq_refl).
    repeat rewrite nth_vector_of_function. fold coordinate. rewrite Hinside.
    rewrite <- (to_list_nth_order nat width target
      (coordinate - index * width) Hoffset O).
    rewrite <- (to_list_nth_order nat width source
      (coordinate - index * width) Hoffset O).
    reflexivity.
  - unfold StepAction, zvec_sub_run, nvec_to_zvec.
    rewrite (nth_map2 Z.sub _ _ position position position eq_refl eq_refl).
    repeat rewrite (nth_map Z.of_nat _ position position eq_refl).
    repeat rewrite nth_vector_of_function. fold coordinate. rewrite Hinside.
    reflexivity.
Qed.

Lemma rule_block_step_action : forall d q (rule : SRule d q)
    (W : VASSSection d q) index source target,
    rule_block_zvec rule W index (StepAction source target) =
    StepAction (rule_block_nvec rule W index source)
      (rule_block_nvec rule W index target).
Proof.
  intros. unfold rule_block_zvec, rule_block_nvec.
  rewrite step_action_append, step_action_zero,
    block_z_at_step_action. reflexivity.
Qed.

Lemma rule_copy_transition_in : forall d q (rule : SRule d q)
    (W : VASSSection d q) child transition,
    List.In transition (section_system W) ->
    List.In (rule_copy_transition rule W child transition)
      (rule_image_system rule W).
Proof.
  intros d q rule W child transition Hin.
  unfold rule_image_system. apply in_or_app. left.
  unfold rule_copy_transitions. apply in_flat_map.
  exists child. split; [apply all_fin_complete|].
  now apply List.in_map.
Qed.

Lemma rule_copy_direct_reach : forall d q (rule : SRule d q)
    (W : VASSSection d q) child source_state source target_state target
    context,
    DirectVASReach (section_system W) source_state source target_state target ->
    DirectVASReach (rule_image_system rule W)
      (rule_copy_state rule W child source_state)
      (nvec_add (rule_block_nvec rule W (proj1_sig (Fin.to_nat child)) source)
        context)
      (rule_copy_state rule W child target_state)
      (nvec_add (rule_block_nvec rule W (proj1_sig (Fin.to_nat child)) target)
        context).
Proof.
  intros d q rule W child source_state source target_state target context Hreach.
  induction Hreach.
  - constructor.
  - eapply direct_vas_reach_step with
      (transition := rule_copy_transition rule W child transition)
      (target := nvec_add
        (rule_block_nvec rule W (proj1_sig (Fin.to_nat child)) target)
        context).
    + now apply rule_copy_transition_in.
    + change (rule_block_zvec rule W (proj1_sig (Fin.to_nat child))
        (VASTransitionAction transition) =
        StepAction
          (nvec_add (rule_block_nvec rule W
            (proj1_sig (Fin.to_nat child)) source) context)
          (nvec_add (rule_block_nvec rule W
            (proj1_sig (Fin.to_nat child)) target) context)).
      rewrite H0, rule_block_step_action.
      symmetry. apply step_action_shift.
    + exact IHHreach.
Qed.

Lemma nvec_to_zvec_is_step_from_zero : forall d (value : NVec d),
    nvec_to_zvec value = StepAction (nvec_zero d) value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  unfold StepAction, zvec_sub_run, nvec_to_zvec, nvec_zero.
  rewrite (nth_map Z.of_nat value index index eq_refl),
    (nth_map2 Z.sub _ _ index index index eq_refl eq_refl),
    (nth_map Z.of_nat value index index eq_refl),
    (nth_map Z.of_nat _ index index eq_refl), const_nth. lia.
Qed.

Lemma rule_advance_to_initial_in : forall d q (rule : SRule d q)
    (W : VASSSection d q) child next config,
    fin_successor child = Some next ->
    List.In config (section_initial_configs W) ->
    List.In (rule_advance_to_initial rule W child next config)
      (rule_image_system rule W).
Proof.
  intros d q rule W child next config Hnext Hconfig.
  unfold rule_image_system. apply in_or_app. right.
  apply in_or_app. left. unfold rule_advance_transitions.
  apply in_flat_map. exists child. split; [apply all_fin_complete|].
  unfold rule_advance_transitions_for. rewrite Hnext.
  now apply List.in_map.
Qed.

Lemma rule_advance_to_initial_reach : forall d q (rule : SRule d q)
    (W : VASSSection d q) child next config context,
    fin_successor child = Some next ->
    List.In config (section_initial_configs W) ->
    DirectVASReach (rule_image_system rule W)
      (rule_copy_state rule W child
        (section_accept_state W (rule_required_state rule child))) context
      (rule_copy_state rule W next (fst config))
      (nvec_add (rule_block_nvec rule W
        (proj1_sig (Fin.to_nat next)) (snd config)) context).
Proof.
  intros d q rule W child next config context Hnext Hconfig.
  eapply direct_vas_reach_step with
      (transition := rule_advance_to_initial rule W child next config)
      (target := nvec_add (rule_block_nvec rule W
        (proj1_sig (Fin.to_nat next)) (snd config)) context).
  - now apply rule_advance_to_initial_in.
  - change (rule_block_zvec rule W (proj1_sig (Fin.to_nat next))
      (nvec_to_zvec (snd config)) =
      StepAction context
        (nvec_add (rule_block_nvec rule W
          (proj1_sig (Fin.to_nat next)) (snd config)) context)).
    rewrite nvec_to_zvec_is_step_from_zero, rule_block_step_action.
    assert (Hzero : rule_block_nvec rule W (proj1_sig (Fin.to_nat next))
        (nvec_zero (rule_block_width W)) =
        nvec_zero (d + rule_image_aux_dimension rule W)).
    { assert (Hblock : block_n_at (rule_child_count rule)
          (proj1_sig (Fin.to_nat next))
          (nvec_zero (rule_block_width W)) =
          nvec_zero (rule_image_aux_dimension rule W)).
      { apply (proj1 (Vector.eq_nth_iff nat
        (rule_child_count rule * rule_block_width W) _ _)).
        intros index index' Heq; subst index'. unfold block_n_at, nvec_zero.
        rewrite nth_vector_of_function, const_nth.
        destruct (_ && _)%bool; [|reflexivity].
        rewrite Vector.to_list_const, List.nth_repeat. reflexivity. }
      unfold rule_block_nvec. rewrite Hblock.
      symmetry. apply nvec_zero_append. }
    transitivity (StepAction
      (nvec_add (rule_block_nvec rule W (proj1_sig (Fin.to_nat next))
        (nvec_zero (rule_block_width W))) context)
      (nvec_add (rule_block_nvec rule W (proj1_sig (Fin.to_nat next))
        (snd config)) context)).
    + symmetry. apply step_action_shift.
    + rewrite Hzero, nvec_add_zero_left_stateful. reflexivity.
  - constructor.
Qed.

Lemma rule_final_transition_in : forall d q (rule : SRule d q)
    (W : VASSSection d q),
    List.In (rule_final_transition rule W) (rule_image_system rule W).
Proof.
  intros. unfold rule_image_system.
  apply in_or_app. right.
  apply in_or_app. right.
  apply in_or_app. right.
  cbn. auto.
Qed.

Lemma rule_advance_to_collect_in : forall d q (rule : SRule d q)
    (W : VASSSection d q) child,
    fin_successor child = None ->
    List.In (rule_advance_to_collect rule W child)
      (rule_image_system rule W).
Proof.
  intros d q rule W child Hlast.
  unfold rule_image_system. apply in_or_app. right.
  apply in_or_app. left. unfold rule_advance_transitions.
  apply in_flat_map. exists child. split; [apply all_fin_complete|].
  unfold rule_advance_transitions_for. rewrite Hlast. cbn. auto.
Qed.

Lemma rule_advance_to_collect_reach : forall d q (rule : SRule d q)
    (W : VASSSection d q) child counters,
    fin_successor child = None ->
    DirectVASReach (rule_image_system rule W)
      (rule_copy_state rule W child
        (section_accept_state W (rule_required_state rule child))) counters
      (rule_collect_state rule W) counters.
Proof.
  intros d q rule W child counters Hlast.
  eapply direct_vas_reach_step with
      (transition := rule_advance_to_collect rule W child)
      (target := counters).
  - now apply rule_advance_to_collect_in.
  - cbn. symmetry. apply step_action_refl.
  - constructor.
Qed.

Lemma rule_transfer_transition_in : forall d q (rule : SRule d q)
    (W : VASSSection d q) child coordinate,
    List.In (rule_transfer_transition rule W child coordinate)
      (rule_image_system rule W).
Proof.
  intros d q rule W child coordinate. unfold rule_image_system.
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  unfold rule_transfer_transitions. apply in_flat_map.
  exists child. split; [apply all_fin_complete|].
  apply List.in_map. apply all_fin_complete.
Qed.

Lemma rule_transfer_action_step : forall d q (rule : SRule d q)
    (W : VASSSection d q) child coordinate,
    rule_transfer_action rule W child coordinate =
    StepAction
      (one_hot_nat (d + rule_image_aux_dimension rule W)
        (d + child * rule_block_width W + coordinate))
      (one_hot_nat (d + rule_image_aux_dimension rule W) coordinate).
Proof.
  intros d q rule W child coordinate.
  unfold rule_transfer_action, StepAction, zvec_sub_run.
  rewrite !one_hot_z_of_nat.
  apply (proj1 (Vector.eq_nth_iff Z
    (d + rule_image_aux_dimension rule W) _ _)).
  intros index index' Heq; subst index'.
  unfold zvec_add, one_hot_z, nvec_to_zvec.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (nth_map Z.opp _ index index eq_refl),
    (nth_map2 Z.sub _ _ index index index eq_refl eq_refl).
  repeat rewrite nth_vector_of_function. lia.
Qed.

Lemma rule_transfer_unit_reach : forall d q (rule : SRule d q)
    (W : VASSSection d q)
    (child : Fin.t (rule_child_count rule)) (coordinate : Fin.t d) context,
    DirectVASReach (rule_image_system rule W)
      (rule_collect_state rule W)
      (nvec_add
        (one_hot_nat (d + rule_image_aux_dimension rule W)
          (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
            proj1_sig (Fin.to_nat coordinate))) context)
      (rule_collect_state rule W)
      (nvec_add
        (one_hot_nat (d + rule_image_aux_dimension rule W)
          (proj1_sig (Fin.to_nat coordinate))) context).
Proof.
  intros d q rule W child coordinate context.
  eapply direct_vas_reach_step with
      (transition := rule_transfer_transition rule W child coordinate)
      (target := nvec_add
        (one_hot_nat (d + rule_image_aux_dimension rule W)
          (proj1_sig (Fin.to_nat coordinate))) context).
  - apply rule_transfer_transition_in.
  - cbn. rewrite rule_transfer_action_step. symmetry.
    apply step_action_shift.
  - constructor.
Qed.

Fixpoint nvec_times {dimension} (count : nat) (value : NVec dimension) :
    NVec dimension :=
  match count with
  | O => nvec_zero dimension
  | S tail => nvec_add value (nvec_times tail value)
  end.

Lemma rule_transfer_units_reach : forall d q (rule : SRule d q)
    (W : VASSSection d q)
    (child : Fin.t (rule_child_count rule)) (coordinate : Fin.t d)
    count context,
    DirectVASReach (rule_image_system rule W)
      (rule_collect_state rule W)
      (nvec_add
        (nvec_times count
          (one_hot_nat (d + rule_image_aux_dimension rule W)
            (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
              proj1_sig (Fin.to_nat coordinate)))) context)
      (rule_collect_state rule W)
      (nvec_add
        (nvec_times count
          (one_hot_nat (d + rule_image_aux_dimension rule W)
            (proj1_sig (Fin.to_nat coordinate)))) context).
Proof.
  intros d q rule W child coordinate count. induction count as [|count IH];
    intro context; cbn.
  - rewrite !nvec_add_zero_left_stateful. constructor.
  - rewrite !nvec_add_assoc_stateful.
    eapply direct_vas_reach_trans.
    + apply rule_transfer_unit_reach.
    + replace (nvec_add
          (one_hot_nat (d + rule_image_aux_dimension rule W)
            (proj1_sig (Fin.to_nat coordinate)))
          (nvec_add
            (nvec_times count
              (one_hot_nat (d + rule_image_aux_dimension rule W)
                (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
                  proj1_sig (Fin.to_nat coordinate)))) context))
        with (nvec_add
          (nvec_times count
            (one_hot_nat (d + rule_image_aux_dimension rule W)
              (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
                proj1_sig (Fin.to_nat coordinate))))
          (nvec_add
            (one_hot_nat (d + rule_image_aux_dimension rule W)
              (proj1_sig (Fin.to_nat coordinate))) context)).
      2:{ rewrite <- !nvec_add_assoc_stateful. f_equal.
          apply nvec_add_comm_stateful. }
      specialize (IH (nvec_add
        (one_hot_nat (d + rule_image_aux_dimension rule W)
          (proj1_sig (Fin.to_nat coordinate))) context)).
      replace (nvec_add
          (one_hot_nat (d + rule_image_aux_dimension rule W)
            (proj1_sig (Fin.to_nat coordinate)))
          (nvec_add
            (nvec_times count
              (one_hot_nat (d + rule_image_aux_dimension rule W)
                (proj1_sig (Fin.to_nat coordinate)))) context))
        with (nvec_add
          (nvec_times count
            (one_hot_nat (d + rule_image_aux_dimension rule W)
              (proj1_sig (Fin.to_nat coordinate))))
          (nvec_add
            (one_hot_nat (d + rule_image_aux_dimension rule W)
              (proj1_sig (Fin.to_nat coordinate))) context)).
      * exact IH.
      * rewrite <- !nvec_add_assoc_stateful.
        f_equal. apply nvec_add_comm_stateful.
Qed.

Record RuleTransferItem {d q} (rule : SRule d q) := {
  transfer_child : Fin.t (rule_child_count rule);
  transfer_coordinate : Fin.t d;
  transfer_count : nat
}.

Definition transfer_child_units {d q} (rule : SRule d q)
    (W : VASSSection d q) (item : RuleTransferItem rule) :=
  nvec_times (transfer_count rule item)
    (one_hot_nat (d + rule_image_aux_dimension rule W)
      (d + proj1_sig (Fin.to_nat (transfer_child rule item)) *
        rule_block_width W +
        proj1_sig (Fin.to_nat (transfer_coordinate rule item)))).

Definition transfer_main_units {d q} (rule : SRule d q)
    (W : VASSSection d q) (item : RuleTransferItem rule) :=
  nvec_times (transfer_count rule item)
    (one_hot_nat (d + rule_image_aux_dimension rule W)
      (proj1_sig (Fin.to_nat (transfer_coordinate rule item)))).

Fixpoint transfer_plan_source {d q} (rule : SRule d q)
    (W : VASSSection d q) (plan : list (RuleTransferItem rule)) :=
  match plan with
  | [] => nvec_zero (d + rule_image_aux_dimension rule W)
  | item :: tail => nvec_add (transfer_child_units rule W item)
      (transfer_plan_source rule W tail)
  end.

Fixpoint transfer_plan_target {d q} (rule : SRule d q)
    (W : VASSSection d q) (plan : list (RuleTransferItem rule)) :=
  match plan with
  | [] => nvec_zero (d + rule_image_aux_dimension rule W)
  | item :: tail => nvec_add (transfer_main_units rule W item)
      (transfer_plan_target rule W tail)
  end.

Lemma rule_transfer_plan_reach : forall d q (rule : SRule d q)
    (W : VASSSection d q) plan context,
    DirectVASReach (rule_image_system rule W)
      (rule_collect_state rule W)
      (nvec_add (transfer_plan_source rule W plan) context)
      (rule_collect_state rule W)
      (nvec_add (transfer_plan_target rule W plan) context).
Proof.
  intros d q rule W plan. induction plan as [|item tail IH]; intro context; cbn.
  - rewrite !nvec_add_zero_left_stateful. constructor.
  - rewrite !nvec_add_assoc_stateful.
    eapply direct_vas_reach_trans.
    + unfold transfer_child_units, transfer_main_units.
      apply rule_transfer_units_reach.
    + fold (transfer_main_units rule W item).
      specialize (IH (nvec_add (transfer_main_units rule W item) context)).
      replace (nvec_add (transfer_main_units rule W item)
          (nvec_add (transfer_plan_source rule W tail) context))
        with (nvec_add (transfer_plan_source rule W tail)
          (nvec_add (transfer_main_units rule W item) context)).
      2:{ rewrite <- !nvec_add_assoc_stateful. f_equal.
          apply nvec_add_comm_stateful. }
      replace (nvec_add (transfer_main_units rule W item)
          (nvec_add (transfer_plan_target rule W tail) context))
        with (nvec_add (transfer_plan_target rule W tail)
          (nvec_add (transfer_main_units rule W item) context)).
      * exact IH.
      * rewrite <- !nvec_add_assoc_stateful. f_equal.
        apply nvec_add_comm_stateful.
Qed.

Fixpoint coordinate_counts {dimension} (value : NVec dimension) :
    list (Fin.t dimension * nat) :=
  match value with
  | Vector.nil => []
  | Vector.cons head tail =>
      (Fin.F1, head) ::
      List.map (fun entry => (Fin.FS (fst entry), snd entry))
        (coordinate_counts tail)
  end.

Definition coordinate_count_vector {dimension}
    (entry : Fin.t dimension * nat) : NVec dimension :=
  nvec_times (snd entry)
    (one_hot_nat dimension (proj1_sig (Fin.to_nat (fst entry)))).

Lemma nvec_add_cons : forall dimension left_head right_head
    (left_tail right_tail : NVec dimension),
    nvec_add (Vector.cons left_head left_tail)
      (Vector.cons right_head right_tail) =
    Vector.cons (left_head + right_head)%nat (nvec_add left_tail right_tail).
Proof. reflexivity. Qed.

Lemma nvec_times_cons_zero : forall dimension count head
    (tail : NVec dimension),
    nvec_times count (Vector.cons head tail) =
    Vector.cons (count * head)%nat (nvec_times count tail).
Proof.
  intros dimension count. induction count as [|count IH]; intros head tail; cbn.
  - reflexivity.
  - rewrite IH. cbn. f_equal.
Qed.

Lemma nvec_times_zero : forall dimension count,
    nvec_times count (nvec_zero dimension) = nvec_zero dimension.
Proof.
  intros dimension count. induction count as [|count IH]; cbn; [reflexivity|].
  rewrite IH. apply nvec_add_zero_left_stateful.
Qed.

Lemma coordinate_count_vector_head : forall dimension count,
    coordinate_count_vector (@Fin.F1 dimension, count) =
    Vector.cons count (nvec_zero dimension).
Proof.
  intros dimension count. unfold coordinate_count_vector.
  change (nvec_times count (one_hot_nat (S dimension) 0) =
    Vector.cons count (nvec_zero dimension)).
  assert (Hone : one_hot_nat (S dimension) 0 =
      Vector.cons 1%nat (nvec_zero dimension)).
  { unfold one_hot_nat. apply (proj1 (Vector.eq_nth_iff nat (S dimension) _ _)).
    intros position position' Heq; subst position'.
    refine (Fin.caseS' position (fun selected => _) _ _).
    - repeat rewrite nth_vector_of_function. cbn. reflexivity.
    - intro tail. repeat rewrite nth_vector_of_function. cbn.
      unfold nvec_zero. rewrite const_nth.
      destruct (Fin.to_nat tail) as [tail_index Htail]. cbn. reflexivity. }
  rewrite Hone, nvec_times_cons_zero, nvec_times_zero. f_equal. lia.
Qed.

Lemma coordinate_count_vector_tail : forall dimension
    (entry : Fin.t dimension * nat),
    coordinate_count_vector (Fin.FS (fst entry), snd entry) =
    Vector.cons 0%nat (coordinate_count_vector entry).
Proof.
  intros dimension [index count]. unfold coordinate_count_vector. cbn.
  rewrite nvec_times_cons_zero. cbn. f_equal.
  - destruct (Fin.to_nat index) as [position Hposition]. cbn. lia.
  -
  f_equal.
  unfold one_hot_nat. apply (proj1 (Vector.eq_nth_iff nat dimension _ _)).
  intros position position' Heq; subst position'.
  repeat rewrite nth_vector_of_function.
  destruct (Fin.to_nat position) as [left Hleft].
  destruct (Fin.to_nat index) as [right Hright]. cbn.
  reflexivity.
Qed.

Lemma coordinate_counts_cons : forall dimension head (tail : NVec dimension),
    coordinate_counts (Vector.cons head tail) =
      (@Fin.F1 dimension, head) ::
      List.map (fun entry => (Fin.FS (fst entry), snd entry))
        (coordinate_counts tail).
Proof. reflexivity. Qed.

Local Opaque coordinate_count_vector.
Lemma shifted_coordinate_rsum : forall dimension
    (entries : list (Fin.t dimension * nat)),
    nvec_rsum_stateful
      (List.map
        (fun entry : Fin.t dimension * nat =>
          coordinate_count_vector (Fin.FS (fst entry), snd entry)) entries) =
    Vector.cons 0%nat
      (nvec_rsum_stateful (List.map coordinate_count_vector entries)).
Proof.
  intros dimension entries. induction entries as [|entry entries IH].
  - reflexivity.
  - rewrite !map_cons.
    change (nvec_add
      (coordinate_count_vector (Fin.FS (fst entry), snd entry))
      (nvec_rsum_stateful
        (List.map
          (fun item : Fin.t dimension * nat =>
            coordinate_count_vector (Fin.FS (fst item), snd item)) entries)) =
      Vector.cons 0%nat
        (nvec_add (coordinate_count_vector entry)
          (nvec_rsum_stateful (List.map coordinate_count_vector entries)))).
    rewrite coordinate_count_vector_tail, IH. reflexivity.
Qed.

Lemma shifted_coordinate_rsum_map : forall dimension
    (entries : list (Fin.t dimension * nat)),
    nvec_rsum_stateful
      (List.map coordinate_count_vector
        (List.map (fun entry => (Fin.FS (fst entry), snd entry)) entries)) =
    Vector.cons 0%nat
      (nvec_rsum_stateful (List.map coordinate_count_vector entries)).
Proof.
  intros. rewrite List.map_map. apply shifted_coordinate_rsum.
Qed.

Lemma coordinate_counts_expansion : forall dimension (value : NVec dimension),
    nvec_sum (List.map coordinate_count_vector (coordinate_counts value)) = value.
Proof.
  intros dimension value. induction value as [|head dimension tail IH].
  - reflexivity.
  - rewrite coordinate_counts_cons, map_cons.
    rewrite coordinate_count_vector_head.
    rewrite nvec_sum_rsum_stateful.
    replace
      (List.map
        (fun entry : Fin.t dimension * nat =>
          coordinate_count_vector (Fin.FS (fst entry), snd entry))
        (coordinate_counts tail))
      with
      (List.map coordinate_count_vector
        (List.map (fun entry => (Fin.FS (fst entry), snd entry))
          (coordinate_counts tail))).
    2:{ now rewrite List.map_map. }
    cbn [nvec_rsum_stateful].
    rewrite shifted_coordinate_rsum_map.
    rewrite nvec_sum_rsum_stateful in IH.
    rewrite IH, nvec_add_cons, nvec_add_zero_left_stateful. f_equal. lia.
Qed.
Local Transparent coordinate_count_vector.

Definition child_transfer_item {d q} (rule : SRule d q)
    (child : Fin.t (rule_child_count rule))
    (entry : Fin.t d * nat) : RuleTransferItem rule :=
  {| transfer_child := child;
     transfer_coordinate := fst entry;
     transfer_count := snd entry |}.

Definition child_transfer_plan {d q} (rule : SRule d q)
    (child : Fin.t (rule_child_count rule)) (visible : NVec d) :
    list (RuleTransferItem rule) :=
  List.map (child_transfer_item rule child) (coordinate_counts visible).

Definition visible_block_value {d q} (W : VASSSection d q)
    (visible : NVec d) : NVec (rule_block_width W) :=
  Vector.append visible (nvec_zero (section_aux_dimension W)).

Definition machine_main_value {d q} (rule : SRule d q)
    (W : VASSSection d q) (visible : NVec d) :
    NVec (d + rule_image_aux_dimension rule W) :=
  Vector.append visible (nvec_zero (rule_image_aux_dimension rule W)).

Lemma block_n_at_add : forall width count index
    (left right : NVec width),
    block_n_at count index (nvec_add left right) =
    nvec_add (block_n_at count index left) (block_n_at count index right).
Proof.
  intros width count index left right.
  apply (proj1 (Vector.eq_nth_iff nat (count * width) _ _)).
  intros position position' Heq; subst position'.
  unfold block_n_at, nvec_add. repeat rewrite nth_vector_of_function.
  rewrite (nth_map2 Nat.add _ _ position position position eq_refl eq_refl).
  repeat rewrite nth_vector_of_function.
  destruct (Nat.leb (index * width) (proj1_sig (Fin.to_nat position)) &&
    Nat.ltb (proj1_sig (Fin.to_nat position)) (S index * width))%bool
      eqn:Hinside; [|reflexivity].
  apply andb_true_iff in Hinside as [Hlower Hupper].
  apply Nat.leb_le in Hlower. apply Nat.ltb_lt in Hupper.
  assert (Hoffset : (proj1_sig (Fin.to_nat position) - index * width < width)%nat)
    by nia.
  rewrite <- (to_list_nth_order nat width (Vector.map2 Nat.add left right)
    (proj1_sig (Fin.to_nat position) - index * width) Hoffset 0%nat).
  rewrite <- (to_list_nth_order nat width left
    (proj1_sig (Fin.to_nat position) - index * width) Hoffset 0%nat).
  rewrite <- (to_list_nth_order nat width right
    (proj1_sig (Fin.to_nat position) - index * width) Hoffset 0%nat).
  unfold Vector.nth_order.
  rewrite (nth_map2 Nat.add _ _ (Fin.of_nat_lt Hoffset)
    (Fin.of_nat_lt Hoffset) (Fin.of_nat_lt Hoffset) eq_refl eq_refl).
  reflexivity.
Qed.

Lemma block_n_at_zero : forall width count index,
    block_n_at count index (nvec_zero width) = nvec_zero (count * width).
Proof.
  intros width count index.
  apply (proj1 (Vector.eq_nth_iff nat (count * width) _ _)).
  intros position position' Heq; subst position'.
  unfold block_n_at, nvec_zero. rewrite nth_vector_of_function, const_nth.
  destruct (Nat.leb (index * width) (proj1_sig (Fin.to_nat position)) &&
    Nat.ltb (proj1_sig (Fin.to_nat position)) (S index * width))%bool;
    [rewrite Vector.to_list_const, List.nth_repeat|]; reflexivity.
Qed.

Lemma rule_block_nvec_add : forall d q (rule : SRule d q)
    (W : VASSSection d q) child left right,
    rule_block_nvec rule W child (nvec_add left right) =
    nvec_add (rule_block_nvec rule W child left)
      (rule_block_nvec rule W child right).
Proof.
  intros. unfold rule_block_nvec. rewrite block_n_at_add.
  rewrite nvec_add_append, nvec_add_zero_left_stateful. reflexivity.
Qed.

Lemma rule_block_nvec_zero : forall d q (rule : SRule d q)
    (W : VASSSection d q) child,
    rule_block_nvec rule W child (nvec_zero (rule_block_width W)) =
    nvec_zero (d + rule_image_aux_dimension rule W).
Proof.
  intros. unfold rule_block_nvec. rewrite block_n_at_zero.
  symmetry. apply nvec_zero_append.
Qed.

Lemma transfer_plan_source_sum : forall d q (rule : SRule d q)
    (W : VASSSection d q) plan,
    transfer_plan_source rule W plan =
    nvec_sum (List.map (transfer_child_units rule W) plan).
Proof.
  intros d q rule W plan. rewrite nvec_sum_rsum_stateful.
  induction plan as [|item tail IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma transfer_plan_target_sum : forall d q (rule : SRule d q)
    (W : VASSSection d q) plan,
    transfer_plan_target rule W plan =
    nvec_sum (List.map (transfer_main_units rule W) plan).
Proof.
  intros d q rule W plan. rewrite nvec_sum_rsum_stateful.
  induction plan as [|item tail IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma rule_block_nvec_sum : forall d q (rule : SRule d q)
    (W : VASSSection d q) child values,
    rule_block_nvec rule W child (nvec_sum values) =
    nvec_sum (List.map (rule_block_nvec rule W child) values).
Proof.
  intros d q rule W child values.
  rewrite !nvec_sum_rsum_stateful. induction values as [|value values IH]; cbn.
  - apply rule_block_nvec_zero.
  - rewrite rule_block_nvec_add, IH. reflexivity.
Qed.

Lemma machine_main_value_add : forall d q (rule : SRule d q)
    (W : VASSSection d q) left right,
    machine_main_value rule W (nvec_add left right) =
    nvec_add (machine_main_value rule W left)
      (machine_main_value rule W right).
Proof.
  intros. unfold machine_main_value. rewrite nvec_add_append,
    nvec_add_zero_left_stateful. reflexivity.
Qed.

Lemma machine_main_value_zero : forall d q (rule : SRule d q)
    (W : VASSSection d q),
    machine_main_value rule W (nvec_zero d) =
    nvec_zero (d + rule_image_aux_dimension rule W).
Proof.
  intros. unfold machine_main_value. symmetry. apply nvec_zero_append.
Qed.

Local Opaque machine_main_value.
Lemma machine_main_value_sum : forall d q (rule : SRule d q)
    (W : VASSSection d q) values,
    machine_main_value rule W (nvec_sum values) =
    nvec_sum (List.map (machine_main_value rule W) values).
Proof.
  intros. rewrite !nvec_sum_rsum_stateful.
  induction values as [|value values IH]; cbn.
  - apply machine_main_value_zero.
  - rewrite machine_main_value_add, IH. reflexivity.
Qed.
Local Transparent machine_main_value.

Lemma one_hot_append_zero_right : forall left right (index : Fin.t left),
    Vector.append
      (one_hot_nat left (proj1_sig (Fin.to_nat index))) (nvec_zero right) =
    one_hot_nat (left + right) (proj1_sig (Fin.to_nat index)).
Proof.
  intros left right index.
  apply (proj1 (Vector.eq_nth_iff nat (left + right) _ _)).
  intros position position' Heq; subst position'.
  refine (@Fin.case_L_R' left right
    (fun selected =>
      Vector.nth
        (Vector.append
          (one_hot_nat left (proj1_sig (Fin.to_nat index)))
          (nvec_zero right)) selected =
      Vector.nth
        (one_hot_nat (left + right) (proj1_sig (Fin.to_nat index))) selected)
    position _ _).
  - intro selected. rewrite VectorSpec.nth_append_L.
    unfold one_hot_nat. repeat rewrite nth_vector_of_function.
    rewrite Fin.L_sanity. reflexivity.
  - intro selected. rewrite VectorSpec.nth_append_R.
    unfold one_hot_nat, nvec_zero. rewrite const_nth, nth_vector_of_function.
    pose proof (proj2_sig (Fin.to_nat index)) as Hindex.
    rewrite Fin.R_sanity.
    destruct (Fin.to_nat selected) as [selected_nat Hselected]. cbn.
    cbn in Hindex.
    assert ((left + selected_nat <> proj1_sig (Fin.to_nat index))%nat) by lia.
    apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma one_hot_append_zero_left : forall left right (index : Fin.t right),
    Vector.append (nvec_zero left)
      (one_hot_nat right (proj1_sig (Fin.to_nat index))) =
    one_hot_nat (left + right) (left + proj1_sig (Fin.to_nat index)).
Proof.
  intros left right index.
  apply (proj1 (Vector.eq_nth_iff nat (left + right) _ _)).
  intros position position' Heq; subst position'.
  refine (@Fin.case_L_R' left right
    (fun selected =>
      Vector.nth
        (Vector.append (nvec_zero left)
          (one_hot_nat right (proj1_sig (Fin.to_nat index)))) selected =
      Vector.nth
        (one_hot_nat (left + right)
          (left + proj1_sig (Fin.to_nat index))) selected)
    position _ _).
  - intro selected. rewrite VectorSpec.nth_append_L.
    unfold one_hot_nat, nvec_zero. rewrite const_nth, nth_vector_of_function.
    pose proof (proj2_sig (Fin.to_nat selected)) as Hselected.
    rewrite Fin.L_sanity.
    destruct (Fin.to_nat selected) as [selected_nat Hselected']. cbn.
    assert ((selected_nat <> left + proj1_sig (Fin.to_nat index))%nat) by lia.
    apply Nat.eqb_neq in H. now rewrite H.
  - intro selected. rewrite VectorSpec.nth_append_R.
    unfold one_hot_nat. repeat rewrite nth_vector_of_function.
    rewrite Fin.R_sanity.
    destruct (Fin.to_nat selected) as [selected_nat Hselected].
    destruct (Fin.to_nat index) as [index_nat Hindex]. cbn.
    destruct (selected_nat =? index_nat)%nat eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. now rewrite Nat.eqb_refl.
    + apply Nat.eqb_neq in Heq.
      assert ((left + selected_nat <> left + index_nat)%nat) by lia.
      apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma one_hot_append_zero_left_nat : forall left right index,
    (index < right)%nat ->
    Vector.append (nvec_zero left) (one_hot_nat right index) =
    one_hot_nat (left + right) (left + index).
Proof.
  intros left right index Hindex.
  pose proof (one_hot_append_zero_left left right (Fin.of_nat_lt Hindex)) as H.
  rewrite !Fin.to_nat_of_nat in H. exact H.
Qed.

Lemma one_hot_append_zero_right_nat : forall left right index,
    (index < left)%nat ->
    Vector.append (one_hot_nat left index) (nvec_zero right) =
    one_hot_nat (left + right) index.
Proof.
  intros left right index Hindex.
  pose proof (one_hot_append_zero_right left right (Fin.of_nat_lt Hindex)) as H.
  rewrite !Fin.to_nat_of_nat in H. exact H.
Qed.

Lemma nvec_times_append : forall left right count
    (left_value : NVec left) (right_value : NVec right),
    nvec_times count (Vector.append left_value right_value) =
    Vector.append (nvec_times count left_value)
      (nvec_times count right_value).
Proof.
  intros left right count. induction count as [|count IH];
    intros left_value right_value; cbn.
  - apply nvec_zero_append.
  - rewrite IH, nvec_add_append. reflexivity.
Qed.

Lemma visible_block_coordinate_count : forall d q (W : VASSSection d q)
    (entry : Fin.t d * nat),
    visible_block_value W (coordinate_count_vector entry) =
    nvec_times (snd entry)
      (one_hot_nat (rule_block_width W)
        (proj1_sig (Fin.to_nat (fst entry)))).
Proof.
  intros d q W [coordinate count].
  unfold visible_block_value, coordinate_count_vector.
  change (Vector.append
    (nvec_times count
      (one_hot_nat d (proj1_sig (Fin.to_nat coordinate))))
    (nvec_zero (section_aux_dimension W)) =
    nvec_times count
      (one_hot_nat (rule_block_width W)
        (proj1_sig (Fin.to_nat coordinate)))).
  rewrite <- (nvec_times_zero (section_aux_dimension W) count).
  rewrite <- nvec_times_append.
  f_equal. apply one_hot_append_zero_right.
Qed.

Lemma block_n_at_one_hot : forall width count
    (block : Fin.t count) (coordinate : Fin.t width),
    block_n_at count (proj1_sig (Fin.to_nat block))
      (one_hot_nat width (proj1_sig (Fin.to_nat coordinate))) =
    one_hot_nat (count * width)
      (proj1_sig (Fin.to_nat block) * width +
        proj1_sig (Fin.to_nat coordinate)).
Proof.
  intros width count block coordinate.
  apply (proj1 (Vector.eq_nth_iff nat (count * width) _ _)).
  intros position position' Heq; subst position'.
  unfold block_n_at. rewrite nth_vector_of_function.
  set (block_index := proj1_sig (Fin.to_nat block)).
  set (coordinate_index := proj1_sig (Fin.to_nat coordinate)).
  set (position_index := proj1_sig (Fin.to_nat position)).
  destruct (Nat.leb (block_index * width) position_index &&
    Nat.ltb position_index (S block_index * width))%bool eqn:Hinside.
  - apply andb_true_iff in Hinside as [Hlower Hupper].
    apply Nat.leb_le in Hlower. apply Nat.ltb_lt in Hupper.
    assert (Hoffset : (position_index - block_index * width < width)%nat)
      by nia.
    rewrite <- (to_list_nth_order nat width
      (one_hot_nat width coordinate_index)
      (position_index - block_index * width) Hoffset 0%nat).
    unfold Vector.nth_order, one_hot_nat. repeat rewrite nth_vector_of_function.
    rewrite Fin.to_nat_of_nat. cbn.
    fold position_index block_index coordinate_index.
    destruct (position_index - block_index * width =? coordinate_index)%nat
      eqn:Heqoffset.
    + apply Nat.eqb_eq in Heqoffset.
      assert (Hposition : position_index =
        (block_index * width + coordinate_index)%nat) by nia.
      assert (Hglobal : (position_index =?
        block_index * width + coordinate_index)%nat = true).
      { apply Nat.eqb_eq. exact Hposition. }
      rewrite Hglobal. reflexivity.
    + apply Nat.eqb_neq in Heqoffset.
      assert (Hposition : position_index <>
        (block_index * width + coordinate_index)%nat) by nia.
      apply Nat.eqb_neq in Hposition. rewrite Hposition. reflexivity.
  - apply andb_false_iff in Hinside.
    unfold one_hot_nat. rewrite nth_vector_of_function.
    fold position_index block_index coordinate_index.
    assert (Hblock : (block_index < count)%nat).
    { unfold block_index. exact (proj2_sig (Fin.to_nat block)). }
    assert (Hcoordinate : (coordinate_index < width)%nat).
    { unfold coordinate_index. exact (proj2_sig (Fin.to_nat coordinate)). }
    assert (position_index <> block_index * width + coordinate_index)%nat.
    { intro Heqposition. subst position_index. destruct Hinside as [Hlow|Hhigh].
      - apply Nat.leb_gt in Hlow. nia.
      - apply Nat.ltb_ge in Hhigh. nia. }
    apply Nat.eqb_neq in H. now rewrite H.
Qed.

Lemma block_n_at_times : forall width count block multiplier
    (value : NVec width),
    block_n_at count block (nvec_times multiplier value) =
    nvec_times multiplier (block_n_at count block value).
Proof.
  intros width count block multiplier value.
  induction multiplier as [|multiplier IH]; cbn.
  - apply block_n_at_zero.
  - rewrite block_n_at_add, IH. reflexivity.
Qed.

Lemma transfer_child_units_item : forall d q (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule))
    (entry : Fin.t d * nat),
    transfer_child_units rule W (child_transfer_item rule child entry) =
    rule_block_nvec rule W (proj1_sig (Fin.to_nat child))
      (visible_block_value W (coordinate_count_vector entry)).
Proof.
  intros d q rule W child [coordinate count].
  change (nvec_times count
    (one_hot_nat (d + rule_image_aux_dimension rule W)
      (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
        proj1_sig (Fin.to_nat coordinate))) =
    rule_block_nvec rule W (proj1_sig (Fin.to_nat child))
      (visible_block_value W
        (coordinate_count_vector (coordinate, count)))).
  rewrite visible_block_coordinate_count.
  unfold rule_block_nvec. rewrite block_n_at_times.
  change (nvec_times count
    (one_hot_nat (d + rule_image_aux_dimension rule W)
      (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
        proj1_sig (Fin.to_nat coordinate))) =
    Vector.append (nvec_zero d)
      (nvec_times count
        (block_n_at (rule_child_count rule)
          (proj1_sig (Fin.to_nat child))
          (one_hot_nat (rule_block_width W)
            (proj1_sig (Fin.to_nat coordinate)))))).
  set (block_coordinate := Fin.L (section_aux_dimension W) coordinate).
  assert (Hblock_coordinate : proj1_sig (Fin.to_nat block_coordinate) =
      proj1_sig (Fin.to_nat coordinate)).
  { unfold block_coordinate. apply Fin.L_sanity. }
  pose proof (block_n_at_one_hot (rule_block_width W)
    (rule_child_count rule) child block_coordinate) as Hblock.
  subst block_coordinate.
  setoid_rewrite (Fin.L_sanity (section_aux_dimension W) coordinate) in Hblock.
  rewrite Hblock.
  rewrite <- (nvec_times_zero d count).
  rewrite <- nvec_times_append.
  f_equal. symmetry. rewrite <- Nat.add_assoc.
  apply one_hot_append_zero_left_nat.
  pose proof (proj2_sig (Fin.to_nat child)) as Hchild.
  pose proof (proj2_sig (Fin.to_nat coordinate)) as Hcoordinate.
  cbn in Hchild, Hcoordinate.
  eapply Nat.lt_le_trans with
    (m := (S (proj1_sig (Fin.to_nat child)) * rule_block_width W)%nat).
  - rewrite Nat.mul_succ_l. apply Nat.add_lt_mono_l.
    unfold rule_block_width. lia.
  - apply Nat.mul_le_mono_r. lia.
Qed.

Lemma transfer_main_units_item : forall d q (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule))
    (entry : Fin.t d * nat),
    transfer_main_units rule W (child_transfer_item rule child entry) =
    machine_main_value rule W (coordinate_count_vector entry).
Proof.
  intros d q rule W child [coordinate count].
  change (nvec_times count
    (one_hot_nat (d + rule_image_aux_dimension rule W)
      (proj1_sig (Fin.to_nat coordinate))) =
    machine_main_value rule W
      (coordinate_count_vector (coordinate, count))).
  unfold machine_main_value, coordinate_count_vector.
  change (nvec_times count
    (one_hot_nat (d + rule_image_aux_dimension rule W)
      (proj1_sig (Fin.to_nat coordinate))) =
    Vector.append
      (nvec_times count
        (one_hot_nat d (proj1_sig (Fin.to_nat coordinate))))
      (nvec_zero (rule_image_aux_dimension rule W))).
  rewrite <- (nvec_times_zero (rule_image_aux_dimension rule W) count).
  rewrite <- nvec_times_append.
  f_equal. symmetry. apply one_hot_append_zero_right.
Qed.

Lemma visible_block_value_add : forall d q (W : VASSSection d q) left right,
    visible_block_value W (nvec_add left right) =
    nvec_add (visible_block_value W left) (visible_block_value W right).
Proof.
  intros. unfold visible_block_value.
  symmetry. etransitivity.
  - apply nvec_add_append.
  - f_equal. apply nvec_add_zero_left_stateful.
Qed.

Lemma visible_block_value_zero : forall d q (W : VASSSection d q),
    visible_block_value W (nvec_zero d) = nvec_zero (rule_block_width W).
Proof.
  intros. unfold visible_block_value, rule_block_width.
  symmetry. apply nvec_zero_append.
Qed.

Local Opaque visible_block_value.
Lemma visible_block_value_sum : forall d q (W : VASSSection d q) values,
    visible_block_value W (nvec_sum values) =
    nvec_sum (List.map (visible_block_value W) values).
Proof.
  intros. rewrite !nvec_sum_rsum_stateful.
  induction values as [|value values IH]; cbn.
  - apply visible_block_value_zero.
  - rewrite visible_block_value_add, IH. reflexivity.
Qed.
Local Transparent visible_block_value.

Lemma child_transfer_plan_source : forall d q (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule)) visible,
    transfer_plan_source rule W (child_transfer_plan rule child visible) =
    rule_block_nvec rule W (proj1_sig (Fin.to_nat child))
      (visible_block_value W visible).
Proof.
  intros d q rule W child visible.
  rewrite transfer_plan_source_sum. unfold child_transfer_plan.
  rewrite List.map_map.
  assert (Hmap : List.map
      (fun entry => transfer_child_units rule W
        (child_transfer_item rule child entry))
      (coordinate_counts visible) =
    List.map
      (fun entry => rule_block_nvec rule W (proj1_sig (Fin.to_nat child))
        (visible_block_value W (coordinate_count_vector entry)))
      (coordinate_counts visible)).
  { apply List.map_ext. intro entry. apply transfer_child_units_item. }
  rewrite Hmap, <- List.map_map, <- rule_block_nvec_sum.
  f_equal.
  rewrite <- (coordinate_counts_expansion d visible) at 2.
  rewrite visible_block_value_sum, List.map_map. reflexivity.
Qed.

Lemma child_transfer_plan_target : forall d q (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule)) visible,
    transfer_plan_target rule W (child_transfer_plan rule child visible) =
    machine_main_value rule W visible.
Proof.
  intros d q rule W child visible.
  rewrite transfer_plan_target_sum. unfold child_transfer_plan.
  rewrite List.map_map.
  assert (Hmap : List.map
      (fun entry => transfer_main_units rule W
        (child_transfer_item rule child entry))
      (coordinate_counts visible) =
    List.map
      (fun entry => machine_main_value rule W (coordinate_count_vector entry))
      (coordinate_counts visible)).
  { apply List.map_ext. intro entry. apply transfer_main_units_item. }
  rewrite Hmap, <- List.map_map.
  rewrite <- (coordinate_counts_expansion d visible) at 2.
  rewrite machine_main_value_sum, List.map_map. reflexivity.
Qed.

Definition OrderedRuleImage {d q} (rule : SRule d q)
    (relation : Fin.t q -> NVec d -> Prop)
    (state : Fin.t q) (counters : NVec d) : Prop :=
  exists children : list (Mell.BVASS.Stateful.SConfig d q),
    List.Forall (fun child => relation (fst child) (snd child)) children /\
    List.map fst children = input_states rule /\
    add_displacement (rule_delta rule) (List.map snd children) = Some counters /\
    state = output_state rule.

Lemma rule_image_ordered : forall d q (B : SBVAS d q) rule relation state counters,
    RuleImage B rule relation state counters ->
    List.In rule (stateful_rules B) /\
    (2 <= List.length (input_states rule))%nat /\
    OrderedRuleImage rule relation state counters.
Proof.
  intros d q B rule relation state counters
    [Hrule [Harity [children [Hchildren [Hstates [Happly Hstate]]]]]].
  pose proof (Permutation_sym Hstates) as Hstates_sym.
  destruct (@Permutation_map_inv _ _ fst _ _ Hstates_sym)
    as [ordered [Hordered Hperm]].
  split; [exact Hrule|]. split; [exact Harity|].
  exists ordered. repeat split.
  - eapply Permutation_Forall; [exact Hperm|exact Hchildren].
  - symmetry. exact Hordered.
  - rewrite <- Happly. apply add_displacement_permutation.
    now apply Permutation_map.
  - exact Hstate.
Qed.

Lemma ordered_rule_image : forall d q (B : SBVAS d q) rule relation state counters,
    List.In rule (stateful_rules B) ->
    (2 <= List.length (input_states rule))%nat ->
    OrderedRuleImage rule relation state counters ->
    RuleImage B rule relation state counters.
Proof.
  intros d q B rule relation state counters Hrule Harity
    [children [Hchildren [Hstates [Happly Hstate]]]].
  repeat split; try assumption.
  exists children. repeat split; try assumption.
  rewrite Hstates. apply Permutation_refl.
Qed.

(** Proof data for one sequential child copy.  The index is an occurrence:
    equal states and equal counters at two rule inputs remain distinct. *)
Record RuleChildExecution {d q} (rule : SRule d q)
    (W : VASSSection d q) := {
  child_execution_index : Fin.t (rule_child_count rule);
  child_execution_visible : NVec d;
  child_execution_initial_state : Fin.t (section_state_count W);
  child_execution_initial_counters : NVec (rule_block_width W);
  child_execution_initial_in :
    List.In (child_execution_initial_state, child_execution_initial_counters)
      (section_initial_configs W);
  child_execution_reach :
    DirectVASReach (section_system W)
      child_execution_initial_state child_execution_initial_counters
      (section_accept_state W
        (rule_required_state rule child_execution_index))
      (section_target_vector W child_execution_visible)
}.

Definition child_execution_block {d q} {rule : SRule d q}
    {W : VASSSection d q} (execution : RuleChildExecution rule W) :=
  rule_block_nvec rule W
    (proj1_sig (Fin.to_nat (child_execution_index rule W execution)))
    (section_target_vector W (child_execution_visible rule W execution)).

Definition child_execution_transfer_plan {d q} {rule : SRule d q}
    {W : VASSSection d q} (execution : RuleChildExecution rule W) :=
  child_transfer_plan rule (child_execution_index rule W execution)
    (child_execution_visible rule W execution).

Definition children_transfer_plan {d q} {rule : SRule d q}
    {W : VASSSection d q} (executions : list (RuleChildExecution rule W)) :=
  List.flat_map child_execution_transfer_plan executions.

Lemma transfer_plan_source_app : forall d q (rule : SRule d q)
    (W : VASSSection d q) left right,
    transfer_plan_source rule W (left ++ right) =
    nvec_add (transfer_plan_source rule W left)
      (transfer_plan_source rule W right).
Proof.
  intros d q rule W left. induction left as [|item tail IH]; intro right; cbn.
  - symmetry. apply nvec_add_zero_left_stateful.
  - rewrite IH, nvec_add_assoc_stateful. reflexivity.
Qed.

Lemma transfer_plan_target_app : forall d q (rule : SRule d q)
    (W : VASSSection d q) left right,
    transfer_plan_target rule W (left ++ right) =
    nvec_add (transfer_plan_target rule W left)
      (transfer_plan_target rule W right).
Proof.
  intros d q rule W left. induction left as [|item tail IH]; intro right; cbn.
  - symmetry. apply nvec_add_zero_left_stateful.
  - rewrite IH, nvec_add_assoc_stateful. reflexivity.
Qed.

Lemma children_transfer_plan_source : forall d q (rule : SRule d q)
    (W : VASSSection d q) executions,
    transfer_plan_source rule W (children_transfer_plan executions) =
    nvec_sum (List.map child_execution_block executions).
Proof.
  intros d q rule W executions. induction executions as [|execution tail IH].
  - reflexivity.
  - change (transfer_plan_source rule W
      (child_execution_transfer_plan execution ++ children_transfer_plan tail) =
      nvec_sum (child_execution_block execution ::
        List.map child_execution_block tail)).
    rewrite transfer_plan_source_app.
    unfold child_execution_transfer_plan, child_execution_block at 1.
    rewrite child_transfer_plan_source, IH.
    unfold visible_block_value, section_target_vector.
    rewrite !nvec_sum_rsum_stateful. reflexivity.
Qed.

Lemma children_transfer_plan_target : forall d q (rule : SRule d q)
    (W : VASSSection d q) executions,
    transfer_plan_target rule W (children_transfer_plan executions) =
    machine_main_value rule W
      (nvec_sum (List.map
        (fun execution => child_execution_visible rule W execution)
        executions)).
Proof.
  intros d q rule W executions. induction executions as [|execution tail IH].
  - symmetry. apply machine_main_value_zero.
  - change (transfer_plan_target rule W
      (child_execution_transfer_plan execution ++ children_transfer_plan tail) =
      machine_main_value rule W
        (nvec_sum (child_execution_visible rule W execution ::
          List.map (fun item => child_execution_visible rule W item) tail))).
    rewrite transfer_plan_target_app.
    unfold child_execution_transfer_plan at 1.
    rewrite child_transfer_plan_target, IH.
    rewrite !nvec_sum_rsum_stateful. cbn [nvec_rsum_stateful].
    rewrite machine_main_value_add. reflexivity.
Qed.

Inductive ConsecutiveChildExecutions {d q} {rule : SRule d q}
    {W : VASSSection d q} : list (RuleChildExecution rule W) -> Prop :=
| consecutive_child_last : forall execution,
    fin_successor (child_execution_index rule W execution) = None ->
    ConsecutiveChildExecutions [execution]
| consecutive_child_cons : forall first second tail,
    fin_successor (child_execution_index rule W first) =
      Some (child_execution_index rule W second) ->
    ConsecutiveChildExecutions (second :: tail) ->
    ConsecutiveChildExecutions (first :: second :: tail).

Lemma execute_consecutive_children : forall d q (rule : SRule d q)
    (W : VASSSection d q) first tail,
    ConsecutiveChildExecutions (first :: tail) ->
    forall context,
    DirectVASReach (rule_image_system rule W)
      (rule_copy_state rule W (child_execution_index rule W first)
        (child_execution_initial_state rule W first))
      (nvec_add
        (rule_block_nvec rule W
          (proj1_sig (Fin.to_nat (child_execution_index rule W first)))
          (child_execution_initial_counters rule W first)) context)
      (rule_collect_state rule W)
      (nvec_add
        (nvec_sum (List.map child_execution_block (first :: tail))) context).
Proof.
  intros d q rule W first tail Hconsecutive.
  remember (first :: tail) as executions eqn:Hexecutions.
  revert first tail Hexecutions.
  induction Hconsecutive as [execution Hlast|head second rest Hnext Hrest IH];
    intros first tail Heq; inversion Heq; subst; clear Heq; intro context.
  - rewrite nvec_sum_rsum_stateful. cbn [List.map nvec_rsum_stateful].
    rewrite nvec_add_zero.
    eapply direct_vas_reach_trans.
    + apply rule_copy_direct_reach. apply child_execution_reach.
    + unfold child_execution_block.
      apply rule_advance_to_collect_reach. exact Hlast.
  - eapply direct_vas_reach_trans.
    + apply rule_copy_direct_reach. apply child_execution_reach.
    + eapply direct_vas_reach_trans.
      * apply rule_advance_to_initial_reach; [exact Hnext|].
        apply child_execution_initial_in.
      * specialize (IH second rest eq_refl
          (nvec_add (child_execution_block first) context)).
        unfold child_execution_block at 1 in IH.
        replace (nvec_add
            (nvec_sum (List.map child_execution_block (first :: second :: rest)))
            context)
          with (nvec_add
            (nvec_sum (List.map child_execution_block (second :: rest)))
            (nvec_add (child_execution_block first) context)).
        -- exact IH.
        -- rewrite !nvec_sum_rsum_stateful.
           cbn [List.map nvec_rsum_stateful].
           apply (proj1 (Vector.eq_nth_iff nat
             (d + rule_image_aux_dimension rule W) _ _)).
           intros index index' Heq; subst index'. unfold nvec_add.
           repeat rewrite (nth_map2 Nat.add _ _
             index index index eq_refl eq_refl). lia.
Qed.

Inductive ConsecutiveFin {count} : list (Fin.t count) -> Prop :=
| consecutive_fin_last : forall index,
    fin_successor index = None -> ConsecutiveFin [index]
| consecutive_fin_cons : forall first second tail,
    fin_successor first = Some second ->
    ConsecutiveFin (second :: tail) ->
    ConsecutiveFin (first :: second :: tail).

Lemma fin_successor_F1_last : fin_successor (@Fin.F1 0) = None.
Proof.
  unfold fin_successor. destruct (lt_dec 1 1); [lia|reflexivity].
Qed.

Lemma fin_successor_F1_next : forall count,
    fin_successor (@Fin.F1 (S count)) = Some (Fin.FS (@Fin.F1 count)).
Proof.
  intro count. unfold fin_successor. destruct (lt_dec 1 (S (S count))) as [H|H].
  - cbn. f_equal.
  - lia.
Qed.

Lemma fin_successor_some_value : forall count (index next : Fin.t count),
    fin_successor index = Some next ->
    proj1_sig (Fin.to_nat next) = S (proj1_sig (Fin.to_nat index)).
Proof.
  intros count index next Hsuccessor. unfold fin_successor in Hsuccessor.
  destruct (lt_dec (S (proj1_sig (Fin.to_nat index))) count) as [Hlt|Hlt];
    [|discriminate].
  injection Hsuccessor as Heq. subst next.
  destruct count as [|count]; [lia|]. cbn. rewrite Fin.to_nat_of_nat.
  reflexivity.
Qed.

Lemma fin_successor_none_value : forall count (index : Fin.t count),
    fin_successor index = None ->
    ~ (S (proj1_sig (Fin.to_nat index)) < count)%nat.
Proof.
  intros count index Hsuccessor Hlt.
  assert (Hexists : exists next, fin_successor index = Some next).
  { unfold fin_successor.
    destruct (lt_dec (S (proj1_sig (Fin.to_nat index))) count) as [H|H].
    - eexists. reflexivity.
    - lia. }
  destruct Hexists as [next Hnext]. rewrite Hsuccessor in Hnext. discriminate.
Qed.

Lemma fin_successor_exists : forall count (index : Fin.t count),
    (S (proj1_sig (Fin.to_nat index)) < count)%nat ->
    exists next, fin_successor index = Some next.
Proof.
  intros count index Hlt. unfold fin_successor.
  destruct (lt_dec (S (proj1_sig (Fin.to_nat index))) count) as [H|H].
  - eexists. reflexivity.
  - lia.
Qed.

Lemma fin_to_nat_FS_value : forall count (index : Fin.t count),
    proj1_sig (Fin.to_nat (Fin.FS index)) =
    S (proj1_sig (Fin.to_nat index)).
Proof.
  intros count index. cbn. destruct (Fin.to_nat index). reflexivity.
Qed.

Lemma fin_successor_FS : forall count (index : Fin.t count),
    fin_successor (Fin.FS index) =
    option_map Fin.FS (fin_successor index).
Proof.
  intros count index. destruct (fin_successor index) as [next|] eqn:Hsuccessor.
  - pose proof (fin_successor_some_value count index next Hsuccessor) as Hvalue.
    assert (Hlt : (S (proj1_sig (Fin.to_nat (Fin.FS index))) < S count)%nat).
    { rewrite fin_to_nat_FS_value, <- Hvalue.
      apply (proj1 (Nat.succ_lt_mono _ _)).
      exact (proj2_sig (Fin.to_nat next)). }
    destruct (fin_successor_exists (S count) (Fin.FS index) Hlt)
      as [next' Hnext'].
    rewrite Hnext'. cbn. f_equal. apply Fin.to_nat_inj.
    pose proof (fin_successor_some_value (S count) (Fin.FS index) next' Hnext').
    rewrite fin_to_nat_FS_value in H. rewrite fin_to_nat_FS_value.
    rewrite H, Hvalue. reflexivity.
  - pose proof (fin_successor_none_value count index Hsuccessor) as Hlast.
    destruct (fin_successor (Fin.FS index)) as [next'|] eqn:Hnext'; [|reflexivity].
    pose proof (fin_successor_some_value (S count) (Fin.FS index) next' Hnext').
    rewrite fin_to_nat_FS_value in H.
    exfalso. apply Hlast. apply (proj2 (Nat.succ_lt_mono _ _)).
    rewrite <- H. exact (proj2_sig (Fin.to_nat next')).
Qed.

Lemma consecutive_fin_map_FS : forall count (indices : list (Fin.t count)),
    ConsecutiveFin indices -> ConsecutiveFin (List.map Fin.FS indices).
Proof.
  intros count indices H. induction H.
  - cbn. constructor. rewrite fin_successor_FS, H. reflexivity.
  - cbn. constructor.
    + rewrite fin_successor_FS, H. reflexivity.
    + exact IHConsecutiveFin.
Qed.

Lemma all_fin_consecutive : forall count,
    ConsecutiveFin (all_fin (S count)).
Proof.
  induction count as [|count IH].
  - cbn. constructor. apply fin_successor_F1_last.
  - cbn. constructor.
    + apply fin_successor_F1_next.
    + change (ConsecutiveFin (List.map Fin.FS (all_fin (S count)))).
      apply consecutive_fin_map_FS. exact IH.
Qed.

Lemma all_fin_consecutive_nonempty : forall count : nat,
    count <> O -> ConsecutiveFin (all_fin count).
Proof.
  intros [|count] Hnonzero; [contradiction|]. apply all_fin_consecutive.
Qed.

Lemma consecutive_executions_of_indices : forall d q (rule : SRule d q)
    (W : VASSSection d q) executions indices,
    List.map (fun execution => child_execution_index rule W execution)
      executions = indices ->
    ConsecutiveFin indices ->
    ConsecutiveChildExecutions executions.
Proof.
  intros d q rule W executions indices Hindices Hconsecutive.
  revert executions Hindices. induction Hconsecutive;
    intros executions Hindices; destruct executions as [|execution executions];
    cbn in Hindices; try discriminate.
  - destruct executions; [|discriminate]. injection Hindices as Hindex. subst.
    constructor. exact H.
  - destruct executions as [|next executions]; [discriminate|].
    inversion Hindices; subst. constructor; [exact H|].
    apply IHHconsecutive. reflexivity.
Qed.

Lemma all_fin_nonempty_first : forall count,
    all_fin (S count) = @Fin.F1 count :: List.map Fin.FS (all_fin count).
Proof. reflexivity. Qed.

Lemma all_fin_vector_nth : forall A (values : list A),
    List.map (Vector.nth (Vector.of_list values))
      (all_fin (List.length values)) = values.
Proof.
  intros A values. induction values as [|value tail IH]; cbn.
  - reflexivity.
  - f_equal. rewrite List.map_map.
    change (List.map (Vector.nth (Vector.of_list tail))
      (all_fin (List.length tail)) = tail).
    exact IH.
Qed.

Lemma rule_required_states_all_fin : forall d q (rule : SRule d q),
    List.map (rule_required_state rule) (all_fin (rule_child_count rule)) =
    input_states rule.
Proof.
  intros. unfold rule_required_state, rule_child_count.
  apply all_fin_vector_nth.
Qed.

Lemma child_executions_from_aligned : forall d q (rule : SRule d q)
    (W : VASSSection d q) children indices,
    List.Forall
      (fun child => VASSSectionReach W (fst child) (snd child)) children ->
    List.map fst children = List.map (rule_required_state rule) indices ->
    exists executions : list (RuleChildExecution rule W),
      List.map (fun execution => child_execution_index rule W execution)
        executions = indices /\
      List.map (fun execution => child_execution_visible rule W execution)
        executions = List.map snd children.
Proof.
  intros d q rule W children. induction children as [|child tail IH];
    intros indices Hchildren Hstates.
  - destruct indices; [|discriminate]. exists []. auto.
  - destruct indices as [|index indices]; [discriminate|].
    inversion Hchildren as [|? ? Hchild Htail]; subst.
    cbn in Hstates. injection Hstates as Hstate Hstates.
    destruct Hchild as [initial_state [initial_counters [Hinitial Hreach]]].
    apply vas_reach_direct_iff in Hreach.
    assert (Hrequired : DirectVASReach (section_system W)
        initial_state initial_counters
        (section_accept_state W (rule_required_state rule index))
        (section_target_vector W (snd child))).
    { rewrite <- Hstate. exact Hreach. }
    pose (Hexecution :=
      ({| child_execution_index := index;
         child_execution_visible := snd child;
         child_execution_initial_state := initial_state;
         child_execution_initial_counters := initial_counters;
         child_execution_initial_in := Hinitial;
         child_execution_reach := Hrequired |} : RuleChildExecution rule W)).
    destruct (IH indices Htail Hstates) as [executions [Hindices Hvisible]].
    exists (Hexecution :: executions). split.
    + unfold Hexecution. cbn. now rewrite Hindices.
    + unfold Hexecution. cbn. now rewrite Hvisible.
Qed.

Lemma child_executions_of_ordered : forall d q (rule : SRule d q)
    (W : VASSSection d q) children,
    List.Forall
      (fun child => VASSSectionReach W (fst child) (snd child)) children ->
    List.map fst children = input_states rule ->
    exists executions : list (RuleChildExecution rule W),
      List.map (fun execution => child_execution_index rule W execution)
        executions = all_fin (rule_child_count rule) /\
      List.map (fun execution => child_execution_visible rule W execution)
        executions = List.map snd children /\
      ConsecutiveChildExecutions executions.
Proof.
  intros d q rule W children Hchildren Hstates.
  rewrite <- rule_required_states_all_fin in Hstates.
  destruct (child_executions_from_aligned d q rule W children
    (all_fin (rule_child_count rule)) Hchildren Hstates)
    as [executions [Hindices Hvisible]].
  exists executions. split; [exact Hindices|]. split; [exact Hvisible|].
  eapply consecutive_executions_of_indices; [exact Hindices|].
  apply all_fin_consecutive_nonempty. unfold rule_child_count.
  intro Hlength. apply List.length_zero_iff_nil in Hlength.
  exact (input_nonempty rule Hlength).
Qed.

Lemma all_fin_head_value : forall count (index : Fin.t count),
    proj1_sig (Fin.to_nat index) = 0%nat ->
    List.hd_error (all_fin count) = Some index.
Proof.
  intros [|count] index Hvalue.
  - exact (Fin.case0 (fun index => List.hd_error (all_fin 0) = Some index)
      index).
  - cbn. f_equal. apply Fin.to_nat_inj. cbn. symmetry. exact Hvalue.
Qed.

Lemma first_child_value : forall d q (rule : SRule d q),
    proj1_sig (Fin.to_nat (first_child rule)) = 0%nat.
Proof.
  intros. unfold first_child. rewrite Fin.to_nat_of_nat. reflexivity.
Qed.

Lemma all_fin_head_first_child : forall d q (rule : SRule d q),
    List.hd_error (all_fin (rule_child_count rule)) = Some (first_child rule).
Proof.
  intros. apply all_fin_head_value. apply first_child_value.
Qed.

Lemma executions_first_child : forall d q (rule : SRule d q)
    (W : VASSSection d q) executions,
    List.map (fun execution => child_execution_index rule W execution)
      executions = all_fin (rule_child_count rule) ->
    exists first tail,
      executions = first :: tail /\
      child_execution_index rule W first = first_child rule.
Proof.
  intros d q rule W executions Hindices.
  destruct executions as [|first tail].
  - pose proof (f_equal (@List.hd_error _) Hindices) as Hhead.
    cbn in Hhead. rewrite all_fin_head_first_child in Hhead. discriminate.
  - exists first, tail. split; [reflexivity|].
    pose proof (f_equal (@List.hd_error _) Hindices) as Hhead.
    cbn in Hhead. rewrite all_fin_head_first_child in Hhead.
    now injection Hhead.
Qed.

Lemma rule_final_reach : forall d q (rule : SRule d q)
    (W : VASSSection d q) visibles target,
    add_displacement (rule_delta rule) visibles = Some target ->
    DirectVASReach (rule_image_system rule W)
      (rule_collect_state rule W)
      (machine_main_value rule W (nvec_sum visibles))
      (rule_output_state rule W (output_state rule))
      (section_target_vector (compile_rule_image rule W) target).
Proof.
  intros d q rule W visibles target Happly.
  eapply direct_vas_reach_step with
      (transition := rule_final_transition rule W)
      (target := section_target_vector (compile_rule_image rule W) target).
  - apply rule_final_transition_in.
  - assert (Hdelta : rule_delta rule =
        StepAction (nvec_sum visibles) target).
    { unfold add_displacement in Happly.
      apply (proj1 (Vector.eq_nth_iff Z d _ _)).
      intros index index' Heq; subst index'.
      pose proof (zvec_to_nvec_sound d _ _ Happly index) as Hsound.
      unfold StepAction, zvec_sub_run, zvec_add, nvec_to_zvec in Hsound |- *.
      rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl) in Hsound.
      rewrite (nth_map Z.of_nat (nvec_sum visibles) index index eq_refl) in Hsound.
      rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl),
        (nth_map Z.of_nat target index index eq_refl),
        (nth_map Z.of_nat (nvec_sum visibles) index index eq_refl).
      lia. }
    cbn. unfold machine_main_value, section_target_vector.
    rewrite Hdelta, step_action_append, step_action_zero. reflexivity.
  - constructor.
Qed.

Theorem compile_rule_image_complete : forall d q (rule : SRule d q)
    (W : VASSSection d q) state counters,
    OrderedRuleImage rule (VASSSectionReach W) state counters ->
    VASSSectionReach (compile_rule_image rule W) state counters.
Proof.
  intros d q rule W state counters
    [children [Hchildren [Hstates [Happly Hstate]]]].
  destruct (child_executions_of_ordered d q rule W children Hchildren Hstates)
    as [executions [Hindices [Hvisible Hconsecutive]]].
  destruct (executions_first_child d q rule W executions Hindices)
    as [first [tail [Hexecutions Hfirst]]].
  subst executions state.
  exists (rule_copy_state rule W (first_child rule)
      (child_execution_initial_state rule W first)),
    (rule_block_nvec rule W 0
      (child_execution_initial_counters rule W first)).
  split.
  - apply List.in_map_iff.
    exists (child_execution_initial_state rule W first,
      child_execution_initial_counters rule W first).
    split; [reflexivity|]. apply child_execution_initial_in.
  - apply vas_reach_direct_iff.
    eapply direct_vas_reach_trans.
    + pose proof (execute_consecutive_children d q rule W first tail
        Hconsecutive (nvec_zero (d + rule_image_aux_dimension rule W)))
        as Hexecute.
      rewrite !nvec_add_zero in Hexecute.
      rewrite Hfirst, first_child_value in Hexecute. exact Hexecute.
    + eapply direct_vas_reach_trans.
      * pose proof (rule_transfer_plan_reach d q rule W
          (children_transfer_plan (first :: tail))
          (nvec_zero (d + rule_image_aux_dimension rule W))) as Htransfer.
        rewrite !nvec_add_zero in Htransfer.
        rewrite children_transfer_plan_source,
          children_transfer_plan_target in Htransfer.
        exact Htransfer.
      * rewrite <- Hvisible in Happly.
        exact (rule_final_reach d q rule W
          (List.map
            (fun execution => child_execution_visible rule W execution)
            (first :: tail)) counters Happly).
Qed.

Lemma rule_has_state : forall d q (rule : SRule d q),
    exists state : Fin.t q, List.In state (input_states rule).
Proof.
  intros d q rule. destruct (input_states rule) as [|state tail] eqn:Hinputs.
  - exfalso. exact (input_nonempty rule Hinputs).
  - exists state. cbn. auto.
Qed.

Lemma section_state_count_positive_for_rule : forall d q (rule : SRule d q)
    (W : VASSSection d q),
    (0 < section_state_count W)%nat.
Proof.
  intros d q rule W. destruct (rule_has_state d q rule) as [state _].
  eapply Nat.le_lt_trans.
  - lia.
  - exact (proj2_sig (Fin.to_nat (section_accept_state W state))).
Qed.

Lemma fin_of_nat_lt_value : forall n p (H : (p < n)%nat),
    proj1_sig (Fin.to_nat (Fin.of_nat_lt H)) = p.
Proof.
  induction n as [|n IH]; intros [|p] H; cbn in *; try lia.
  destruct (Fin.to_nat (Fin.of_nat_lt (proj2 (Nat.succ_lt_mono p n) H)))
    as [value Hvalue] eqn:Hnat. cbn. f_equal.
  pose proof (IH p (proj2 (Nat.succ_lt_mono p n) H)) as Hrec.
  rewrite Hnat in Hrec. exact Hrec.
Qed.

Lemma fin_L_value : forall left right (index : Fin.t left),
    proj1_sig (Fin.to_nat (Fin.L right index)) =
    proj1_sig (Fin.to_nat index).
Proof.
  intros. apply Fin.L_sanity.
Qed.

Lemma rule_copy_state_value : forall d q (rule : SRule d q)
    (W : VASSSection d q) child state,
    proj1_sig (Fin.to_nat (rule_copy_state rule W child state)) =
    (proj1_sig (Fin.to_nat child) * section_state_count W +
      proj1_sig (Fin.to_nat state))%nat.
Proof.
  intros. unfold rule_copy_state. rewrite fin_L_value, fin_of_nat_lt_value.
  reflexivity.
Qed.

Lemma rule_copy_state_injective : forall d q (rule : SRule d q)
    (W : VASSSection d q) child1 state1 child2 state2,
    rule_copy_state rule W child1 state1 =
      rule_copy_state rule W child2 state2 ->
    child1 = child2 /\ state1 = state2.
Proof.
  intros d q rule W child1 state1 child2 state2 Heq.
  pose proof (f_equal (fun index => proj1_sig (Fin.to_nat index)) Heq) as Hvalue.
  cbv beta in Hvalue.
  rewrite !rule_copy_state_value in Hvalue.
  pose proof (proj2_sig (Fin.to_nat state1)) as Hstate1.
  pose proof (proj2_sig (Fin.to_nat state2)) as Hstate2.
  pose proof (section_state_count_positive_for_rule d q rule W) as Hpositive.
  assert (Hquotient1 : proj1_sig (Fin.to_nat child1) =
      ((proj1_sig (Fin.to_nat child1) * section_state_count W +
        proj1_sig (Fin.to_nat state1)) / section_state_count W)%nat).
  { eapply Nat.div_unique; [exact Hstate1|].
    rewrite Nat.mul_comm. reflexivity. }
  assert (Hquotient2 : proj1_sig (Fin.to_nat child2) =
      ((proj1_sig (Fin.to_nat child2) * section_state_count W +
        proj1_sig (Fin.to_nat state2)) / section_state_count W)%nat).
  { eapply Nat.div_unique; [exact Hstate2|].
    rewrite Nat.mul_comm. reflexivity. }
  assert (Hchild : proj1_sig (Fin.to_nat child1) =
      proj1_sig (Fin.to_nat child2)).
  { rewrite Hquotient1, Hquotient2, Hvalue. reflexivity. }
  assert (Hstate : proj1_sig (Fin.to_nat state1) =
      proj1_sig (Fin.to_nat state2)).
  { rewrite Hchild in Hvalue. nia. }
  split; apply Fin.to_nat_inj; assumption.
Qed.

Lemma rule_advance_transition_cases : forall d q (rule : SRule d q)
    (W : VASSSection d q) transition,
    List.In transition (rule_advance_transitions rule W) ->
    (exists child next config,
      fin_successor child = Some next /\
      List.In config (section_initial_configs W) /\
      transition = rule_advance_to_initial rule W child next config) \/
    (exists child,
      fin_successor child = None /\
      transition = rule_advance_to_collect rule W child).
Proof.
  intros d q rule W transition Hin.
  unfold rule_advance_transitions in Hin.
  apply in_flat_map in Hin as [child [_ Hin]].
  unfold rule_advance_transitions_for in Hin.
  destruct (fin_successor child) as [next|] eqn:Hnext.
  - left. apply List.in_map_iff in Hin as [config [<- Hconfig]].
    exists child, next, config. auto.
  - right. cbn in Hin. destruct Hin as [<-|[]].
    exists child. auto.
Qed.

Lemma rule_transfer_transition_cases : forall d q (rule : SRule d q)
    (W : VASSSection d q) transition,
    List.In transition (rule_transfer_transitions rule W) ->
    exists child coordinate,
      transition = rule_transfer_transition rule W child coordinate.
Proof.
  intros d q rule W transition Hin.
  unfold rule_transfer_transitions in Hin.
  apply in_flat_map in Hin as [child [_ Hin]].
  apply List.in_map_iff in Hin as [coordinate [<- _]].
  eauto.
Qed.

Lemma rule_copy_source_transition_cases : forall d q (rule : SRule d q)
    (W : VASSSection d q) child state transition,
    List.In transition (rule_image_system rule W) ->
    VASTransitionSource transition = rule_copy_state rule W child state ->
    (exists original,
      List.In original (section_system W) /\
      VASTransitionSource original = state /\
      transition = rule_copy_transition rule W child original) \/
    (state = section_accept_state W (rule_required_state rule child) /\
      ((exists next config,
          fin_successor child = Some next /\
          List.In config (section_initial_configs W) /\
          transition = rule_advance_to_initial rule W child next config) \/
       (fin_successor child = None /\
          transition = rule_advance_to_collect rule W child))).
Proof.
  intros d q rule W child state transition Hin Hsource.
  destruct (rule_image_transition_cases d q rule W transition Hin)
    as [Hcopy|[Hadvance|[Htransfer|Hfinal]]].
  - destruct (rule_copy_transition_source_is_copy d q rule W transition Hcopy)
      as [selected [original [Horiginal ->]]].
    cbn in Hsource.
    apply rule_copy_state_injective in Hsource as [Hchild Hstate].
    subst selected. left. exists original. auto.
  - destruct (rule_advance_transition_cases d q rule W transition Hadvance)
      as [[selected [next [config [Hnext [Hconfig ->]]]]]|[selected [Hlast ->]]];
      cbn in Hsource;
      apply rule_copy_state_injective in Hsource as [Hchild Hstate]; subst selected.
    + right. split; [symmetry; exact Hstate|]. left.
      exists next, config. auto.
    + right. split; [symmetry; exact Hstate|]. right. auto.
  - destruct (rule_transfer_transition_cases d q rule W transition Htransfer)
      as [selected [coordinate ->]]. cbn in Hsource.
    exfalso. eapply rule_copy_collect_distinct. symmetry. exact Hsource.
  - subst transition. cbn in Hsource.
    exfalso. eapply rule_copy_collect_distinct. symmetry. exact Hsource.
Qed.

Lemma rule_collect_source_transition_cases : forall d q (rule : SRule d q)
    (W : VASSSection d q) transition,
    List.In transition (rule_image_system rule W) ->
    VASTransitionSource transition = rule_collect_state rule W ->
    (exists child coordinate,
      transition = rule_transfer_transition rule W child coordinate) \/
    transition = rule_final_transition rule W.
Proof.
  intros d q rule W transition Hin Hsource.
  destruct (rule_image_transition_cases d q rule W transition Hin)
    as [Hcopy|[Hadvance|[Htransfer|Hfinal]]].
  - destruct (rule_copy_transition_source_is_copy d q rule W transition Hcopy)
      as [child [original [_ ->]]]. cbn in Hsource.
    exfalso. eapply rule_copy_collect_distinct. exact Hsource.
  - destruct (rule_advance_transition_source_is_copy d q rule W transition Hadvance)
      as [child Hcopy]. rewrite Hcopy in Hsource.
    exfalso. eapply rule_copy_collect_distinct. exact Hsource.
  - left. now apply rule_transfer_transition_cases in Htransfer.
  - now right.
Qed.

(** The proof-only projections below expose the visible parent block and one
    child occurrence.  They deliberately retain child indices: two equal
    configurations at distinct inputs are not identified. *)
Definition rule_main_projection {d q} (rule : SRule d q)
    (W : VASSSection d q)
    (value : NVec (d + rule_image_aux_dimension rule W)) : NVec d :=
  fst (Vector.splitat d value).

Lemma rule_child_coordinate_bound : forall d q (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule))
    (coordinate : Fin.t (rule_block_width W)),
    (proj1_sig (Fin.to_nat child) * rule_block_width W +
       proj1_sig (Fin.to_nat coordinate) <
     rule_image_aux_dimension rule W)%nat.
Proof.
  intros d q rule W child coordinate.
  assert (Hchild :
      (proj1_sig (Fin.to_nat child) < rule_child_count rule)%nat).
  { exact (proj2_sig (Fin.to_nat child)). }
  assert (Hcoordinate :
      (proj1_sig (Fin.to_nat coordinate) < rule_block_width W)%nat).
  { exact (proj2_sig (Fin.to_nat coordinate)). }
  unfold rule_image_aux_dimension.
  assert (Hstep :
    (proj1_sig (Fin.to_nat child) * rule_block_width W +
       proj1_sig (Fin.to_nat coordinate) <
     S (proj1_sig (Fin.to_nat child)) * rule_block_width W)%nat).
  { rewrite Nat.mul_succ_l. lia. }
  assert (Hbound :
    (S (proj1_sig (Fin.to_nat child)) * rule_block_width W <=
     rule_child_count rule * rule_block_width W)%nat).
  { apply Nat.mul_le_mono_r. lia. }
  exact (Nat.lt_le_trans _ _ _ Hstep Hbound).
Qed.

Definition rule_child_projection {d q} (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule))
    (value : NVec (d + rule_image_aux_dimension rule W)) :
    NVec (rule_block_width W) :=
  vector_of_function (rule_block_width W) (fun coordinate =>
    Vector.nth (snd (Vector.splitat d value)) (Fin.of_nat_lt (p :=
      proj1_sig (Fin.to_nat child) * rule_block_width W +
        proj1_sig (Fin.to_nat coordinate))
      (rule_child_coordinate_bound d q rule W child coordinate))).

Lemma rule_main_projection_append : forall d q (rule : SRule d q)
    (W : VASSSection d q) main blocks,
    rule_main_projection rule W (Vector.append main blocks) = main.
Proof.
  intros. unfold rule_main_projection. now rewrite VectorSpec.splitat_append.
Qed.

Lemma rule_main_projection_block : forall d q (rule : SRule d q)
    (W : VASSSection d q) child value,
    rule_main_projection rule W (rule_block_nvec rule W child value) =
      nvec_zero d.
Proof.
  intros. unfold rule_block_nvec. apply rule_main_projection_append.
Qed.

Lemma rule_child_projection_block_same : forall d q (rule : SRule d q)
    (W : VASSSection d q) child value,
    rule_child_projection rule W child
      (rule_block_nvec rule W (proj1_sig (Fin.to_nat child)) value) = value.
Proof.
  intros d q rule W child value.
  apply (proj1 (Vector.eq_nth_iff nat (rule_block_width W) _ _)).
  intros coordinate coordinate' Heq; subst coordinate'.
  unfold rule_child_projection.
  rewrite nth_vector_of_function.
  unfold rule_block_nvec.
  rewrite VectorSpec.splitat_append. cbn [snd].
  unfold block_n_at.
  rewrite nth_vector_of_function.
  rewrite Fin.to_nat_of_nat. cbn [proj1_sig].
  assert (Hcoordinate :
      (proj1_sig (Fin.to_nat coordinate) < rule_block_width W)%nat).
  { exact (proj2_sig (Fin.to_nat coordinate)). }
  assert (Hchild :
      (proj1_sig (Fin.to_nat child) < rule_child_count rule)%nat).
  { exact (proj2_sig (Fin.to_nat child)). }
  assert (Hlower :
    (proj1_sig (Fin.to_nat child) * rule_block_width W <=?
     proj1_sig (Fin.to_nat child) * rule_block_width W +
       proj1_sig (Fin.to_nat coordinate))%nat = true).
  { apply Nat.leb_le. lia. }
  assert (Hupper :
    (proj1_sig (Fin.to_nat child) * rule_block_width W +
       proj1_sig (Fin.to_nat coordinate) <?
     S (proj1_sig (Fin.to_nat child)) * rule_block_width W)%nat = true).
  { apply Nat.ltb_lt. rewrite Nat.mul_succ_l. lia. }
  rewrite Hlower, Hupper. cbn.
  replace (proj1_sig (Fin.to_nat child) * rule_block_width W +
      proj1_sig (Fin.to_nat coordinate) -
      proj1_sig (Fin.to_nat child) * rule_block_width W)%nat
    with (proj1_sig (Fin.to_nat coordinate)) by nia.
  symmetry.
  rewrite <- (to_list_nth_order nat (rule_block_width W) value
    (proj1_sig (Fin.to_nat coordinate)) Hcoordinate 0%nat).
  unfold Vector.nth_order. f_equal. apply Fin.to_nat_inj.
  rewrite Fin.to_nat_of_nat. reflexivity.
Qed.

Lemma rule_child_projection_block_other : forall d q (rule : SRule d q)
    (W : VASSSection d q) selected child value,
    selected <> child ->
    rule_child_projection rule W selected
      (rule_block_nvec rule W (proj1_sig (Fin.to_nat child)) value) =
      nvec_zero (rule_block_width W).
Proof.
  intros d q rule W selected child value Hneq.
  apply (proj1 (Vector.eq_nth_iff nat (rule_block_width W) _ _)).
  intros coordinate coordinate' Heq; subst coordinate'.
  unfold rule_child_projection.
  rewrite nth_vector_of_function.
  unfold rule_block_nvec.
  rewrite VectorSpec.splitat_append. cbn [snd].
  unfold block_n_at, nvec_zero.
  rewrite nth_vector_of_function, Fin.to_nat_of_nat, const_nth.
  cbn [proj1_sig].
  assert (Hcoordinate :
      (proj1_sig (Fin.to_nat coordinate) < rule_block_width W)%nat).
  { exact (proj2_sig (Fin.to_nat coordinate)). }
  assert (Hselected :
      (proj1_sig (Fin.to_nat selected) < rule_child_count rule)%nat).
  { exact (proj2_sig (Fin.to_nat selected)). }
  assert (Hchild :
      (proj1_sig (Fin.to_nat child) < rule_child_count rule)%nat).
  { exact (proj2_sig (Fin.to_nat child)). }
  destruct (Nat.leb
      (proj1_sig (Fin.to_nat child) * rule_block_width W)
      (proj1_sig (Fin.to_nat selected) * rule_block_width W +
        proj1_sig (Fin.to_nat coordinate)) &&
    Nat.ltb
      (proj1_sig (Fin.to_nat selected) * rule_block_width W +
        proj1_sig (Fin.to_nat coordinate))
      (S (proj1_sig (Fin.to_nat child)) * rule_block_width W))%bool
    eqn:Hinside; [|reflexivity].
  apply andb_true_iff in Hinside as [Hlower Hupper].
  apply Nat.leb_le in Hlower. apply Nat.ltb_lt in Hupper.
  exfalso. apply Hneq. apply Fin.to_nat_inj. nia.
Qed.

Lemma rule_child_projection_add : forall d q (rule : SRule d q)
    (W : VASSSection d q) child left right,
    rule_child_projection rule W child (nvec_add left right) =
    nvec_add (rule_child_projection rule W child left)
      (rule_child_projection rule W child right).
Proof.
  intros d q rule W child left right.
  destruct (Vector.splitat d left) as [left_main left_blocks] eqn:Hleft.
  destruct (Vector.splitat d right) as [right_main right_blocks] eqn:Hright.
  apply VectorSpec.append_splitat in Hleft, Hright.
  subst left right. rewrite nvec_add_append.
  unfold rule_child_projection.
  repeat rewrite VectorSpec.splitat_append. cbn [snd].
  apply (proj1 (Vector.eq_nth_iff nat (rule_block_width W) _ _)).
  intros index index' Heq; subst index'.
  unfold nvec_add.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  repeat rewrite nth_vector_of_function.
  rewrite (nth_map2 Nat.add _ _
    (Fin.of_nat_lt (rule_child_coordinate_bound d q rule W child index))
    (Fin.of_nat_lt (rule_child_coordinate_bound d q rule W child index))
    (Fin.of_nat_lt (rule_child_coordinate_bound d q rule W child index))
    eq_refl eq_refl).
  reflexivity.
Qed.

Definition rule_child_zprojection {d q} (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule))
    (value : ZVec (d + rule_image_aux_dimension rule W)) :
    ZVec (rule_block_width W) :=
  vector_of_function (rule_block_width W) (fun coordinate =>
    Vector.nth (snd (Vector.splitat d value)) (Fin.of_nat_lt (p :=
      proj1_sig (Fin.to_nat child) * rule_block_width W +
        proj1_sig (Fin.to_nat coordinate))
      (rule_child_coordinate_bound d q rule W child coordinate))).

Definition rule_main_zprojection {d q} (rule : SRule d q)
    (W : VASSSection d q)
    (value : ZVec (d + rule_image_aux_dimension rule W)) : ZVec d :=
  fst (Vector.splitat d value).

Lemma rule_main_zprojection_step_action : forall d q (rule : SRule d q)
    (W : VASSSection d q) source target,
    rule_main_zprojection rule W (StepAction source target) =
    StepAction (rule_main_projection rule W source)
      (rule_main_projection rule W target).
Proof.
  intros d q rule W source target.
  destruct (Vector.splitat d source) as [source_main source_blocks]
    eqn:Hsource.
  destruct (Vector.splitat d target) as [target_main target_blocks]
    eqn:Htarget.
  apply VectorSpec.append_splitat in Hsource, Htarget.
  subst source target. rewrite step_action_append.
  unfold rule_main_zprojection, rule_main_projection.
  repeat rewrite VectorSpec.splitat_append. reflexivity.
Qed.

Lemma rule_main_zprojection_block : forall d q (rule : SRule d q)
    (W : VASSSection d q) child value,
    rule_main_zprojection rule W (rule_block_zvec rule W child value) =
      zvec_zero d.
Proof.
  intros. unfold rule_main_zprojection, rule_block_zvec.
  now rewrite VectorSpec.splitat_append.
Qed.

Lemma rule_main_zprojection_final : forall d q (rule : SRule d q)
    (W : VASSSection d q),
    rule_main_zprojection rule W
      (VASTransitionAction (rule_final_transition rule W)) =
      rule_delta rule.
Proof.
  intros. unfold rule_main_zprojection, rule_final_transition. cbn.
  now rewrite VectorSpec.splitat_append.
Qed.

Lemma rule_child_zprojection_block_same : forall d q (rule : SRule d q)
    (W : VASSSection d q) child value,
    rule_child_zprojection rule W child
      (rule_block_zvec rule W (proj1_sig (Fin.to_nat child)) value) = value.
Proof.
  intros d q rule W child value.
  apply (proj1 (Vector.eq_nth_iff Z (rule_block_width W) _ _)).
  intros coordinate coordinate' Heq; subst coordinate'.
  unfold rule_child_zprojection. rewrite nth_vector_of_function.
  unfold rule_block_zvec. rewrite VectorSpec.splitat_append. cbn [snd].
  unfold block_z_at. rewrite nth_vector_of_function, Fin.to_nat_of_nat.
  cbn [proj1_sig].
  assert (Hcoordinate :
      (proj1_sig (Fin.to_nat coordinate) < rule_block_width W)%nat).
  { exact (proj2_sig (Fin.to_nat coordinate)). }
  assert (Hlower :
    (proj1_sig (Fin.to_nat child) * rule_block_width W <=?
     proj1_sig (Fin.to_nat child) * rule_block_width W +
       proj1_sig (Fin.to_nat coordinate))%nat = true).
  { apply Nat.leb_le. lia. }
  assert (Hupper :
    (proj1_sig (Fin.to_nat child) * rule_block_width W +
       proj1_sig (Fin.to_nat coordinate) <?
     S (proj1_sig (Fin.to_nat child)) * rule_block_width W)%nat = true).
  { apply Nat.ltb_lt. rewrite Nat.mul_succ_l. lia. }
  rewrite Hlower, Hupper. cbn.
  replace (proj1_sig (Fin.to_nat child) * rule_block_width W +
      proj1_sig (Fin.to_nat coordinate) -
      proj1_sig (Fin.to_nat child) * rule_block_width W)%nat
    with (proj1_sig (Fin.to_nat coordinate)) by nia.
  symmetry.
  rewrite <- (to_list_nth_order Z (rule_block_width W) value
    (proj1_sig (Fin.to_nat coordinate)) Hcoordinate 0%Z).
  unfold Vector.nth_order. f_equal. apply Fin.to_nat_inj.
  rewrite Fin.to_nat_of_nat. reflexivity.
Qed.

Lemma rule_child_zprojection_step_action : forall d q (rule : SRule d q)
    (W : VASSSection d q) child source target,
    rule_child_zprojection rule W child (StepAction source target) =
    StepAction (rule_child_projection rule W child source)
      (rule_child_projection rule W child target).
Proof.
  intros d q rule W child source target.
  destruct (Vector.splitat d source) as [source_main source_blocks]
    eqn:Hsource.
  destruct (Vector.splitat d target) as [target_main target_blocks]
    eqn:Htarget.
  apply VectorSpec.append_splitat in Hsource, Htarget.
  subst source target. rewrite step_action_append.
  unfold rule_child_zprojection, rule_child_projection.
  repeat rewrite VectorSpec.splitat_append. cbn [snd].
  unfold StepAction, zvec_sub_run, nvec_to_zvec.
  apply (proj1 (Vector.eq_nth_iff Z (rule_block_width W) _ _)).
  intros index index' Heq; subst index'.
  repeat rewrite nth_vector_of_function.
  rewrite (nth_map2 Z.sub _ _
    (Fin.of_nat_lt (rule_child_coordinate_bound d q rule W child index))
    (Fin.of_nat_lt (rule_child_coordinate_bound d q rule W child index))
    (Fin.of_nat_lt (rule_child_coordinate_bound d q rule W child index))
    eq_refl eq_refl).
  repeat rewrite (nth_map Z.of_nat _
    (Fin.of_nat_lt (rule_child_coordinate_bound d q rule W child index))
    (Fin.of_nat_lt (rule_child_coordinate_bound d q rule W child index))
    eq_refl).
  rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl).
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl).
  repeat rewrite nth_vector_of_function. reflexivity.
Qed.

Lemma rule_copy_step_project : forall d q (rule : SRule d q)
    (W : VASSSection d q) child
    (original : VASTransition (rule_block_width W) (section_state_count W))
    source target,
    rule_block_zvec rule W (proj1_sig (Fin.to_nat child))
      (VASTransitionAction original) = StepAction source target ->
    VASTransitionAction original =
      StepAction (rule_child_projection rule W child source)
        (rule_child_projection rule W child target).
Proof.
  intros d q rule W child original source target Hstep.
  pose proof (f_equal (rule_child_zprojection rule W child) Hstep) as H.
  rewrite rule_child_zprojection_block_same,
    rule_child_zprojection_step_action in H. exact H.
Qed.

Lemma rule_collect_to_output_inv : forall d q (rule : SRule d q)
    (W : VASSSection d q) source state target,
    DirectVASReach (rule_image_system rule W)
      (rule_collect_state rule W) source
      (rule_output_state rule W state) target ->
    exists before,
      DirectVASReach (rule_image_system rule W)
        (rule_collect_state rule W) source
        (rule_collect_state rule W) before /\
      VASTransitionAction (rule_final_transition rule W) =
        StepAction before target /\
      state = output_state rule.
Proof.
  intros d q rule W source state target Hreach.
  remember (rule_collect_state rule W) as start_state eqn:Hstart.
  remember source as start_counter eqn:Hstartcounter.
  remember (rule_output_state rule W state) as final_state eqn:Hfinal.
  remember target as final_counter eqn:Hfinalcounter.
  revert source state target Hstart Hstartcounter Hfinal Hfinalcounter.
  induction Hreach; intros source0 output0 final0
      Hstart Hstartcounter Hfinal Hfinalcounter.
  - exfalso. eapply rule_collect_output_distinct.
    transitivity state; [symmetry; exact Hstart|exact Hfinal].
  - subst source.
    destruct (rule_collect_source_transition_cases d q rule W transition H Hstart)
      as [[child [coordinate ->]]|Hlast].
    + cbn in Hreach.
      destruct (IHHreach target output0 final0 eq_refl eq_refl
        Hfinal Hfinalcounter)
        as [before [Hprefix [Haction Houtput]]].
      exists before. repeat split; try assumption.
      eapply direct_vas_reach_step; eauto.
    + subst transition. cbn in Hreach.
      rewrite Hfinal, Hfinalcounter in Hreach.
      destruct (rule_output_reach_inv d q rule W (output_state rule)
        target (rule_output_state rule W output0) final0 Hreach)
        as [Hstate Hcounter].
      apply (rule_output_state_injective d q rule W) in Hstate.
      subst output0 final0. exists source0. repeat split.
      * constructor.
      * rewrite Hcounter. exact H0.
Qed.

Lemma rule_child_projection_target_zero : forall d q (rule : SRule d q)
    (W : VASSSection d q) child counters,
    rule_child_projection rule W child
      (section_target_vector (compile_rule_image rule W) counters) =
      nvec_zero (rule_block_width W).
Proof.
  intros d q rule W child counters.
  unfold section_target_vector, rule_child_projection.
  rewrite VectorSpec.splitat_append. cbn [snd].
  apply (proj1 (Vector.eq_nth_iff nat (rule_block_width W) _ _)).
  intros index index' Heq; subst index'.
  rewrite nth_vector_of_function. unfold nvec_zero. rewrite !const_nth.
  reflexivity.
Qed.

Lemma rule_main_projection_target : forall d q (rule : SRule d q)
    (W : VASSSection d q) counters,
    rule_main_projection rule W
      (section_target_vector (compile_rule_image rule W) counters) = counters.
Proof.
  intros. unfold section_target_vector. apply rule_main_projection_append.
Qed.

Lemma rule_final_step_inv : forall d q (rule : SRule d q)
    (W : VASSSection d q) before target,
    VASTransitionAction (rule_final_transition rule W) =
      StepAction before
        (section_target_vector (compile_rule_image rule W) target) ->
    rule_delta rule =
      StepAction (rule_main_projection rule W before) target /\
    forall child,
      rule_child_projection rule W child before =
        nvec_zero (rule_block_width W).
Proof.
  intros d q rule W before target Hstep. split.
  - pose proof (f_equal (rule_main_zprojection rule W) Hstep) as Hmain.
    rewrite rule_main_zprojection_final,
      rule_main_zprojection_step_action,
      rule_main_projection_target in Hmain. exact Hmain.
  - intro child.
    pose proof (f_equal (rule_child_zprojection rule W child) Hstep) as Hchild.
    assert (Hzero : rule_child_zprojection rule W child
        (Vector.append (rule_delta rule)
          (zvec_zero (rule_image_aux_dimension rule W))) =
        zvec_zero (rule_block_width W)).
    { unfold rule_child_zprojection. rewrite VectorSpec.splitat_append.
      cbn [snd]. apply (proj1 (Vector.eq_nth_iff Z
        (rule_block_width W) _ _)).
      intros index index' Heq; subst index'.
      rewrite nth_vector_of_function. unfold zvec_zero. rewrite !const_nth.
      reflexivity. }
    change (rule_child_zprojection rule W child
      (Vector.append (rule_delta rule)
        (zvec_zero (rule_image_aux_dimension rule W))) =
      rule_child_zprojection rule W child
        (StepAction before
          (section_target_vector (compile_rule_image rule W) target))) in Hchild.
    rewrite Hzero, rule_child_zprojection_step_action,
      rule_child_projection_target_zero in Hchild.
    now apply step_action_zero_source in Hchild.
Qed.

Lemma same_step_action_offset : forall dimension
    (small_source small_target source target : NVec dimension),
    nvec_le small_source source ->
    StepAction small_source small_target = StepAction source target ->
    exists offset,
      source = nvec_add small_source offset /\
      target = nvec_add small_target offset.
Proof.
  intros dimension small_source small_target source target Hle Haction.
  exists (Vector.map2 Nat.sub source small_source).
  assert (Hsource : source = nvec_add small_source
      (Vector.map2 Nat.sub source small_source)).
  { apply (proj1 (Vector.eq_nth_iff nat dimension _ _)).
    intros index index' Heq; subst index'. unfold nvec_add.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
    rewrite (nth_map2 Nat.sub _ _ index index index eq_refl eq_refl).
    specialize (Hle index). lia. }
  split; [exact Hsource|].
  apply step_action_deterministic with (source := source).
  pose proof (step_action_shift dimension small_source small_target
    (Vector.map2 Nat.sub source small_source)) as Hshift.
  rewrite <- Hsource in Hshift. rewrite <- Haction. symmetry. exact Hshift.
Qed.

Lemma step_action_coordinate_value : forall dimension
    (action : ZVec dimension) source target coordinate,
    action = StepAction source target ->
    Vector.nth action coordinate =
      Z.of_nat (Vector.nth target coordinate) -
        Z.of_nat (Vector.nth source coordinate).
Proof.
  intros dimension action source target coordinate ->.
  unfold StepAction, zvec_sub_run, nvec_to_zvec.
  rewrite (nth_map2 Z.sub _ _ coordinate coordinate coordinate eq_refl eq_refl),
    (nth_map Z.of_nat target coordinate coordinate eq_refl),
    (nth_map Z.of_nat source coordinate coordinate eq_refl).
  reflexivity.
Qed.

Lemma negative_one_hot_coordinate : forall dimension selected coordinate,
    Vector.nth (Vector.map Z.opp (one_hot_z dimension selected)) coordinate =
    if Nat.eqb (proj1_sig (Fin.to_nat coordinate)) selected
    then (-1)%Z else 0%Z.
Proof.
  intros. rewrite (nth_map Z.opp _ coordinate coordinate eq_refl).
  unfold one_hot_z. rewrite nth_vector_of_function.
  destruct (Nat.eqb _ _); reflexivity.
Qed.

Lemma one_hot_nat_coordinate : forall dimension selected coordinate,
    Vector.nth (one_hot_nat dimension selected) coordinate =
    if Nat.eqb (proj1_sig (Fin.to_nat coordinate)) selected
    then 1%nat else O.
Proof.
  intros. unfold one_hot_nat. rewrite nth_vector_of_function. reflexivity.
Qed.

Lemma transfer_unit_action_at_child : forall dimension child_index main_index
    (coordinate : Fin.t dimension),
    Nat.eqb (proj1_sig (Fin.to_nat coordinate)) child_index = true ->
    child_index <> main_index ->
    Vector.nth
      (StepAction (one_hot_nat dimension child_index)
        (one_hot_nat dimension main_index)) coordinate = (-1)%Z.
Proof.
  intros dimension child_index main_index coordinate Hchild Hdistinct.
  unfold StepAction, zvec_sub_run, nvec_to_zvec.
  rewrite (nth_map2 Z.sub _ _ coordinate coordinate coordinate eq_refl eq_refl),
    (nth_map Z.of_nat _ coordinate coordinate eq_refl),
    (nth_map Z.of_nat _ coordinate coordinate eq_refl),
    !one_hot_nat_coordinate, Hchild.
  assert (Hmain :
      Nat.eqb (proj1_sig (Fin.to_nat coordinate)) main_index = false).
  { apply Nat.eqb_neq. apply Nat.eqb_eq in Hchild. congruence. }
  rewrite Hmain. reflexivity.
Qed.

Lemma one_hot_nat_le_from_negative_step : forall dimension source target index,
    Vector.map Z.opp (one_hot_z dimension index) = StepAction source target ->
    nvec_le (one_hot_nat dimension index) source.
Proof.
  intros dimension source target selected Hstep coordinate.
  unfold one_hot_nat. rewrite nth_vector_of_function.
  destruct (Nat.eqb (proj1_sig (Fin.to_nat coordinate)) selected)
    eqn:Hselected; cbn; [|lia].
  pose proof (step_action_coordinate_value dimension
    (Vector.map Z.opp (one_hot_z dimension selected)) source target
    coordinate Hstep) as Hcoordinate.
  rewrite negative_one_hot_coordinate, Hselected in Hcoordinate.
  cbn in Hcoordinate. lia.
Qed.

Lemma transfer_unit_source_le : forall dimension child_index main_index
    source target,
    StepAction (one_hot_nat dimension child_index)
      (one_hot_nat dimension main_index) = StepAction source target ->
    child_index <> main_index ->
    nvec_le (one_hot_nat dimension child_index) source.
Proof.
  intros dimension child_index main_index source target Hstep Hdistinct coordinate.
  rewrite one_hot_nat_coordinate.
  destruct (Nat.eqb (proj1_sig (Fin.to_nat coordinate)) child_index)
    eqn:Hchild; cbn; [|lia].
  pose proof (step_action_coordinate_value dimension
    (StepAction (one_hot_nat dimension child_index)
      (one_hot_nat dimension main_index)) source target coordinate Hstep)
    as Hactual.
  rewrite (transfer_unit_action_at_child dimension child_index main_index
    coordinate Hchild Hdistinct) in Hactual. lia.
Qed.

Lemma rule_transfer_step_offset : forall d q (rule : SRule d q)
    (W : VASSSection d q) child coordinate source target,
    VASTransitionAction (rule_transfer_transition rule W child coordinate) =
      StepAction source target ->
    exists offset,
      source = nvec_add
        (one_hot_nat (d + rule_image_aux_dimension rule W)
          (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
            proj1_sig (Fin.to_nat coordinate))) offset /\
      target = nvec_add
        (one_hot_nat (d + rule_image_aux_dimension rule W)
          (proj1_sig (Fin.to_nat coordinate))) offset.
Proof.
  intros d q rule W child coordinate source target Hstep.
  change (rule_transfer_action rule W
    (proj1_sig (Fin.to_nat child)) (proj1_sig (Fin.to_nat coordinate)) =
    StepAction source target) in Hstep.
  rewrite rule_transfer_action_step in Hstep.
  eapply same_step_action_offset; [|exact Hstep].
  eapply transfer_unit_source_le; [exact Hstep|].
  pose proof (proj2_sig (Fin.to_nat coordinate)) as Hcoordinate.
  unfold rule_block_width in *. lia.
Qed.

Definition rule_child_visible_projection {d q} (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule))
    (value : NVec (d + rule_image_aux_dimension rule W)) : NVec d :=
  fst (Vector.splitat d (rule_child_projection rule W child value)).

Definition rule_collect_mass {d q} (rule : SRule d q)
    (W : VASSSection d q)
    (value : NVec (d + rule_image_aux_dimension rule W)) : NVec d :=
  nvec_add (rule_main_projection rule W value)
    (nvec_sum (List.map
      (fun child => rule_child_visible_projection rule W child value)
      (all_fin (rule_child_count rule)))).

Lemma rule_main_projection_add : forall d q (rule : SRule d q)
    (W : VASSSection d q) left right,
    rule_main_projection rule W (nvec_add left right) =
      nvec_add (rule_main_projection rule W left)
        (rule_main_projection rule W right).
Proof.
  intros d q rule W left right.
  destruct (Vector.splitat d left) as [left_main left_blocks] eqn:Hleft.
  destruct (Vector.splitat d right) as [right_main right_blocks] eqn:Hright.
  apply VectorSpec.append_splitat in Hleft, Hright. subst left right.
  rewrite nvec_add_append. unfold rule_main_projection.
  repeat rewrite VectorSpec.splitat_append. reflexivity.
Qed.

Lemma nvec_split_left_add : forall left_dimension right_dimension
    (left right : NVec (left_dimension + right_dimension)),
    fst (Vector.splitat left_dimension (nvec_add left right)) =
      nvec_add (fst (Vector.splitat left_dimension left))
        (fst (Vector.splitat left_dimension right)).
Proof.
  intros left_dimension right_dimension left right.
  destruct (Vector.splitat left_dimension left) as [left_head left_tail]
    eqn:Hleft.
  destruct (Vector.splitat left_dimension right) as [right_head right_tail]
    eqn:Hright.
  apply VectorSpec.append_splitat in Hleft, Hright. subst left right.
  rewrite nvec_add_append, VectorSpec.splitat_append. reflexivity.
Qed.

Lemma nvec_split_right_add : forall left_dimension right_dimension
    (left right : NVec (left_dimension + right_dimension)),
    snd (Vector.splitat left_dimension (nvec_add left right)) =
      nvec_add (snd (Vector.splitat left_dimension left))
        (snd (Vector.splitat left_dimension right)).
Proof.
  intros left_dimension right_dimension left right.
  destruct (Vector.splitat left_dimension left) as [left_head left_tail]
    eqn:Hleft.
  destruct (Vector.splitat left_dimension right) as [right_head right_tail]
    eqn:Hright.
  apply VectorSpec.append_splitat in Hleft, Hright. subst left right.
  rewrite nvec_add_append, VectorSpec.splitat_append. reflexivity.
Qed.

Lemma rule_child_visible_projection_add : forall d q (rule : SRule d q)
    (W : VASSSection d q) child left right,
    rule_child_visible_projection rule W child (nvec_add left right) =
      nvec_add (rule_child_visible_projection rule W child left)
        (rule_child_visible_projection rule W child right).
Proof.
  intros. unfold rule_child_visible_projection.
  rewrite rule_child_projection_add. apply nvec_split_left_add.
Qed.

Lemma nvec_rsum_map_add : forall dimension A (f g : A -> NVec dimension) values,
    nvec_rsum_stateful (List.map (fun value => nvec_add (f value) (g value)) values) =
    nvec_add (nvec_rsum_stateful (List.map f values))
      (nvec_rsum_stateful (List.map g values)).
Proof.
  intros dimension A f g values. induction values as [|value tail IH]; cbn.
  - symmetry. apply nvec_add_zero_left_stateful.
  - rewrite IH. apply (proj1 (Vector.eq_nth_iff nat dimension _ _)).
    intros index index' Heq; subst index'. unfold nvec_add.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
    lia.
Qed.

Lemma rule_collect_mass_add : forall d q (rule : SRule d q)
    (W : VASSSection d q) left right,
    rule_collect_mass rule W (nvec_add left right) =
      nvec_add (rule_collect_mass rule W left)
        (rule_collect_mass rule W right).
Proof.
  intros. unfold rule_collect_mass.
  rewrite rule_main_projection_add.
  repeat rewrite nvec_sum_rsum_stateful.
  assert (Hmap :
    List.map (fun child => rule_child_visible_projection rule W child
      (nvec_add left right)) (all_fin (rule_child_count rule)) =
    List.map (fun child => nvec_add
      (rule_child_visible_projection rule W child left)
      (rule_child_visible_projection rule W child right))
      (all_fin (rule_child_count rule))).
  { apply List.map_ext. intro child.
    apply rule_child_visible_projection_add. }
  rewrite Hmap.
  rewrite nvec_rsum_map_add.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma nvec_rsum_zeros : forall dimension count,
    nvec_rsum_stateful (List.repeat (nvec_zero dimension) count) =
      nvec_zero dimension.
Proof.
  intros dimension count. induction count; cbn; [reflexivity|].
  rewrite IHcount. apply nvec_add_zero_left_stateful.
Qed.

Lemma nvec_rsum_map_zero : forall dimension A (values : list A),
    nvec_rsum_stateful
      (List.map (fun _ => nvec_zero dimension) values) = nvec_zero dimension.
Proof.
  intros dimension A values. induction values; cbn; [reflexivity|].
  rewrite IHvalues. apply nvec_add_zero_left_stateful.
Qed.

Lemma all_fin_indicator_sum : forall count dimension
    (selected : Fin.t count) (value : NVec dimension),
    nvec_rsum_stateful
      (List.map (fun index =>
        if Fin.eq_dec index selected then value else nvec_zero dimension)
        (all_fin count)) = value.
Proof.
  intros count dimension. induction count as [|count IH]; intros selected value.
  - exact (Fin.case0 (fun selected => _ = value) selected).
  - refine (Fin.caseS' selected (fun chosen =>
      nvec_rsum_stateful
        (List.map (fun index =>
          if Fin.eq_dec index chosen then value else nvec_zero dimension)
          (all_fin (S count))) = value) _ _).
    + cbn. destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_|Hneq]; [|contradiction].
      rewrite List.map_map.
      assert (Htail : List.map
          (fun index : Fin.t count =>
            if Fin.eq_dec (Fin.FS index) Fin.F1
            then value else nvec_zero dimension)
          (all_fin count) =
        List.map (fun _ : Fin.t count => nvec_zero dimension)
          (all_fin count)).
      { apply List.map_ext. intro index. destruct (Fin.eq_dec _ _).
        - discriminate.
        - reflexivity. }
      rewrite Htail.
      rewrite nvec_rsum_map_zero, nvec_add_zero. reflexivity.
    + intro tail. cbn. destruct (Fin.eq_dec Fin.F1 (Fin.FS tail)) as [Heq|_].
      { discriminate. }
      rewrite List.map_map.
      assert (Hmap : List.map
          (fun index : Fin.t count =>
            if Fin.eq_dec (Fin.FS index) (Fin.FS tail)
            then value else nvec_zero dimension)
          (all_fin count) =
        List.map (fun index =>
          if Fin.eq_dec index tail then value else nvec_zero dimension)
          (all_fin count)).
      { apply List.map_ext. intro index.
        destruct (Fin.eq_dec (Fin.FS index) (Fin.FS tail)) as [HeqFS|HneqFS];
        destruct (Fin.eq_dec index tail) as [Heq|Hneq]; try reflexivity.
        - exfalso. apply Hneq. now apply Fin.FS_inj in HeqFS.
        - exfalso. apply HneqFS. now subst tail. }
      rewrite Hmap, IH. apply nvec_add_zero_left_stateful.
Qed.

Lemma rule_child_visible_projection_block : forall d q (rule : SRule d q)
    (W : VASSSection d q) selected child visible,
    rule_child_visible_projection rule W selected
      (rule_block_nvec rule W (proj1_sig (Fin.to_nat child))
        (visible_block_value W visible)) =
    if Fin.eq_dec selected child then visible else nvec_zero d.
Proof.
  intros d q rule W selected child visible.
  destruct (Fin.eq_dec selected child) as [Heq|Hneq].
  - subst selected. unfold rule_child_visible_projection.
    rewrite rule_child_projection_block_same. unfold visible_block_value.
    rewrite VectorSpec.splitat_append. reflexivity.
  - unfold rule_child_visible_projection.
    rewrite rule_child_projection_block_other by exact Hneq.
    assert (Hzero : nvec_zero (rule_block_width W) =
        Vector.append (nvec_zero d) (nvec_zero (section_aux_dimension W))).
    { unfold rule_block_width. apply nvec_zero_append. }
    rewrite Hzero, VectorSpec.splitat_append. reflexivity.
Qed.

Lemma rule_collect_mass_child_unit : forall d q (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule))
    (coordinate : Fin.t d),
    rule_collect_mass rule W
      (one_hot_nat (d + rule_image_aux_dimension rule W)
        (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
          proj1_sig (Fin.to_nat coordinate))) =
      one_hot_nat d (proj1_sig (Fin.to_nat coordinate)).
Proof.
  intros d q rule W child coordinate.
  assert (Hunit :
    one_hot_nat (d + rule_image_aux_dimension rule W)
      (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
        proj1_sig (Fin.to_nat coordinate)) =
    rule_block_nvec rule W (proj1_sig (Fin.to_nat child))
      (visible_block_value W
        (coordinate_count_vector (coordinate, 1%nat)))).
  { transitivity (transfer_child_units rule W
      (child_transfer_item rule child (coordinate, 1%nat))).
    - unfold transfer_child_units, child_transfer_item. cbn [nvec_times].
      symmetry. apply nvec_add_zero.
    - apply transfer_child_units_item. }
  rewrite Hunit. unfold rule_collect_mass.
  rewrite rule_main_projection_block, nvec_add_zero_left_stateful,
    nvec_sum_rsum_stateful.
  assert (Hmap : List.map
      (fun selected => rule_child_visible_projection rule W selected
        (rule_block_nvec rule W (proj1_sig (Fin.to_nat child))
          (visible_block_value W
            (coordinate_count_vector (coordinate, 1%nat)))))
      (all_fin (rule_child_count rule)) =
    List.map (fun selected => if Fin.eq_dec selected child
      then coordinate_count_vector (coordinate, 1%nat) else nvec_zero d)
      (all_fin (rule_child_count rule))).
  { apply List.map_ext. intro selected.
    apply rule_child_visible_projection_block. }
  rewrite Hmap, all_fin_indicator_sum.
  unfold coordinate_count_vector. cbn [nvec_times].
  apply nvec_add_zero.
Qed.

Lemma rule_main_projection_one_hot : forall d q (rule : SRule d q)
    (W : VASSSection d q) (coordinate : Fin.t d),
    rule_main_projection rule W
      (one_hot_nat (d + rule_image_aux_dimension rule W)
        (proj1_sig (Fin.to_nat coordinate))) =
      one_hot_nat d (proj1_sig (Fin.to_nat coordinate)).
Proof.
  intros d q rule W coordinate.
  rewrite <- (one_hot_append_zero_right_nat d
    (rule_image_aux_dimension rule W)
    (proj1_sig (Fin.to_nat coordinate)) (proj2_sig (Fin.to_nat coordinate))).
  apply rule_main_projection_append.
Qed.

Lemma rule_child_projection_main_one_hot : forall d q (rule : SRule d q)
    (W : VASSSection d q) child (coordinate : Fin.t d),
    rule_child_projection rule W child
      (one_hot_nat (d + rule_image_aux_dimension rule W)
        (proj1_sig (Fin.to_nat coordinate))) =
      nvec_zero (rule_block_width W).
Proof.
  intros d q rule W child coordinate.
  rewrite <- (one_hot_append_zero_right_nat d
    (rule_image_aux_dimension rule W)
    (proj1_sig (Fin.to_nat coordinate)) (proj2_sig (Fin.to_nat coordinate))).
  unfold rule_child_projection. rewrite VectorSpec.splitat_append. cbn [snd].
  apply (proj1 (Vector.eq_nth_iff nat (rule_block_width W) _ _)).
  intros index index' Heq; subst index'. rewrite nth_vector_of_function.
  unfold nvec_zero. rewrite !const_nth. reflexivity.
Qed.

Lemma rule_collect_mass_main_unit : forall d q (rule : SRule d q)
    (W : VASSSection d q) (coordinate : Fin.t d),
    rule_collect_mass rule W
      (one_hot_nat (d + rule_image_aux_dimension rule W)
        (proj1_sig (Fin.to_nat coordinate))) =
      one_hot_nat d (proj1_sig (Fin.to_nat coordinate)).
Proof.
  intros d q rule W coordinate. unfold rule_collect_mass.
  rewrite rule_main_projection_one_hot, nvec_sum_rsum_stateful.
  assert (Hmap : List.map
      (fun child => rule_child_visible_projection rule W child
        (one_hot_nat (d + rule_image_aux_dimension rule W)
          (proj1_sig (Fin.to_nat coordinate))))
      (all_fin (rule_child_count rule)) =
    List.map (fun _ => nvec_zero d) (all_fin (rule_child_count rule))).
  { apply List.map_ext. intro child.
    unfold rule_child_visible_projection.
    rewrite rule_child_projection_main_one_hot.
    assert (Hzero : nvec_zero (rule_block_width W) =
        Vector.append (nvec_zero d) (nvec_zero (section_aux_dimension W))).
    { unfold rule_block_width. apply nvec_zero_append. }
    rewrite Hzero, VectorSpec.splitat_append. reflexivity. }
  rewrite Hmap, nvec_rsum_map_zero, nvec_add_zero. reflexivity.
Qed.

Lemma rule_transfer_preserves_collect_mass : forall d q
    (rule : SRule d q) (W : VASSSection d q) child coordinate source target,
    VASTransitionAction (rule_transfer_transition rule W child coordinate) =
      StepAction source target ->
    rule_collect_mass rule W source = rule_collect_mass rule W target.
Proof.
  intros d q rule W child coordinate source target Hstep.
  destruct (rule_transfer_step_offset d q rule W child coordinate
    source target Hstep) as [offset [Hsource Htarget]].
  rewrite Hsource, Htarget, !rule_collect_mass_add,
    rule_collect_mass_child_unit, rule_collect_mass_main_unit.
  reflexivity.
Qed.

Lemma rule_collect_reach_preserves_mass : forall d q
    (rule : SRule d q) (W : VASSSection d q) source target,
    DirectVASReach (rule_image_system rule W)
      (rule_collect_state rule W) source
      (rule_collect_state rule W) target ->
    rule_collect_mass rule W source = rule_collect_mass rule W target.
Proof.
  intros d q rule W source target Hreach.
  assert (Haux : forall initial_state initial final_state final,
      DirectVASReach (rule_image_system rule W)
        initial_state initial final_state final ->
      initial_state = rule_collect_state rule W ->
      final_state = rule_collect_state rule W ->
      rule_collect_mass rule W initial = rule_collect_mass rule W final).
  { intros initial_state initial final_state final Hpath.
    induction Hpath; intros Hinitial Hfinal.
    - reflexivity.
    - destruct (rule_collect_source_transition_cases d q rule W transition H
        Hinitial) as [[child [coordinate ->]]|Hlast].
      + cbn in Hpath. transitivity (rule_collect_mass rule W target0).
        * eapply rule_transfer_preserves_collect_mass. exact H0.
        * eapply IHHpath; [reflexivity|exact Hfinal].
      + subst transition. cbn in Hpath.
        destruct (rule_output_reach_inv d q rule W (output_state rule) target0
          final_state final Hpath) as [Hstate _].
        exfalso. eapply rule_collect_output_distinct.
        rewrite <- Hfinal. exact Hstate. }
  eapply Haux; eauto.
Qed.

Definition rule_child_aux_projection {d q} (rule : SRule d q)
    (W : VASSSection d q) (child : Fin.t (rule_child_count rule))
    (value : NVec (d + rule_image_aux_dimension rule W)) :
    NVec (section_aux_dimension W) :=
  snd (Vector.splitat d (rule_child_projection rule W child value)).

Lemma rule_child_aux_projection_add : forall d q (rule : SRule d q)
    (W : VASSSection d q) child left right,
    rule_child_aux_projection rule W child (nvec_add left right) =
    nvec_add (rule_child_aux_projection rule W child left)
      (rule_child_aux_projection rule W child right).
Proof.
  intros. unfold rule_child_aux_projection.
  rewrite rule_child_projection_add.
  apply nvec_split_right_add.
Qed.

Lemma rule_child_aux_projection_main_unit : forall d q
    (rule : SRule d q) (W : VASSSection d q) selected
    (coordinate : Fin.t d),
    rule_child_aux_projection rule W selected
      (one_hot_nat (d + rule_image_aux_dimension rule W)
        (proj1_sig (Fin.to_nat coordinate))) =
      nvec_zero (section_aux_dimension W).
Proof.
  intros. unfold rule_child_aux_projection.
  rewrite rule_child_projection_main_one_hot.
  assert (Hzero : nvec_zero (rule_block_width W) =
      Vector.append (nvec_zero d) (nvec_zero (section_aux_dimension W))).
  { unfold rule_block_width. apply nvec_zero_append. }
  rewrite Hzero, VectorSpec.splitat_append. reflexivity.
Qed.

Lemma rule_child_aux_projection_child_unit : forall d q
    (rule : SRule d q) (W : VASSSection d q)
    (selected child : Fin.t (rule_child_count rule))
    (coordinate : Fin.t d),
    rule_child_aux_projection rule W selected
      (one_hot_nat (d + rule_image_aux_dimension rule W)
        (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
          proj1_sig (Fin.to_nat coordinate))) =
      nvec_zero (section_aux_dimension W).
Proof.
  intros d q rule W selected child coordinate.
  assert (Hunit :
    one_hot_nat (d + rule_image_aux_dimension rule W)
      (d + proj1_sig (Fin.to_nat child) * rule_block_width W +
        proj1_sig (Fin.to_nat coordinate)) =
    rule_block_nvec rule W (proj1_sig (Fin.to_nat child))
      (visible_block_value W
        (coordinate_count_vector (coordinate, 1%nat)))).
  { transitivity (transfer_child_units rule W
      (child_transfer_item rule child (coordinate, 1%nat)));
      [unfold transfer_child_units, child_transfer_item;
       cbn [nvec_times]; symmetry; apply nvec_add_zero|
       apply transfer_child_units_item]. }
  rewrite Hunit. unfold rule_child_aux_projection.
  destruct (Fin.eq_dec selected child) as [->|Hneq].
  - rewrite rule_child_projection_block_same.
    unfold visible_block_value. rewrite VectorSpec.splitat_append. reflexivity.
  - rewrite rule_child_projection_block_other by exact Hneq.
    assert (Hzero : nvec_zero (rule_block_width W) =
        Vector.append (nvec_zero d) (nvec_zero (section_aux_dimension W))).
    { unfold rule_block_width. apply nvec_zero_append. }
    rewrite Hzero, VectorSpec.splitat_append. reflexivity.
Qed.

Lemma rule_transfer_preserves_child_aux : forall d q
    (rule : SRule d q) (W : VASSSection d q) selected child coordinate
    source target,
    VASTransitionAction (rule_transfer_transition rule W child coordinate) =
      StepAction source target ->
    rule_child_aux_projection rule W selected source =
      rule_child_aux_projection rule W selected target.
Proof.
  intros d q rule W selected child coordinate source target Hstep.
  destruct (rule_transfer_step_offset d q rule W child coordinate
    source target Hstep) as [offset [Hsource Htarget]].
  rewrite Hsource, Htarget, !rule_child_aux_projection_add,
    rule_child_aux_projection_child_unit,
    rule_child_aux_projection_main_unit.
  reflexivity.
Qed.

Lemma rule_collect_reach_preserves_child_aux : forall d q
    (rule : SRule d q) (W : VASSSection d q) selected source target,
    DirectVASReach (rule_image_system rule W)
      (rule_collect_state rule W) source
      (rule_collect_state rule W) target ->
    rule_child_aux_projection rule W selected source =
      rule_child_aux_projection rule W selected target.
Proof.
  intros d q rule W selected source target Hreach.
  assert (Haux : forall initial_state initial final_state final,
      DirectVASReach (rule_image_system rule W)
        initial_state initial final_state final ->
      initial_state = rule_collect_state rule W ->
      final_state = rule_collect_state rule W ->
      rule_child_aux_projection rule W selected initial =
        rule_child_aux_projection rule W selected final).
  { intros initial_state initial final_state final Hpath.
    induction Hpath; intros Hinitial Hfinal.
    - reflexivity.
    - destruct (rule_collect_source_transition_cases d q rule W transition H
        Hinitial) as [[child [coordinate ->]]|Hlast].
      + cbn in Hpath. transitivity
          (rule_child_aux_projection rule W selected target0).
        * eapply rule_transfer_preserves_child_aux. exact H0.
        * eapply IHHpath; [reflexivity|exact Hfinal].
      + subst transition. cbn in Hpath.
        destruct (rule_output_reach_inv d q rule W (output_state rule) target0
          final_state final Hpath) as [Hstate _].
        exfalso. eapply rule_collect_output_distinct.
        rewrite <- Hfinal. exact Hstate. }
  eapply Haux; eauto.
Qed.

Lemma rule_copy_to_output_split : forall d q (rule : SRule d q)
    (W : VASSSection d q) child state source output target,
    DirectVASReach (rule_image_system rule W)
      (rule_copy_state rule W child state) source
      (rule_output_state rule W output) target ->
    exists collect_counter,
      DirectVASReach (rule_image_system rule W)
        (rule_copy_state rule W child state) source
        (rule_collect_state rule W) collect_counter /\
      DirectVASReach (rule_image_system rule W)
        (rule_collect_state rule W) collect_counter
        (rule_output_state rule W output) target.
Proof.
  intros d q rule W child state source output target Hreach.
  assert (Haux : forall initial_state initial final_state final child0 state0 output0,
      DirectVASReach (rule_image_system rule W)
        initial_state initial final_state final ->
      initial_state = rule_copy_state rule W child0 state0 ->
      final_state = rule_output_state rule W output0 ->
      exists collect_counter,
        DirectVASReach (rule_image_system rule W)
          (rule_copy_state rule W child0 state0) initial
          (rule_collect_state rule W) collect_counter /\
        DirectVASReach (rule_image_system rule W)
          (rule_collect_state rule W) collect_counter
          (rule_output_state rule W output0) final).
  { intros initial_state initial final_state final child0 state0 output0 Hpath.
    revert child0 state0 output0.
    induction Hpath; intros child_index copy_state output_index Hinitial Hfinal.
    - exfalso. eapply rule_copy_output_distinct.
      rewrite <- Hinitial, <- Hfinal. reflexivity.
    - destruct (rule_copy_source_transition_cases d q rule W child_index copy_state
        transition H Hinitial) as
        [[original [Horiginal [Horiginal_source ->]]]|
         [Haccepted [[next [config [Hnext [Hconfig ->]]]]|[Hlast ->]]]].
      + cbn in Hpath.
        destruct (IHHpath child_index (VASTransitionTarget original) output_index
          eq_refl Hfinal) as [collect_counter [Hprefix Hsuffix]].
        exists collect_counter. split; [|exact Hsuffix].
        rewrite <- Hinitial.
        eapply direct_vas_reach_step; eauto.
      + cbn in Hpath.
        destruct (IHHpath next (fst config) output_index eq_refl Hfinal)
          as [collect_counter [Hprefix Hsuffix]].
        exists collect_counter. split; [|exact Hsuffix].
        rewrite <- Hinitial.
        eapply direct_vas_reach_step; eauto.
      + cbn in Hpath. exists target0. split; [|].
        * rewrite <- Hinitial. eapply direct_vas_reach_step; eauto. constructor.
        * now rewrite Hfinal in Hpath. }
  eapply Haux; eauto.
Qed.

(** A copy prefix stops at the first entrance into [Collect].  Recording this
    phase separately prevents later transfer loops from being mistaken for
    part of a child computation. *)
Inductive RuleCopyPrefix {d q} (rule : SRule d q) (W : VASSSection d q) :
    forall (child : Fin.t (rule_child_count rule))
      (state : Fin.t (section_state_count W)),
      NVec (d + rule_image_aux_dimension rule W) ->
      NVec (d + rule_image_aux_dimension rule W) -> Prop :=
| rule_copy_prefix_step : forall child state original source next collect,
    List.In original (section_system W) ->
    VASTransitionSource original = state ->
    VASTransitionAction (rule_copy_transition rule W child original) =
      StepAction source next ->
    RuleCopyPrefix rule W child (VASTransitionTarget original) next collect ->
    RuleCopyPrefix rule W child state source collect
| rule_copy_prefix_next : forall child state next_child config source next collect,
    state = section_accept_state W (rule_required_state rule child) ->
    fin_successor child = Some next_child ->
    List.In config (section_initial_configs W) ->
    VASTransitionAction
      (rule_advance_to_initial rule W child next_child config) =
      StepAction source next ->
    RuleCopyPrefix rule W next_child (fst config) next collect ->
    RuleCopyPrefix rule W child state source collect
| rule_copy_prefix_last : forall child state source collect,
    state = section_accept_state W (rule_required_state rule child) ->
    fin_successor child = None ->
    VASTransitionAction (rule_advance_to_collect rule W child) =
      StepAction source collect ->
    RuleCopyPrefix rule W child state source collect.

Lemma rule_copy_prefix_reach : forall d q (rule : SRule d q)
    (W : VASSSection d q) child state source collect,
    RuleCopyPrefix rule W child state source collect ->
    DirectVASReach (rule_image_system rule W)
      (rule_copy_state rule W child state) source
      (rule_collect_state rule W) collect.
Proof.
  intros d q rule W child state source collect Hprefix.
  induction Hprefix.
  - rewrite <- H0. eapply direct_vas_reach_step with
        (transition := rule_copy_transition rule W child original)
        (target := next); eauto using rule_copy_transition_in.
  - subst state. eapply direct_vas_reach_step with
        (transition := rule_advance_to_initial rule W child next_child config)
        (target := next); eauto using rule_advance_to_initial_in.
  - subst state. eapply direct_vas_reach_step with
        (transition := rule_advance_to_collect rule W child)
        (target := collect); eauto using rule_advance_to_collect_in.
    constructor.
Qed.

Lemma rule_copy_to_output_phase_decomposition : forall d q
    (rule : SRule d q) (W : VASSSection d q) child state source output target,
    DirectVASReach (rule_image_system rule W)
      (rule_copy_state rule W child state) source
      (rule_output_state rule W output) target ->
    exists collect_counter,
      RuleCopyPrefix rule W child state source collect_counter /\
      DirectVASReach (rule_image_system rule W)
        (rule_collect_state rule W) collect_counter
        (rule_output_state rule W output) target.
Proof.
  intros d q rule W child state source output target Hreach.
  assert (Haux : forall initial_state initial final_state final child0 state0 output0,
      DirectVASReach (rule_image_system rule W)
        initial_state initial final_state final ->
      initial_state = rule_copy_state rule W child0 state0 ->
      final_state = rule_output_state rule W output0 ->
      exists collect_counter,
        RuleCopyPrefix rule W child0 state0 initial collect_counter /\
        DirectVASReach (rule_image_system rule W)
          (rule_collect_state rule W) collect_counter
          (rule_output_state rule W output0) final).
  { intros initial_state initial final_state final child0 state0 output0 Hpath.
    revert child0 state0 output0.
    induction Hpath; intros child_index copy_state output_index Hinitial Hfinal.
    - exfalso. eapply rule_copy_output_distinct.
      rewrite <- Hinitial, <- Hfinal. reflexivity.
    - destruct (rule_copy_source_transition_cases d q rule W child_index copy_state
        transition H Hinitial) as
        [[original [Horiginal [Horiginal_source ->]]]|
         [Haccepted [[next_child [config [Hnext [Hconfig ->]]]]|[Hlast ->]]]].
      + cbn in Hpath.
        destruct (IHHpath child_index (VASTransitionTarget original) output_index
          eq_refl Hfinal) as [collect_counter [Hprefix Hsuffix]].
        exists collect_counter. split; [|exact Hsuffix].
        eapply rule_copy_prefix_step with (original := original)
          (next := target0); eauto.
      + cbn in Hpath.
        destruct (IHHpath next_child (fst config) output_index eq_refl Hfinal)
          as [collect_counter [Hprefix Hsuffix]].
        exists collect_counter. split; [|exact Hsuffix].
        eapply rule_copy_prefix_next with (next_child := next_child)
          (config := config) (next := target0); eauto.
      + cbn in Hpath. exists target0. split.
        * eapply rule_copy_prefix_last; eauto.
        * now rewrite Hfinal in Hpath. }
  eapply Haux; eauto.
Qed.

Lemma rule_child_zprojection_block_other : forall d q (rule : SRule d q)
    (W : VASSSection d q) selected child value,
    selected <> child ->
    rule_child_zprojection rule W selected
      (rule_block_zvec rule W (proj1_sig (Fin.to_nat child)) value) =
      zvec_zero (rule_block_width W).
Proof.
  intros d q rule W selected child value Hneq.
  apply (proj1 (Vector.eq_nth_iff Z (rule_block_width W) _ _)).
  intros coordinate coordinate' Heq; subst coordinate'.
  unfold rule_child_zprojection. rewrite nth_vector_of_function.
  unfold rule_block_zvec. rewrite VectorSpec.splitat_append. cbn [snd].
  unfold block_z_at, zvec_zero.
  rewrite nth_vector_of_function, Fin.to_nat_of_nat, const_nth.
  cbn [proj1_sig].
  destruct (Nat.leb
      (proj1_sig (Fin.to_nat child) * rule_block_width W)
      (proj1_sig (Fin.to_nat selected) * rule_block_width W +
        proj1_sig (Fin.to_nat coordinate)) &&
    Nat.ltb
      (proj1_sig (Fin.to_nat selected) * rule_block_width W +
        proj1_sig (Fin.to_nat coordinate))
      (S (proj1_sig (Fin.to_nat child)) * rule_block_width W))%bool
    eqn:Hinside; [|reflexivity].
  apply andb_true_iff in Hinside as [Hlower Hupper].
  apply Nat.leb_le in Hlower. apply Nat.ltb_lt in Hupper.
  assert (Hcoordinate :
      (proj1_sig (Fin.to_nat coordinate) < rule_block_width W)%nat)
    by exact (proj2_sig (Fin.to_nat coordinate)).
  assert (Hselected :
      (proj1_sig (Fin.to_nat selected) < rule_child_count rule)%nat)
    by exact (proj2_sig (Fin.to_nat selected)).
  assert (Hchild :
      (proj1_sig (Fin.to_nat child) < rule_child_count rule)%nat)
    by exact (proj2_sig (Fin.to_nat child)).
  exfalso. apply Hneq. apply Fin.to_nat_inj.
  nia.
Qed.

Lemma rule_block_step_preserves_other_child : forall d q
    (rule : SRule d q) (W : VASSSection d q) selected child action
    source target,
    selected <> child ->
    rule_block_zvec rule W (proj1_sig (Fin.to_nat child)) action =
      StepAction source target ->
    rule_child_projection rule W selected source =
      rule_child_projection rule W selected target.
Proof.
  intros d q rule W selected child action source target Hneq Hstep.
  pose proof (f_equal (rule_child_zprojection rule W selected) Hstep) as H.
  rewrite rule_child_zprojection_block_other in H by exact Hneq.
  rewrite rule_child_zprojection_step_action in H.
  now apply step_action_zero_source in H.
Qed.

Lemma rule_zero_step_preserves_child : forall d q (rule : SRule d q)
    (W : VASSSection d q) child source target,
    zvec_zero (d + rule_image_aux_dimension rule W) =
      StepAction source target ->
    rule_child_projection rule W child source =
      rule_child_projection rule W child target.
Proof.
  intros d q rule W child source target Hstep.
  apply step_action_zero_source in Hstep. now subst target.
Qed.

Lemma rule_copy_prefix_preserves_prior_child : forall d q
    (rule : SRule d q) (W : VASSSection d q) active state source collect
    (prior : Fin.t (rule_child_count rule)),
    (proj1_sig (Fin.to_nat prior) < proj1_sig (Fin.to_nat active))%nat ->
    RuleCopyPrefix rule W active state source collect ->
    rule_child_projection rule W prior source =
      rule_child_projection rule W prior collect.
Proof.
  intros d q rule W active state source collect prior Hlt Hprefix.
  induction Hprefix.
  - transitivity (rule_child_projection rule W prior next).
    + eapply rule_block_step_preserves_other_child; [|exact H1].
      intro Heq. subst prior. lia.
    + apply IHHprefix. exact Hlt.
  - transitivity (rule_child_projection rule W prior next).
    + eapply rule_block_step_preserves_other_child; [|exact H2].
      intro Heq. subst prior.
      pose proof (fin_successor_some_value _ _ _ H0). lia.
    + apply IHHprefix.
      pose proof (fin_successor_some_value _ _ _ H0). lia.
  - eapply rule_zero_step_preserves_child. exact H1.
Qed.

Record RawRuleChildExecution {d q} (rule : SRule d q)
    (W : VASSSection d q) := {
  raw_child_index : Fin.t (rule_child_count rule);
  raw_child_initial_state : Fin.t (section_state_count W);
  raw_child_initial_counters : NVec (rule_block_width W);
  raw_child_endpoint : NVec (rule_block_width W);
  raw_child_initial_in :
    List.In (raw_child_initial_state, raw_child_initial_counters)
      (section_initial_configs W);
  raw_child_reach :
    DirectVASReach (section_system W)
      raw_child_initial_state raw_child_initial_counters
      (section_accept_state W (rule_required_state rule raw_child_index))
      raw_child_endpoint
}.

Definition raw_child_matches_collect {d q} (rule : SRule d q)
    (W : VASSSection d q)
    (collect : NVec (d + rule_image_aux_dimension rule W))
    (execution : RawRuleChildExecution rule W) : Prop :=
  raw_child_endpoint rule W execution =
    rule_child_projection rule W (raw_child_index rule W execution) collect.

Lemma rule_copy_prefix_parse : forall d q (rule : SRule d q)
    (W : VASSSection d q) child state source collect
    initial_state initial_counters,
    List.In (initial_state, initial_counters) (section_initial_configs W) ->
    DirectVASReach (section_system W)
      initial_state initial_counters state
      (rule_child_projection rule W child source) ->
    (forall later,
      (proj1_sig (Fin.to_nat child) < proj1_sig (Fin.to_nat later))%nat ->
      rule_child_projection rule W later source =
        nvec_zero (rule_block_width W)) ->
    RuleCopyPrefix rule W child state source collect ->
    exists executions : list (RawRuleChildExecution rule W),
      List.map (raw_child_index rule W) executions <> [] /\
      List.hd_error (List.map (raw_child_index rule W) executions) = Some child /\
      ConsecutiveFin (List.map (raw_child_index rule W) executions) /\
      List.Forall (raw_child_matches_collect rule W collect) executions.
Proof.
  intros d q rule W child state source collect initial_state initial_counters
    Hinitial Hcurrent Hfuture Hprefix.
  revert initial_state initial_counters Hinitial Hcurrent Hfuture.
  induction Hprefix; intros initial_state initial_counters
    Hinitial Hcurrent Hfuture.
  - assert (Hprojected : VASTransitionAction original =
        StepAction (rule_child_projection rule W child source)
          (rule_child_projection rule W child next)).
    { eapply rule_copy_step_project. exact H1. }
    assert (Hstep : DirectVASReach (section_system W) state
        (rule_child_projection rule W child source)
        (VASTransitionTarget original)
        (rule_child_projection rule W child next)).
    { rewrite <- H0. eapply direct_vas_reach_step with
          (transition := original)
          (target := rule_child_projection rule W child next); eauto.
      constructor. }
    assert (Hcurrent' : DirectVASReach (section_system W)
        initial_state initial_counters (VASTransitionTarget original)
        (rule_child_projection rule W child next)).
    { eapply direct_vas_reach_trans; eauto. }
    assert (Hfuture' : forall later,
        (proj1_sig (Fin.to_nat child) < proj1_sig (Fin.to_nat later))%nat ->
        rule_child_projection rule W later next =
          nvec_zero (rule_block_width W)).
    { intros later Hlt.
      transitivity (rule_child_projection rule W later source).
      - symmetry. eapply rule_block_step_preserves_other_child; [|exact H1].
        intro Heq. subst later. lia.
      - apply Hfuture. exact Hlt. }
    exact (IHHprefix initial_state initial_counters Hinitial Hcurrent' Hfuture').
  - subst state.
    assert (Hactive_next :
        (proj1_sig (Fin.to_nat child) <
         proj1_sig (Fin.to_nat next_child))%nat).
    { pose proof (fin_successor_some_value _ _ _ H0). lia. }
    assert (Hnext_source : rule_child_projection rule W next_child source =
        nvec_zero (rule_block_width W)) by (apply Hfuture; exact Hactive_next).
    assert (Hnext_target : rule_child_projection rule W next_child next =
        snd config).
    { pose proof (f_equal (rule_child_zprojection rule W next_child) H2) as Hp.
      cbn in Hp. rewrite rule_child_zprojection_block_same,
        rule_child_zprojection_step_action in Hp.
      rewrite nvec_to_zvec_is_step_from_zero in Hp.
      rewrite Hnext_source in Hp.
      symmetry. eapply step_action_deterministic. exact Hp. }
    assert (Hfuture_next : forall later,
        (proj1_sig (Fin.to_nat next_child) <
         proj1_sig (Fin.to_nat later))%nat ->
        rule_child_projection rule W later next =
          nvec_zero (rule_block_width W)).
    { intros later Hlt.
      transitivity (rule_child_projection rule W later source).
      - symmetry. eapply rule_block_step_preserves_other_child; [|exact H2].
        intro Heq. subst later. lia.
      - apply Hfuture. lia. }
    assert (Hnext_refl : DirectVASReach (section_system W)
        (fst config) (snd config) (fst config)
        (rule_child_projection rule W next_child next)).
    { rewrite Hnext_target. constructor. }
    assert (Hconfig_in : List.In (fst config, snd config)
        (section_initial_configs W)).
    { destruct config. exact H1. }
    destruct (IHHprefix (fst config) (snd config) Hconfig_in
      Hnext_refl Hfuture_next)
      as [executions [Hnonempty [Hhead [Hconsecutive Hmatches]]]].
    destruct executions as [|first rest]; [exfalso; apply Hnonempty; reflexivity|].
    cbn in Hhead. injection Hhead as Hfirst.
    pose (current := {| raw_child_index := child;
       raw_child_initial_state := initial_state;
       raw_child_initial_counters := initial_counters;
       raw_child_endpoint := rule_child_projection rule W child source;
       raw_child_initial_in := Hinitial;
       raw_child_reach := Hcurrent |}).
    exists (current :: first :: rest). split; [discriminate|].
    split; [reflexivity|]. split.
    + cbn. rewrite Hfirst. constructor; [exact H0|].
      rewrite <- Hfirst. exact Hconsecutive.
    + constructor; [|exact Hmatches]. unfold raw_child_matches_collect, current.
      cbn. transitivity (rule_child_projection rule W child next).
      * eapply rule_block_step_preserves_other_child; [|exact H2].
        intro Heq. rewrite Heq in Hactive_next. lia.
      * apply rule_copy_prefix_preserves_prior_child with
          (active := next_child) (state := fst config).
        -- exact Hactive_next.
        -- exact Hprefix.
  - subst state.
    pose (current := {| raw_child_index := child;
       raw_child_initial_state := initial_state;
       raw_child_initial_counters := initial_counters;
       raw_child_endpoint := rule_child_projection rule W child source;
       raw_child_initial_in := Hinitial;
       raw_child_reach := Hcurrent |}).
    exists [current]. split; [discriminate|].
    split; [reflexivity|]. split.
    + cbn. constructor. exact H0.
    + constructor; [|constructor]. unfold raw_child_matches_collect, current.
      cbn. eapply rule_zero_step_preserves_child. exact H1.
Qed.

Definition fin_value {count} (index : Fin.t count) : nat :=
  proj1_sig (Fin.to_nat index).

Lemma consecutive_fin_value_sequence : forall count
    (indices : list (Fin.t count)),
    ConsecutiveFin indices ->
    exists start,
      List.map fin_value indices = List.seq start (List.length indices) /\
      (start + List.length indices = count)%nat.
Proof.
  intros count indices Hconsecutive. induction Hconsecutive.
  - exists (fin_value index). split; [reflexivity|].
    pose proof (fin_successor_none_value count index H) as Hnone.
    assert (Hbound : (fin_value index < count)%nat).
    { unfold fin_value. exact (proj2_sig (Fin.to_nat index)). }
    apply Nat.nlt_ge in Hnone.
    cbn. unfold fin_value in Hbound, Hnone |- *. lia.
  - destruct IHHconsecutive as [start [Hsequence Hlength]].
    exists (fin_value first). split.
    + cbn. pose proof (fin_successor_some_value count first second H) as Hvalue.
      cbn in Hsequence. injection Hsequence as Hstart Htail.
      unfold fin_value in *. subst start. rewrite Hvalue.
      rewrite Htail, Hvalue. reflexivity.
    + cbn in Hsequence. injection Hsequence as Hstart _.
      pose proof (fin_successor_some_value count first second H) as Hvalue.
      unfold fin_value in *. subst start. cbn in Hlength |- *. lia.
Qed.

Lemma map_succ_seq : forall start count,
    List.map S (List.seq start count) = List.seq (S start) count.
Proof.
  intros start count. revert start. induction count; intro start; cbn;
    [reflexivity|]. f_equal. apply IHcount.
Qed.

Lemma all_fin_values : forall count,
    List.map (@fin_value count) (all_fin count) = List.seq 0 count.
Proof.
  induction count as [|count IH]; cbn; [reflexivity|].
  f_equal. rewrite List.map_map.
  assert (Hmap : List.map (fun index : Fin.t count => fin_value (Fin.FS index))
      (all_fin count) =
    List.map S (List.map (@fin_value count) (all_fin count))).
  { rewrite List.map_map. apply List.map_ext. intro index.
    unfold fin_value. rewrite fin_to_nat_FS_value. reflexivity. }
  rewrite Hmap, IH, map_succ_seq. reflexivity.
Qed.

Lemma fin_value_map_injective : forall count (left right : list (Fin.t count)),
    List.map fin_value left = List.map fin_value right -> left = right.
Proof.
  intros count left. induction left as [|head tail IH]; intros right Heq;
    destruct right as [|head' tail']; cbn in Heq; try discriminate; [reflexivity|].
  injection Heq as Hhead Htail. f_equal.
  - apply Fin.to_nat_inj. exact Hhead.
  - apply IH. exact Htail.
Qed.

Lemma consecutive_fin_from_first : forall count (indices : list (Fin.t count))
    (first : Fin.t count),
    ConsecutiveFin indices ->
    List.hd_error indices = Some first ->
    fin_value first = 0%nat ->
    indices = all_fin count.
Proof.
  intros count indices first Hconsecutive Hhead Hfirst.
  destruct (consecutive_fin_value_sequence count indices Hconsecutive)
    as [start [Hsequence Hlength]].
  destruct indices as [|head tail]; [discriminate|].
  cbn in Hhead. injection Hhead as ->. cbn in Hsequence.
  pose proof Hsequence as Hsequence_all.
  injection Hsequence as Hstart Htail. rewrite Hfirst in Hstart. subst start.
  change (List.length (first :: tail) = count) in Hlength.
  assert (Hlen : List.length (first :: tail) = count) by exact Hlength.
  apply fin_value_map_injective.
  change (fin_value first :: List.map fin_value tail =
    List.map fin_value (all_fin count)).
  rewrite all_fin_values, Hfirst.
  replace (List.seq 0 count) with
      (List.seq 0 (List.length (first :: tail))) by now rewrite Hlen.
  rewrite Hfirst in Hsequence_all. exact Hsequence_all.
Qed.

Lemma rule_block_step_preserves_main : forall d q (rule : SRule d q)
    (W : VASSSection d q) child action source target,
    rule_block_zvec rule W child action = StepAction source target ->
    rule_main_projection rule W source = rule_main_projection rule W target.
Proof.
  intros d q rule W child action source target Hstep.
  pose proof (f_equal (rule_main_zprojection rule W) Hstep) as H.
  rewrite rule_main_zprojection_block,
    rule_main_zprojection_step_action in H.
  now apply step_action_zero_source in H.
Qed.

Lemma rule_zero_step_preserves_main : forall d q (rule : SRule d q)
    (W : VASSSection d q) source target,
    zvec_zero (d + rule_image_aux_dimension rule W) =
      StepAction source target ->
    rule_main_projection rule W source = rule_main_projection rule W target.
Proof.
  intros d q rule W source target Hstep.
  apply step_action_zero_source in Hstep. now subst target.
Qed.

Lemma rule_copy_prefix_preserves_main : forall d q (rule : SRule d q)
    (W : VASSSection d q) child state source collect,
    RuleCopyPrefix rule W child state source collect ->
    rule_main_projection rule W source = rule_main_projection rule W collect.
Proof.
  intros d q rule W child state source collect Hprefix.
  induction Hprefix.
  - transitivity (rule_main_projection rule W next).
    + eapply rule_block_step_preserves_main. exact H1.
    + exact IHHprefix.
  - transitivity (rule_main_projection rule W next).
    + eapply rule_block_step_preserves_main. exact H2.
    + exact IHHprefix.
  - eapply rule_zero_step_preserves_main. exact H1.
Qed.

Lemma add_displacement_of_step_action : forall d (delta : ZVec d)
    values target,
    delta = StepAction (nvec_sum values) target ->
    add_displacement delta values = Some target.
Proof.
  intros d delta values target ->. unfold add_displacement.
  replace (zvec_add (StepAction (nvec_sum values) target)
      (nvec_to_zvec (nvec_sum values))) with (nvec_to_zvec target).
  - apply zvec_to_nvec_of_nvec.
  - rewrite (zvec_add_comm d (StepAction (nvec_sum values) target)
      (nvec_to_zvec (nvec_sum values))).
    apply step_action_equation.
Qed.

Definition raw_child_visible {d q} (rule : SRule d q)
    (W : VASSSection d q) (execution : RawRuleChildExecution rule W) :
    NVec d := fst (Vector.splitat d (raw_child_endpoint rule W execution)).

Definition raw_child_config {d q} (rule : SRule d q)
    (W : VASSSection d q) (execution : RawRuleChildExecution rule W) :
    Mell.BVASS.Stateful.SConfig d q :=
  (rule_required_state rule (raw_child_index rule W execution),
   raw_child_visible rule W execution).

Lemma raw_matches_visible_map : forall d q (rule : SRule d q)
    (W : VASSSection d q) collect executions,
    List.Forall (raw_child_matches_collect rule W collect) executions ->
    List.map
      (fun execution => rule_child_visible_projection rule W
        (raw_child_index rule W execution) collect) executions =
    List.map (raw_child_visible rule W) executions.
Proof.
  intros d q rule W collect executions Hmatches. induction Hmatches; cbn;
    [reflexivity|]. f_equal; [|exact IHHmatches].
  unfold raw_child_matches_collect in H. unfold raw_child_visible,
    rule_child_visible_projection. now rewrite <- H.
Qed.

Theorem compile_rule_image_sound : forall d q (rule : SRule d q)
    (W : VASSSection d q) state counters,
    VASSSectionReach (compile_rule_image rule W) state counters ->
    OrderedRuleImage rule (VASSSectionReach W) state counters.
Proof.
  intros d q rule W state counters
    [machine_initial_state [machine_initial_counters [Hinitial Hreach]]].
  apply List.in_map_iff in Hinitial as [config [Hconfig Hconfig_in]].
  destruct config as [initial_state initial_counters]. cbn in Hconfig.
  injection Hconfig as Hmachine_state Hmachine_counters.
  subst machine_initial_state machine_initial_counters.
  apply vas_reach_direct_iff in Hreach.
  destruct (rule_copy_to_output_phase_decomposition d q rule W
    (first_child rule) initial_state
    (rule_block_nvec rule W 0 initial_counters) state
    (section_target_vector (compile_rule_image rule W) counters) Hreach)
    as [collect [Hprefix Hsuffix]].
  assert (Hinitial_projection : rule_child_projection rule W
      (first_child rule) (rule_block_nvec rule W 0 initial_counters) =
      initial_counters).
  { rewrite <- first_child_value at 1. apply rule_child_projection_block_same. }
  assert (Hfuture : forall later,
      (proj1_sig (Fin.to_nat (first_child rule)) <
       proj1_sig (Fin.to_nat later))%nat ->
      rule_child_projection rule W later
        (rule_block_nvec rule W 0 initial_counters) =
        nvec_zero (rule_block_width W)).
  { intros later Hlt. rewrite <- first_child_value at 1.
    apply rule_child_projection_block_other. intro Heq. subst later. lia. }
  assert (Hinitial_reach : DirectVASReach (section_system W)
      initial_state initial_counters initial_state
      (rule_child_projection rule W (first_child rule)
        (rule_block_nvec rule W 0 initial_counters))).
  { rewrite Hinitial_projection. constructor. }
  destruct (rule_copy_prefix_parse d q rule W (first_child rule)
      initial_state (rule_block_nvec rule W 0 initial_counters) collect
      initial_state initial_counters Hconfig_in Hinitial_reach Hfuture Hprefix)
    as [executions [Hexecutions_nonempty [Hexecutions_head
      [Hexecutions_consecutive Hexecutions_match]]]].
  assert (Hindices : List.map (raw_child_index rule W) executions =
      all_fin (rule_child_count rule)).
  { eapply consecutive_fin_from_first; eauto. apply first_child_value. }
  destruct (rule_collect_to_output_inv d q rule W collect state
      (section_target_vector (compile_rule_image rule W) counters) Hsuffix)
    as [before [Hcollect [Hfinal_action Houtput]]].
  destruct (rule_final_step_inv d q rule W before counters Hfinal_action)
    as [Hdelta Hchildren_zero].
  assert (Hmain_collect : rule_main_projection rule W collect = nvec_zero d).
  { transitivity (rule_main_projection rule W
        (rule_block_nvec rule W 0 initial_counters)).
    - symmetry. eapply rule_copy_prefix_preserves_main. exact Hprefix.
    - apply rule_main_projection_block. }
  assert (Hmass_collect : rule_collect_mass rule W collect =
      nvec_sum (List.map (raw_child_visible rule W) executions)).
  { unfold rule_collect_mass. rewrite Hmain_collect,
      nvec_add_zero_left_stateful, nvec_sum_rsum_stateful.
    rewrite <- Hindices, List.map_map.
    rewrite raw_matches_visible_map by exact Hexecutions_match.
    symmetry. apply nvec_sum_rsum_stateful. }
  assert (Hmass_before : rule_collect_mass rule W before =
      nvec_sum (List.map (raw_child_visible rule W) executions)).
  { rewrite <- Hmass_collect. symmetry.
    apply rule_collect_reach_preserves_mass. exact Hcollect. }
  assert (Hmain_before : rule_main_projection rule W before =
      nvec_sum (List.map (raw_child_visible rule W) executions)).
  { rewrite <- Hmass_before. unfold rule_collect_mass.
    assert (Hzero_children : nvec_sum (List.map
        (fun child => rule_child_visible_projection rule W child before)
        (all_fin (rule_child_count rule))) = nvec_zero d).
    { rewrite nvec_sum_rsum_stateful.
      transitivity (nvec_rsum_stateful
        (List.map (fun _ : Fin.t (rule_child_count rule) => nvec_zero d)
          (all_fin (rule_child_count rule)))).
      - apply f_equal. apply List.map_ext. intro child.
        unfold rule_child_visible_projection. rewrite Hchildren_zero.
        assert (Hzero : nvec_zero (rule_block_width W) =
            Vector.append (nvec_zero d) (nvec_zero (section_aux_dimension W))).
        { unfold rule_block_width. apply nvec_zero_append. }
        rewrite Hzero, VectorSpec.splitat_append. reflexivity.
      - apply nvec_rsum_map_zero. }
    rewrite Hzero_children, nvec_add_zero. reflexivity. }
  assert (Happly : add_displacement (rule_delta rule)
      (List.map (raw_child_visible rule W) executions) = Some counters).
  { apply add_displacement_of_step_action. rewrite <- Hmain_before. exact Hdelta. }
  exists (List.map (raw_child_config rule W) executions).
  repeat split.
  - apply List.Forall_map. eapply List.Forall_impl;
      [|exact Hexecutions_match].
    intros execution Hmatch. unfold raw_child_config. cbn.
    exists (raw_child_initial_state rule W execution),
      (raw_child_initial_counters rule W execution). split.
    + apply raw_child_initial_in.
    + apply vas_reach_direct_iff.
      assert (Haux : rule_child_aux_projection rule W
          (raw_child_index rule W execution) collect =
          nvec_zero (section_aux_dimension W)).
      { transitivity (rule_child_aux_projection rule W
            (raw_child_index rule W execution) before).
        - apply rule_collect_reach_preserves_child_aux. exact Hcollect.
        - unfold rule_child_aux_projection.
          rewrite Hchildren_zero.
          assert (Hzero : nvec_zero (rule_block_width W) =
              Vector.append (nvec_zero d)
                (nvec_zero (section_aux_dimension W))).
          { unfold rule_block_width. apply nvec_zero_append. }
          rewrite Hzero, VectorSpec.splitat_append. reflexivity. }
      assert (Hendpoint : raw_child_endpoint rule W execution =
          section_target_vector W (raw_child_visible rule W execution)).
      { unfold raw_child_matches_collect in Hmatch.
        unfold raw_child_visible, section_target_vector.
        destruct (Vector.splitat d (raw_child_endpoint rule W execution))
          as [visible auxiliary] eqn:Hsplit.
        apply VectorSpec.append_splitat in Hsplit.
        rewrite Hsplit. cbn [fst snd]. f_equal.
        unfold rule_child_aux_projection in Haux.
        rewrite <- Hmatch in Haux. rewrite Hsplit,
          VectorSpec.splitat_append in Haux. exact Haux. }
      rewrite <- Hendpoint. apply raw_child_reach.
  - rewrite List.map_map. change (List.map
      (fun execution => rule_required_state rule
        (raw_child_index rule W execution)) executions = input_states rule).
    rewrite <- List.map_map, Hindices. apply rule_required_states_all_fin.
  - rewrite List.map_map. change (add_displacement (rule_delta rule)
      (List.map (raw_child_visible rule W) executions) = Some counters).
    exact Happly.
  - exact Houtput.
Qed.

Theorem compile_rule_image_correct : forall d q (rule : SRule d q)
    (W : VASSSection d q) state counters,
    VASSSectionReach (compile_rule_image rule W) state counters <->
    OrderedRuleImage rule (VASSSectionReach W) state counters.
Proof.
  intros. split; [apply compile_rule_image_sound|apply compile_rule_image_complete].
Qed.

Definition branching_rules {d q} (B : SBVAS d q) : list (SRule d q) :=
  List.filter (fun rule => Nat.leb 2 (List.length (input_states rule)))
    (stateful_rules B).

Definition compile_branching_images {d q} (B : SBVAS d q)
    (W : VASSSection d q) : VASSSection d q :=
  section_finite_union (List.map (fun rule => compile_rule_image rule W)
    (branching_rules B)).

Theorem compile_branching_images_correct : forall d q (B : SBVAS d q)
    (W : VASSSection d q) state counters,
    VASSSectionReach (compile_branching_images B W) state counters <->
    BranchingImages B (VASSSectionReach W) state counters.
Proof.
  intros d q B W state counters. unfold compile_branching_images.
  rewrite section_finite_union_reach_iff. split.
  - intros [section [Hsection Hreach]].
    apply List.in_map_iff in Hsection as [rule [<- Hrule]].
    unfold branching_rules in Hrule. apply List.filter_In in Hrule
      as [Hrule Hbranch].
    apply Nat.leb_le in Hbranch.
    exists rule. apply ordered_rule_image; auto.
    now apply compile_rule_image_sound in Hreach.
  - intros [rule Himage].
    apply rule_image_ordered in Himage as [Hrule [Hbranch Hordered]].
    exists (compile_rule_image rule W). split.
    + apply List.in_map_iff. exists rule. split; [reflexivity|].
      unfold branching_rules. apply List.filter_In.
      split; [exact Hrule|]. now apply Nat.leb_le.
    + now apply compile_rule_image_complete.
Qed.

Definition compile_bounded_seed {d q} (B : SBVAS d q)
    (W : VASSSection d q) : VASSSection d q :=
  vass_section_union (initial_vass_section (initial_configs B))
    (compile_branching_images B W).

Theorem compile_bounded_seed_correct : forall d q (B : SBVAS d q)
    (W : VASSSection d q) state counters,
    VASSSectionReach (compile_bounded_seed B W) state counters <->
    List.In (state, counters) (initial_configs B) \/
    BranchingImages B (VASSSectionReach W) state counters.
Proof.
  intros. unfold compile_bounded_seed. rewrite vass_section_union_reach_iff,
    initial_vass_section_reach_iff, compile_branching_images_correct.
  reflexivity.
Qed.

Fixpoint compile_bounded_vass_section {d q} (B : SBVAS d q)
    (bound : nat) : VASSSection d q :=
  match bound with
  | O => compile_unary_closure B (initial_vass_section (initial_configs B))
  | S previous =>
      compile_unary_closure B
        (compile_bounded_seed B (compile_bounded_vass_section B previous))
  end.

Definition DepthSeed {d q} (B : SBVAS d q) (bound : nat)
    (state : Fin.t q) (counters : NVec d) : Prop :=
  match bound with
  | O => List.In (state, counters) (initial_configs B)
  | S previous => BoundedSeed B previous state counters
  end.

Lemma valid_sruns_reach_depth : forall d q (B : SBVAS d q) runs bound,
    ValidSRuns B runs ->
    (runs_max_branching_depth runs <= bound)%nat ->
    List.Forall (fun config =>
      ReachDepth B bound (fst config) (snd config)) (sruns_configs runs).
Proof.
  intros d q B runs bound Hvalid. induction Hvalid; intro Hdepth; cbn.
  - constructor.
  - constructor.
    + destruct (root_config run) as [state counters] eqn:Hroot.
      exists run. repeat split; auto. cbn in Hdepth.
      eapply Nat.le_trans; [apply Nat.le_max_l|exact Hdepth].
    + apply IHHvalid. cbn in Hdepth.
      eapply Nat.le_trans; [apply Nat.le_max_r|exact Hdepth].
Qed.

Lemma valid_run_depth_decompose : forall d q (B : SBVAS d q) run,
    ValidSRun B run ->
    forall bound,
      (branching_depth run <= bound)%nat ->
      UnaryClosure B (DepthSeed B bound)
        (fst (root_config run)) (snd (root_config run)).
Proof.
  intros d q B run.
  remember (run_node_count run) as measure eqn:Hmeasure.
  revert run Hmeasure.
  induction measure using lt_wf_ind;
    intros run Hmeasure Hvalid bound Hdepth.
  destruct run as [config|rule children result].
  - inversion Hvalid; subst. destruct config as [state counters].
    exists state, counters. split.
    + destruct bound; cbn; [exact H1|now left].
    + constructor.
  - inversion Hvalid as
      [|? ? ? Hrule Hchildren Hstates Happly Houtput]; subst.
    destruct children as [|child tail].
    + cbn in Hstates. apply Permutation_nil in Hstates.
      exfalso. eapply input_nonempty. exact Hstates.
    + destruct tail as [|second rest].
      * inversion Hchildren as [|? ? Hchild Hnil]; subst.
        apply Permutation_length_1_inv in Hstates.
        destruct result as [result_state result_counters].
        cbn in Houtput. subst result_state.
        assert (Hchild_measure :
            (run_node_count child < run_node_count
              (srun_node rule (sruns_cons child sruns_nil)
                (output_state rule, result_counters)))%nat).
        { apply direct_child_node_count_lt. constructor. }
        assert (Hchild_depth : (branching_depth child <= bound)%nat).
        { cbn in Hdepth. exact Hdepth. }
        destruct (H (run_node_count child) ltac:(lia) child eq_refl
          Hchild bound Hchild_depth)
          as [source_state [source [Hseed Hsource_reach]]].
        exists source_state, source. split; [exact Hseed|].
        eapply direct_vas_reach_trans; [exact Hsource_reach|].
        eapply unary_rule_application with (rule := rule).
        -- exact Hrule.
        -- exact Hstates.
        -- cbn in Happly. exact Happly.
      * destruct bound as [|previous].
        -- cbn in Hdepth. lia.
        -- destruct result as [result_state result_counters].
           cbn in Houtput. subst result_state.
           exists (output_state rule), result_counters. split.
           ++ cbn. right. exists rule. repeat split.
              ** exact Hrule.
              ** pose proof (Permutation_length Hstates) as Harity.
                 cbn in Harity. lia.
              ** exists (sruns_configs
                   (sruns_cons child (sruns_cons second rest))).
                 repeat split.
                 --- eapply valid_sruns_reach_depth with (bound := previous);
                       [exact Hchildren|].
                     rewrite branching_depth_node_formula in Hdepth.
                     assert (Hleb : Nat.leb 2
                       (List.length (sruns_configs
                         (sruns_cons child (sruns_cons second rest)))) = true).
                     { apply Nat.leb_le. cbn. lia. }
                     rewrite Hleb in Hdepth. lia.
                 --- exact Hstates.
                 --- exact Happly.
           ++ constructor.
Qed.

Theorem reach_depth_decomposition : forall d q (B : SBVAS d q)
    bound state counters,
    ReachDepth B bound state counters <->
    UnaryClosure B (DepthSeed B bound) state counters.
Proof.
  intros d q B bound state counters. split.
  - intros [run [Hvalid [Hroot Hdepth]]].
    pose proof (valid_run_depth_decompose d q B run Hvalid bound Hdepth) as H.
    now rewrite Hroot in H.
  - destruct bound as [|previous].
    + intros [source_state [source [Hinitial Hreach]]].
      destruct (unary_direct_reach_wrap d q B source_state source state counters
        (srun_leaf (source_state, source)) ltac:(constructor; exact Hinitial)
        eq_refl Hreach) as [run [Hvalid [Hroot Hsame]]].
      exists run. repeat split; auto. cbn in Hsame. lia.
    + apply unary_closure_bounded_seed_sound.
Qed.

Lemma rule_image_extensional : forall d q (B : SBVAS d q) rule
    (left right : Fin.t q -> NVec d -> Prop),
    (forall state counters, left state counters <-> right state counters) ->
    forall state counters,
      RuleImage B rule left state counters <->
      RuleImage B rule right state counters.
Proof.
  intros d q B rule left right Hequiv state counters. split.
  - intros [Hrule [Harity [children [Hchildren Hrest]]]].
    split; [exact Hrule|]. split; [exact Harity|]. exists children. split.
    + eapply List.Forall_impl; [|exact Hchildren].
      intros [child_state child_counters] Hchild. apply Hequiv. exact Hchild.
    + exact Hrest.
  - intros [Hrule [Harity [children [Hchildren Hrest]]]].
    split; [exact Hrule|]. split; [exact Harity|]. exists children. split.
    + eapply List.Forall_impl; [|exact Hchildren].
      intros [child_state child_counters] Hchild. apply Hequiv. exact Hchild.
    + exact Hrest.
Qed.

Lemma branching_images_extensional : forall d q (B : SBVAS d q)
    (left right : Fin.t q -> NVec d -> Prop),
    (forall state counters, left state counters <-> right state counters) ->
    forall state counters,
      BranchingImages B left state counters <->
      BranchingImages B right state counters.
Proof.
  intros d q B left right Hequiv state counters. split;
    intros [rule Hrule]; exists rule;
    apply (rule_image_extensional d q B rule left right Hequiv); assumption.
Qed.

Lemma unary_closure_extensional : forall d q (B : SBVAS d q)
    (left right : Fin.t q -> NVec d -> Prop),
    (forall state counters, left state counters <-> right state counters) ->
    forall state counters,
      UnaryClosure B left state counters <->
      UnaryClosure B right state counters.
Proof.
  intros d q B left right Hequiv state counters. split.
  - intros [source_state [source [Hsource Hreach]]].
    exists source_state, source. split; [apply Hequiv; exact Hsource|exact Hreach].
  - intros [source_state [source [Hsource Hreach]]].
    exists source_state, source. split; [apply Hequiv; exact Hsource|exact Hreach].
Qed.

Theorem bounded_vass_section_correct : forall d q (B : SBVAS d q) bound,
    BoundedSectionCorrect B bound (compile_bounded_vass_section B bound).
Proof.
  intros d q B bound. induction bound as [|previous IH];
    intros state counters.
  - cbn [compile_bounded_vass_section].
    rewrite compile_unary_closure_reach_iff,
      reach_depth_decomposition. cbn [DepthSeed].
    apply unary_closure_extensional.
    apply initial_vass_section_reach_iff.
  - cbn [compile_bounded_vass_section].
    rewrite compile_unary_closure_reach_iff,
      reach_depth_decomposition. cbn [DepthSeed].
    apply unary_closure_extensional. intros seed_state seed_counters.
    rewrite compile_bounded_seed_correct. unfold BoundedSeed.
    split; intros [Hinitial|Hbranch]; [now left|right|now left|right].
    + apply (proj1 (branching_images_extensional d q B
        (VASSSectionReach (compile_bounded_vass_section B previous))
        (ReachDepth B previous) IH seed_state seed_counters)).
      exact Hbranch.
    + apply (proj2 (branching_images_extensional d q B
        (VASSSectionReach (compile_bounded_vass_section B previous))
        (ReachDepth B previous) IH seed_state seed_counters)).
      exact Hbranch.
Qed.

Theorem lemma_11_bounded_depth_vass_section :
  forall d q (B : SBVAS d q) bound state counters,
    VASSSectionReach (compile_bounded_vass_section B bound) state counters <->
    exists rho,
      ValidSRun B rho /\
      root_config rho = (state, counters) /\
      (branching_depth rho <= bound)%nat.
Proof.
  intros. apply bounded_vass_section_correct.
Qed.
