From Coq Require Import Fin Lia List Vector VectorSpec ZArith
  Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Closure Presentation.
From Mell.BVAS Require Import System Runs RunOrder.
From Mell.BVASS Require Import Stateful AlmostSemilinear
  BoundedVASSSection.
From Mell.Reduction Require Import StateErasure.
From Mell.VAS Require Import Transformer Intraproductions RelationCone
  AsymptoticRelation AlmostSemilinear SemilinearRelationDecomposition
  AlmostSemilinearProjection AlmostSemilinearCoordinateProjection Corollary63
  StatefulAlmostSemilinear.

Import ListNotations.
Module StdVector := Coq.Vectors.Vector.
Close Scope Z_scope.
Close Scope Q_scope.

(** A run with one distinguished leaf.  The distinguished occurrence is a
    constructor of the derivation, hence remains distinguishable from an
    ordinary initial leaf carrying the same vector. *)
Inductive SpecialLeafReach {d} (system : IBVAS d) : NVec d -> NVec d -> Prop :=
| special_leaf : forall input,
    SpecialLeafReach system input input
| special_action : forall input action prefix middle suffix output,
    List.In action (system_actions system) ->
    List.Forall (Reach system) prefix ->
    SpecialLeafReach system input middle ->
    List.Forall (Reach system) suffix ->
    apply_action action (prefix ++ middle :: suffix) = Some output ->
    SpecialLeafReach system input output.

(** One-state presentation of an [IBVAS].  This bridge is deliberately
    independent of state erasure: it only equips every existing node with the
    unique state. *)
Definition one_state_rule {d} (action : Action d) : SRule d 1.
Proof.
  refine {| input_states := List.repeat Fin.F1 (action_arity action);
            input_nonempty := _;
            output_state := Fin.F1;
            rule_delta := action_offset action |}.
  intro Hnil.
  apply (f_equal (@List.length (Fin.t 1))) in Hnil.
  rewrite repeat_length in Hnil. cbn in Hnil.
  pose proof (action_arity_positive action). lia.
Defined.

Definition one_state_sbvas {d} (system : IBVAS d) : SBVAS d 1 :=
  {| initial_configs := List.map (fun value => (Fin.F1, value))
       (initial_vectors system);
     stateful_rules := List.map one_state_rule (system_actions system) |}.

Lemma one_state_input_states : forall d (action : Action d),
    input_states (one_state_rule action) =
      List.repeat Fin.F1 (action_arity action).
Proof. reflexivity. Qed.

Lemma fin1_unique : forall state : Fin.t 1, state = Fin.F1.
Proof.
  intro state. refine (Fin.caseS' state (fun state => state = Fin.F1)
    eq_refl _). intro impossible.
  exact (Fin.case0 (fun index => Fin.FS index = Fin.F1) impossible).
Qed.

Lemma permutation_repeat_fin1_iff : forall (states : list (Fin.t 1)) count,
    Permutation states (List.repeat Fin.F1 count) <-> length states = count.
Proof.
  intros states count. split.
  - intro H. apply Permutation_length in H. now rewrite repeat_length in H.
  - revert count. induction states as [|state tail IH]; intros count Hlength.
    + destruct count; [constructor|cbn in Hlength; discriminate].
    + destruct count as [|count]; [cbn in Hlength; discriminate|].
      cbn in Hlength. rewrite (fin1_unique state). constructor.
      apply IH. lia.
Qed.

Lemma one_state_reach_forward_mut : forall d (system : IBVAS d),
  (forall value, Reach system value ->
    SReach (one_state_sbvas system) Fin.F1 value) /\
  (forall values, ReachChildren system values ->
    SReachChildren (one_state_sbvas system)
      (List.map (fun value => (Fin.F1, value)) values)).
Proof.
  intros d system. apply Reach_mutind.
  - intros index value Hinitial. apply sreach_initial.
    apply in_map. now apply nth_error_In in Hinitial.
  - intros index action children value Haction Hchildren IHchildren Happly.
    eapply sreach_rule with (rule := one_state_rule action)
      (child_configs := List.map (fun child => (Fin.F1, child)) children).
    + apply in_map. now apply nth_error_In in Haction.
    + exact IHchildren.
    + rewrite List.map_map. cbn. apply permutation_repeat_fin1_iff.
      rewrite map_length. unfold apply_action in Happly.
      destruct (Nat.eqb (length children) (action_arity action)) eqn:E;
        try discriminate. now apply Nat.eqb_eq in E.
    + assert (Echildren :
          List.map snd
            (List.map (fun child => (@Fin.F1 0, child)) children) = children).
      { clear Haction Hchildren IHchildren Happly.
        induction children as [|child tail IH]; cbn; [reflexivity|].
        f_equal. exact IH. }
      rewrite Echildren. cbn. unfold apply_action in Happly.
      destruct (Nat.eqb (length children) (action_arity action));
        try discriminate. exact Happly.
  - constructor.
  - intros value values Hvalue IHvalue Hvalues IHvalues. cbn.
    constructor; assumption.
Qed.

Lemma one_state_reach_forward : forall d (system : IBVAS d) value,
    Reach system value -> SReach (one_state_sbvas system) Fin.F1 value.
Proof. intros; now apply (proj1 (one_state_reach_forward_mut d system)). Qed.

Lemma one_state_reach_backward_mut : forall d (system : IBVAS d),
  (forall state value, SReach (one_state_sbvas system) state value ->
    Reach system value) /\
  (forall configs, SReachChildren (one_state_sbvas system) configs ->
    ReachChildren system (List.map snd configs)).
Proof.
  intros d system. apply SReach_mutind.
  - intros state counters Hinitial. unfold one_state_sbvas in Hinitial.
    cbn in Hinitial. apply in_map_iff in Hinitial as [initial [Heq Hin]].
    injection Heq as _ Evalue. subst counters.
    apply In_nth_error in Hin as [index Hindex].
    now apply reach_initial with (index := index).
  - intros rule child_configs result Hrule Hchildren IHchildren Hstates Happly.
    unfold one_state_sbvas in Hrule. cbn in Hrule.
    apply in_map_iff in Hrule as [action [Erule Hin]]. subst rule.
    apply In_nth_error in Hin as [index Hindex].
    eapply reach_action with (index := index) (action := action)
      (children := List.map snd child_configs).
    + exact Hindex.
    + exact IHchildren.
    + unfold apply_action. assert (Hlength :
          length (List.map snd child_configs) = action_arity action).
      { rewrite length_map.
        change (Permutation (List.map fst child_configs)
          (List.repeat Fin.F1 (action_arity action))) in Hstates.
        apply Permutation_length in Hstates.
        rewrite List.map_length, repeat_length in Hstates. exact Hstates. }
      rewrite Hlength, Nat.eqb_refl. exact Happly.
  - constructor.
  - intros state counters children Hhead IHhead Htail IHtail. cbn.
    constructor; assumption.
Qed.

Lemma one_state_reach_backward : forall d (system : IBVAS d) state value,
    SReach (one_state_sbvas system) state value -> Reach system value.
Proof. intros; now apply (proj1 (one_state_reach_backward_mut d system) state). Qed.

Theorem one_state_reach_iff : forall d (system : IBVAS d) value,
    Reach system value <->
    SReach (one_state_sbvas system) Fin.F1 value.
Proof.
  intros. split; [apply one_state_reach_forward|apply one_state_reach_backward].
Qed.

(** Coordinates of the doubled construction are
    [(marker_a,marker_b), (input,output)]. *)
Definition doubled_dimension (d : nat) := 2 + (d + d).

Definition marker00 : NVec 2 :=
  StdVector.cons nat 0 1 (StdVector.cons nat 0 0 (StdVector.nil nat)).
Definition marker10 : NVec 2 :=
  StdVector.cons nat 1 1 (StdVector.cons nat 0 0 (StdVector.nil nat)).
Definition marker01 : NVec 2 :=
  StdVector.cons nat 0 1 (StdVector.cons nat 1 0 (StdVector.nil nat)).

Definition zmarker00 : ZVec 2 :=
  StdVector.cons Z 0%Z 1 (StdVector.cons Z 0%Z 0 (StdVector.nil Z)).
Definition zmarker_move_ab : ZVec 2 :=
  StdVector.cons Z (-1)%Z 1 (StdVector.cons Z 1%Z 0 (StdVector.nil Z)).
Definition zmarker_move_ba : ZVec 2 :=
  StdVector.cons Z 1%Z 1 (StdVector.cons Z (-1)%Z 0 (StdVector.nil Z)).

Lemma zmarker00_zero : zmarker00 = zvec_zero 2.
Proof. reflexivity. Qed.

Definition doubled_pack {d} (marker : NVec 2)
    (input output : NVec d) : NVec (doubled_dimension d) :=
  StdVector.append marker (npair_pack input output).

Definition doubled_marker {d} (value : NVec (doubled_dimension d)) : NVec 2 :=
  Vector.shiftin_left 2 (d + d) value.
Definition doubled_pair {d} (value : NVec (doubled_dimension d)) : NVec (d+d) :=
  Vector.shiftin_right 2 (d + d) value.
Definition doubled_input {d} (value : NVec (doubled_dimension d)) : NVec d :=
  npair_left (doubled_pair value).
Definition doubled_output {d} (value : NVec (doubled_dimension d)) : NVec d :=
  npair_right (doubled_pair value).

Lemma doubled_unpack_pack : forall d (marker : NVec 2)
    (input output : NVec d),
    doubled_marker (doubled_pack marker input output) = marker /\
    doubled_input (doubled_pack marker input output) = input /\
    doubled_output (doubled_pack marker input output) = output.
Proof.
  intros. unfold doubled_marker, doubled_input, doubled_output,
    doubled_pair, doubled_pack. rewrite shiftin_left_append,
    shiftin_right_append, npair_left_pack, npair_right_pack. auto.
Qed.

Lemma doubled_repack : forall d (value : NVec (doubled_dimension d)),
    doubled_pack (doubled_marker value) (doubled_input value)
      (doubled_output value) = value.
Proof.
  intros d value. unfold doubled_pack, doubled_marker, doubled_pair,
    doubled_input, doubled_output.
  rewrite npair_pack_split. apply append_shiftin.
Qed.

Lemma doubled_marker_zero : forall d,
    doubled_marker (nvec_zero (doubled_dimension d)) = nvec_zero 2.
Proof.
  intro d. unfold doubled_marker, doubled_dimension. rewrite nvec_zero_append.
  apply shiftin_left_append.
Qed.

Lemma doubled_input_zero : forall d,
    doubled_input (nvec_zero (doubled_dimension d)) = nvec_zero d.
Proof.
  intro d. unfold doubled_input, doubled_pair, doubled_dimension.
  rewrite (nvec_zero_append 2 (d + d)),
    shiftin_right_append, npair_left_zero. reflexivity.
Qed.

Lemma doubled_output_zero : forall d,
    doubled_output (nvec_zero (doubled_dimension d)) = nvec_zero d.
Proof.
  intro d. unfold doubled_output, doubled_pair, doubled_dimension.
  rewrite (nvec_zero_append 2 (d + d)),
    shiftin_right_append, npair_right_zero. reflexivity.
Qed.

Lemma doubled_marker_add : forall d
    (left right : NVec (doubled_dimension d)),
    doubled_marker (nvec_add left right) =
      nvec_add (doubled_marker left) (doubled_marker right).
Proof.
  intros d left right. unfold doubled_marker, doubled_dimension in *.
  destruct (StdVector.splitat 2 left) as [left_marker left_pair] eqn:Eleft.
  destruct (StdVector.splitat 2 right) as [right_marker right_pair] eqn:Eright.
  apply VectorSpec.append_splitat in Eleft, Eright. subst left right.
  rewrite nvec_add_append. repeat rewrite shiftin_left_append. reflexivity.
Qed.

Lemma doubled_input_add : forall d
    (left right : NVec (doubled_dimension d)),
    doubled_input (nvec_add left right) =
      nvec_add (doubled_input left) (doubled_input right).
Proof.
  intros d left right. unfold doubled_input, doubled_pair, doubled_dimension in *.
  destruct (StdVector.splitat 2 left) as [left_marker left_pair] eqn:Eleft.
  destruct (StdVector.splitat 2 right) as [right_marker right_pair] eqn:Eright.
  apply VectorSpec.append_splitat in Eleft, Eright. subst left right.
  rewrite nvec_add_append. repeat rewrite shiftin_right_append.
  apply npair_left_add.
Qed.

Lemma doubled_output_add : forall d
    (left right : NVec (doubled_dimension d)),
    doubled_output (nvec_add left right) =
      nvec_add (doubled_output left) (doubled_output right).
Proof.
  intros d left right. unfold doubled_output, doubled_pair, doubled_dimension in *.
  destruct (StdVector.splitat 2 left) as [left_marker left_pair] eqn:Eleft.
  destruct (StdVector.splitat 2 right) as [right_marker right_pair] eqn:Eright.
  apply VectorSpec.append_splitat in Eleft, Eright. subst left right.
  rewrite nvec_add_append. repeat rewrite shiftin_right_append.
  apply npair_right_add.
Qed.

Lemma doubled_marker_rsum : forall d
    (values : list (NVec (doubled_dimension d))),
    doubled_marker (nvec_rsum values) =
      nvec_rsum (List.map doubled_marker values).
Proof.
  intros d values; induction values as [|value values IH].
  - change (doubled_marker (nvec_zero (doubled_dimension d)) = nvec_zero 2).
    apply (doubled_marker_zero d).
  - change (doubled_marker (nvec_add value (nvec_rsum values)) =
      nvec_add (doubled_marker value)
        (nvec_rsum (List.map doubled_marker values))).
    now rewrite doubled_marker_add, IH.
Qed.

Lemma doubled_input_rsum : forall d
    (values : list (NVec (doubled_dimension d))),
    doubled_input (nvec_rsum values) =
      nvec_rsum (List.map doubled_input values).
Proof.
  intros d values; induction values as [|value values IH].
  - change (doubled_input (nvec_zero (doubled_dimension d)) = nvec_zero d).
    apply (doubled_input_zero d).
  - change (doubled_input (nvec_add value (nvec_rsum values)) =
      nvec_add (doubled_input value)
        (nvec_rsum (List.map doubled_input values))).
    now rewrite doubled_input_add, IH.
Qed.

Lemma doubled_output_rsum : forall d
    (values : list (NVec (doubled_dimension d))),
    doubled_output (nvec_rsum values) =
      nvec_rsum (List.map doubled_output values).
Proof.
  intros d values; induction values as [|value values IH].
  - change (doubled_output (nvec_zero (doubled_dimension d)) = nvec_zero d).
    apply (doubled_output_zero d).
  - change (doubled_output (nvec_add value (nvec_rsum values)) =
      nvec_add (doubled_output value)
        (nvec_rsum (List.map doubled_output values))).
    now rewrite doubled_output_add, IH.
Qed.

Lemma nvec_sum_doubled_blocks : forall d
    (values : list (NVec (doubled_dimension d))),
    nvec_sum values = doubled_pack
      (nvec_sum (List.map doubled_marker values))
      (nvec_sum (List.map doubled_input values))
      (nvec_sum (List.map doubled_output values)).
Proof.
  intros d values. rewrite <- (doubled_repack d (nvec_sum values)).
  repeat rewrite nvec_sum_rsum.
  now rewrite doubled_marker_rsum, doubled_input_rsum, doubled_output_rsum.
Qed.

Lemma zvec_pack_add : forall d (marker_delta : ZVec 2)
    (input_delta output_delta : ZVec d)
    marker input output marker' input' output',
    zvec_add
      (StdVector.append marker_delta
        (StdVector.append input_delta output_delta))
      (nvec_to_zvec (doubled_pack marker input output)) =
      nvec_to_zvec (doubled_pack marker' input' output') <->
    zvec_add marker_delta (nvec_to_zvec marker) = nvec_to_zvec marker' /\
    zvec_add input_delta (nvec_to_zvec input) = nvec_to_zvec input' /\
    zvec_add output_delta (nvec_to_zvec output) = nvec_to_zvec output'.
Proof.
  intros. unfold doubled_pack, doubled_dimension, npair_pack in *.
  rewrite !nvec_to_zvec_append,
    !zvec_add_append. split.
  - intro H. apply StdVector.append_inj in H as [Hmarker Hpair].
    apply StdVector.append_inj in Hpair as [Hinput Houtput]. auto.
  - intros [Hmarker [Hinput Houtput]]. now rewrite Hmarker, Hinput, Houtput.
Qed.


Definition zunit {d} (selected : Fin.t d) : ZVec d :=
  Vector.map Z.of_nat
    (Closure.nvec_tabulate d
      (fun index => if Fin.eq_dec index selected then 1 else 0)).

Definition nunit {d} (selected : Fin.t d) : NVec d :=
  Closure.nvec_tabulate d
    (fun index => if Fin.eq_dec index selected then 1 else 0).

Lemma zunit_nunit : forall d (selected : Fin.t d),
    zunit selected = nvec_to_zvec (nunit selected).
Proof. reflexivity. Qed.

Lemma zvec_add_nvec_commute : forall d (delta value : NVec d),
    zvec_add (nvec_to_zvec delta) (nvec_to_zvec value) =
      nvec_to_zvec (nvec_add value delta).
Proof.
  intros d delta value. apply (proj1 (StdVector.eq_nth_iff Z d _ _)).
  intros index index' <-. unfold zvec_add, nvec_to_zvec, nvec_add.
  repeat rewrite (StdVector.nth_map _ _ index index eq_refl).
  rewrite (StdVector.nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (StdVector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  rewrite Nat2Z.inj_add.
  repeat rewrite (StdVector.nth_map _ _ index index eq_refl).
  apply Z.add_comm.
Qed.

Definition doubled_lift_action {d} (action : Action d) :
    Action (doubled_dimension d).
Proof.
  refine {| action_arity := action_arity action;
            action_arity_positive := action_arity_positive action;
            action_offset := StdVector.append zmarker00
              (StdVector.append (zvec_zero d) (action_offset action)) |}.
Defined.

Definition doubled_move_action {d} (marker_delta : ZVec 2)
    (coordinate : Fin.t d) : Action (doubled_dimension d) :=
  {| action_arity := 1;
     action_arity_positive := Nat.lt_0_succ 0;
     action_offset := StdVector.append marker_delta
       (StdVector.append (zunit coordinate) (zunit coordinate)) |}.

Fixpoint doubled_all_fin (d : nat) : list (Fin.t d) :=
  match d with
  | 0 => []
  | S tail => Fin.F1 :: List.map Fin.FS (doubled_all_fin tail)
  end.

Definition doubled_system {d} (system : IBVAS d) :
    IBVAS (doubled_dimension d) :=
  {| initial_vectors :=
       List.map (fun value => doubled_pack marker00 (nvec_zero d) value)
         (initial_vectors system) ++
       [doubled_pack marker10 (nvec_zero d) (nvec_zero d);
        doubled_pack marker01 (nvec_zero d) (nvec_zero d)];
     system_actions :=
       List.map doubled_lift_action (system_actions system) ++
       List.map (doubled_move_action zmarker_move_ab)
         (doubled_all_fin d) ++
       List.map (doubled_move_action zmarker_move_ba)
         (doubled_all_fin d) |}.

Lemma apply_action_displacement : forall d (action : Action d) children result,
    apply_action action children = Some result ->
    add_displacement (action_offset action) children = Some result.
Proof.
  intros d action children result Happly. unfold apply_action in Happly.
  destruct (Nat.eqb (length children) (action_arity action));
    [exact Happly|discriminate].
Qed.

Lemma doubled_lift_apply_elim : forall d (action : Action d) children result,
    apply_action (doubled_lift_action action) children = Some result ->
    doubled_marker result = nvec_sum (List.map doubled_marker children) /\
    doubled_input result = nvec_sum (List.map doubled_input children) /\
    apply_action action (List.map doubled_output children) =
      Some (doubled_output result).
Proof.
  intros d action children result Happly.
  pose proof (apply_action_length _ _ _ _ Happly) as Hlength.
  change (length children = action_arity action) in Hlength.
  pose proof (apply_action_displacement _ _ _ _ Happly) as Hdisplacement.
  pose proof (add_displacement_exact _ _ _ _ Hdisplacement) as Hexact.
  rewrite nvec_sum_doubled_blocks in Hexact.
  rewrite <- (doubled_repack d result) in Hexact.
  apply zvec_pack_add in Hexact as [Hmarker [Hinput Houtput]].
  rewrite zmarker00_zero, zvec_zero_add in Hmarker.
  rewrite zvec_zero_add in Hinput.
  split.
  - apply nvec_to_zvec_inj. symmetry. exact Hmarker.
  - split.
    + apply nvec_to_zvec_inj. symmetry. exact Hinput.
    + apply apply_action_of_exact.
      * rewrite length_map. exact Hlength.
      * exact Houtput.
Qed.

Lemma doubled_lift_apply_intro : forall d (action : Action d) children output,
    apply_action action (List.map doubled_output children) = Some output ->
    apply_action (doubled_lift_action action) children =
      Some (doubled_pack
        (nvec_sum (List.map doubled_marker children))
        (nvec_sum (List.map doubled_input children)) output).
Proof.
  intros d action children output Happly.
  apply apply_action_of_exact.
  - cbn. pose proof (apply_action_length _ _ _ _ Happly) as Hlength.
    now rewrite length_map in Hlength.
  - rewrite nvec_sum_doubled_blocks.
    apply zvec_pack_add. split.
    + rewrite zmarker00_zero, zvec_zero_add. reflexivity.
    + split.
      * rewrite zvec_zero_add. reflexivity.
      * unfold apply_action in Happly.
        destruct (Nat.eqb (length (List.map doubled_output children))
          (action_arity action)); [|discriminate].
        now apply add_displacement_exact in Happly.
Qed.

Lemma doubled_move_ab_apply : forall d (coordinate : Fin.t d) input output,
    apply_action (doubled_move_action zmarker_move_ab coordinate)
      [doubled_pack marker10 input output] =
    Some (doubled_pack marker01 (nvec_add input (nunit coordinate))
      (nvec_add output (nunit coordinate))).
Proof.
  intros. apply apply_action_of_exact; [reflexivity|].
  rewrite nvec_sum_rsum. cbn. rewrite nvec_add_zero_right.
  change (zvec_add
      (StdVector.append zmarker_move_ab
        (StdVector.append (zunit coordinate) (zunit coordinate)))
      (nvec_to_zvec (doubled_pack marker10 input output)) =
    nvec_to_zvec (doubled_pack marker01
      (nvec_add input (nunit coordinate))
      (nvec_add output (nunit coordinate)))).
  apply zvec_pack_add. split.
  - reflexivity.
  - split; rewrite zunit_nunit; apply zvec_add_nvec_commute.
Qed.

Lemma doubled_move_ba_apply : forall d (coordinate : Fin.t d) input output,
    apply_action (doubled_move_action zmarker_move_ba coordinate)
      [doubled_pack marker01 input output] =
    Some (doubled_pack marker10 (nvec_add input (nunit coordinate))
      (nvec_add output (nunit coordinate))).
Proof.
  intros. apply apply_action_of_exact; [reflexivity|].
  rewrite nvec_sum_rsum. cbn. rewrite nvec_add_zero_right.
  change (zvec_add
      (StdVector.append zmarker_move_ba
        (StdVector.append (zunit coordinate) (zunit coordinate)))
      (nvec_to_zvec (doubled_pack marker01 input output)) =
    nvec_to_zvec (doubled_pack marker10
      (nvec_add input (nunit coordinate))
      (nvec_add output (nunit coordinate)))).
  apply zvec_pack_add. split.
  - reflexivity.
  - split; rewrite zunit_nunit; apply zvec_add_nvec_commute.
Qed.

Lemma doubled_all_fin_complete : forall d (coordinate : Fin.t d),
    List.In coordinate (doubled_all_fin d).
Proof.
  intros d coordinate. induction d as [|d IH].
  - exact (Fin.case0 (fun _ => False) coordinate).
  - refine (Fin.caseS' coordinate
      (fun coordinate => List.In coordinate (doubled_all_fin (S d))) _ _).
    + now left.
    + intro tail. right. apply in_map. apply IH.
Qed.

Lemma doubled_move_ab_in : forall d (system : IBVAS d) coordinate,
    List.In (doubled_move_action zmarker_move_ab coordinate)
      (system_actions (doubled_system system)).
Proof.
  intros. unfold doubled_system; cbn. apply in_or_app; right.
  apply in_or_app; left. apply in_map, doubled_all_fin_complete.
Qed.

Lemma doubled_move_ba_in : forall d (system : IBVAS d) coordinate,
    List.In (doubled_move_action zmarker_move_ba coordinate)
      (system_actions (doubled_system system)).
Proof.
  intros. unfold doubled_system; cbn. apply in_or_app; right.
  apply in_or_app; right. apply in_map, doubled_all_fin_complete.
Qed.

Lemma doubled_lift_action_in : forall d (system : IBVAS d) action,
    List.In action (system_actions system) ->
    List.In (doubled_lift_action action)
      (system_actions (doubled_system system)).
Proof.
  intros. unfold doubled_system; cbn. apply in_or_app; left. now apply in_map.
Qed.

Definition MarkerOne (marker : NVec 2) : Prop :=
  marker = marker10 \/ marker = marker01.

Lemma reach_initial_member : forall d (system : IBVAS d) value,
    List.In value (initial_vectors system) -> Reach system value.
Proof.
  intros d system value Hin. apply In_nth_error in Hin as [index Hindex].
  now apply reach_initial with (index := index).
Qed.

Lemma reach_action_member : forall d (system : IBVAS d) action children result,
    List.In action (system_actions system) ->
    ReachChildren system children ->
    apply_action action children = Some result ->
    Reach system result.
Proof.
  intros d system action children result Hin Hchildren Happly.
  apply In_nth_error in Hin as [index Hindex].
  now apply reach_action with (index := index) (action := action)
    (children := children).
Qed.

Lemma doubled_special_zero : forall d (system : IBVAS d),
    Reach (doubled_system system)
      (doubled_pack marker10 (nvec_zero d) (nvec_zero d)).
Proof.
  intros. apply reach_initial_member. unfold doubled_system; cbn.
  apply in_or_app. right. now left.
Qed.

Lemma marker_one_step : forall d (system : IBVAS d) marker input
    (coordinate : Fin.t d),
    MarkerOne marker ->
    Reach (doubled_system system) (doubled_pack marker input input) ->
    exists marker', MarkerOne marker' /\
      Reach (doubled_system system)
        (doubled_pack marker' (nvec_add input (nunit coordinate))
          (nvec_add input (nunit coordinate))).
Proof.
  intros d system marker input coordinate [Hmarker|Hmarker] Hreach;
    subst marker.
  - exists marker01. split; [now right|].
    eapply reach_action_member with
      (action := doubled_move_action zmarker_move_ab coordinate)
      (children := [doubled_pack marker10 input input]).
    + apply doubled_move_ab_in.
    + constructor; [exact Hreach|constructor].
    + apply doubled_move_ab_apply.
  - exists marker10. split; [now left|].
    eapply reach_action_member with
      (action := doubled_move_action zmarker_move_ba coordinate)
      (children := [doubled_pack marker01 input input]).
    + apply doubled_move_ba_in.
    + constructor; [exact Hreach|constructor].
    + apply doubled_move_ba_apply.
Qed.

Lemma nunit_one_hot : forall d (coordinate : Fin.t d),
    nunit coordinate = one_hot_nat d (proj1_sig (Fin.to_nat coordinate)).
Proof.
  intros d coordinate. apply (proj1 (StdVector.eq_nth_iff nat d _ _)).
  intros index index' <-. unfold nunit, one_hot_nat.
  rewrite Closure.nvec_tabulate_nth, nth_vector_of_function.
  destruct (Fin.eq_dec index coordinate) as [->|Hneq].
  - now rewrite Nat.eqb_refl.
  - destruct (Nat.eqb (proj1_sig (Fin.to_nat index))
      (proj1_sig (Fin.to_nat coordinate))) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E. exfalso. apply Hneq, Fin.to_nat_inj. exact E.
Qed.

Lemma coordinate_count_vector_nunit : forall d (coordinate : Fin.t d) count,
    coordinate_count_vector (coordinate, count) =
      nvec_times count (nunit coordinate).
Proof.
  intros. unfold coordinate_count_vector. cbn.
  now rewrite nunit_one_hot.
Qed.

Lemma marker_one_repeat : forall d (system : IBVAS d) count
    (coordinate : Fin.t d) marker input,
    MarkerOne marker ->
    Reach (doubled_system system) (doubled_pack marker input input) ->
    exists marker', MarkerOne marker' /\
      Reach (doubled_system system)
        (doubled_pack marker'
          (nvec_add input (nvec_times count (nunit coordinate)))
          (nvec_add input (nvec_times count (nunit coordinate)))).
Proof.
  intros d system count. induction count as [|count IH];
    intros coordinate marker input Hmarker Hreach.
  - exists marker. split; [exact Hmarker|]. cbn.
    now rewrite nvec_add_zero_right.
  - destruct (IH coordinate marker input Hmarker Hreach)
      as [middle [Hmiddle Hmiddle_reach]].
    destruct (marker_one_step d system middle
      (nvec_add input (nvec_times count (nunit coordinate))) coordinate
      Hmiddle Hmiddle_reach) as [result [Hresult Hresult_reach]].
    exists result. split; [exact Hresult|].
    replace (nvec_add input (nvec_times (S count) (nunit coordinate)))
      with (nvec_add
        (nvec_add input (nvec_times count (nunit coordinate)))
        (nunit coordinate)).
    + exact Hresult_reach.
    + cbn. rewrite nvec_add_assoc.
      f_equal. apply nvec_add_comm_stateful.
Qed.

Lemma marker_one_entries : forall d (system : IBVAS d)
    (entries : list (Fin.t d * nat)) marker input,
    MarkerOne marker ->
    Reach (doubled_system system) (doubled_pack marker input input) ->
    exists marker', MarkerOne marker' /\
      Reach (doubled_system system)
        (doubled_pack marker'
          (nvec_add input
            (nvec_sum (List.map coordinate_count_vector entries)))
          (nvec_add input
            (nvec_sum (List.map coordinate_count_vector entries)))).
Proof.
  intros d system entries. induction entries as [|[coordinate count] entries IH];
    intros marker input Hmarker Hreach.
  - exists marker. split; [exact Hmarker|]. cbn.
    now rewrite nvec_add_zero_right.
  - destruct (marker_one_repeat d system count coordinate marker input
      Hmarker Hreach) as [middle [Hmiddle Hmiddle_reach]].
    destruct (IH middle
      (nvec_add input (nvec_times count (nunit coordinate)))
      Hmiddle Hmiddle_reach) as [result [Hresult Hresult_reach]].
    exists result. split; [exact Hresult|].
    rewrite !nvec_sum_rsum_stateful in Hresult_reach |- *.
    cbn [List.map nvec_rsum_stateful] in *.
    rewrite !coordinate_count_vector_nunit.
    rewrite <- !nvec_add_assoc.
    exact Hresult_reach.
Qed.

Theorem doubled_special_diagonal : forall d (system : IBVAS d) input,
    exists marker, MarkerOne marker /\
      Reach (doubled_system system) (doubled_pack marker input input).
Proof.
  intros d system input.
  destruct (marker_one_entries d system (coordinate_counts input) marker10
    (nvec_zero d)) as [marker [Hmarker Hreach]].
  - now left.
  - apply doubled_special_zero.
  - exists marker. split; [exact Hmarker|].
    rewrite coordinate_counts_expansion in Hreach.
    now rewrite nvec_add_zero_left in Hreach.
Qed.

(** The marker mass counts distinguished leaves.  Keeping this as the sum of
    the two natural coordinates makes the exclusion of the zero and
    multi-marker cases constructive. *)
Definition marker_mass (marker : NVec 2) : nat := nvec_total marker.

Lemma nvec_total_rsum : forall d (values : list (NVec d)),
    nvec_total (nvec_rsum values) =
      List.fold_right Nat.add 0 (List.map nvec_total values).
Proof.
  intros d values; induction values as [|value values IH]; cbn.
  - apply nvec_total_zero.
  - now rewrite nvec_total_add, IH.
Qed.

Lemma nvec_total_zero_inv : forall d (value : NVec d),
    nvec_total value = 0 -> value = nvec_zero d.
Proof.
  intros d value; induction value as [|head d tail IH]; intro Htotal.
  - reflexivity.
  - cbn in Htotal |- *. f_equal.
    + lia.
    + apply IH. lia.
Qed.

Lemma marker_mass_zero_iff : forall marker : NVec 2,
    marker_mass marker = 0 <-> marker = marker00.
Proof.
  intro marker. split.
  - intro H. unfold marker_mass in H.
    pose proof (nvec_total_zero_inv 2 marker H) as ->. reflexivity.
  - intro H. subst marker. reflexivity.
Qed.

Lemma marker_mass_one_iff : forall marker : NVec 2,
    marker_mass marker = 1 <-> MarkerOne marker.
Proof.
  intro marker. unfold marker_mass, MarkerOne.
  refine (StdVector.caseS' marker (fun marker =>
    nvec_total marker = 1 <-> marker = marker10 \/ marker = marker01) _).
  intros first tail. refine (StdVector.caseS' tail (fun tail =>
    nvec_total (StdVector.cons nat first 1 tail) = 1 <->
      StdVector.cons nat first 1 tail = marker10 \/
      StdVector.cons nat first 1 tail = marker01) _).
  intros second tail0. refine (StdVector.case0 (fun tail0 =>
    nvec_total (StdVector.cons nat first 1
      (StdVector.cons nat second 0 tail0)) = 1 <->
    StdVector.cons nat first 1 (StdVector.cons nat second 0 tail0) = marker10 \/
    StdVector.cons nat first 1 (StdVector.cons nat second 0 tail0) = marker01) _ tail0).
  cbn. split.
  - intro H. destruct first as [|first].
    + assert (second = 1) by lia. subst second. now right.
    + assert (first = 0 /\ second = 0) by lia.
      destruct H0 as [-> ->]. now left.
  - intros [H|H]; inversion H; reflexivity.
Qed.

Lemma marker_mass_pack : forall d marker (input output : NVec d),
    marker_mass (doubled_marker (doubled_pack marker input output)) =
      marker_mass marker.
Proof. intros. now rewrite (proj1 (doubled_unpack_pack d marker input output)). Qed.

Lemma marker_mass_sum : forall d
    (values : list (NVec (doubled_dimension d))),
    marker_mass (nvec_sum (List.map doubled_marker values)) =
      List.fold_right Nat.add 0
        (List.map (fun value => marker_mass (doubled_marker value)) values).
Proof.
  intros. unfold marker_mass. rewrite nvec_sum_rsum, nvec_total_rsum.
  now rewrite List.map_map.
Qed.

Lemma special_leaf_reach_shift : forall d (system : IBVAS d) input output,
    SpecialLeafReach system input output ->
    forall delta,
      SpecialLeafReach system (nvec_add input delta) (nvec_add output delta).
Proof.
  intros d system input output Hspecial.
  induction Hspecial as
    [input|input action prefix middle suffix output Hin Hprefix Hmiddle IH
      Hsuffix Happly]; intro delta.
  - constructor.
  - eapply special_action with (action := action) (prefix := prefix)
      (middle := nvec_add middle delta) (suffix := suffix).
    + exact Hin.
    + exact Hprefix.
    + apply IH.
    + exact Hsuffix.
    + eapply apply_action_frame_shift; eauto.
Qed.

Definition doubled_ordinary {d} (value : NVec d) :
    NVec (doubled_dimension d) :=
  doubled_pack marker00 (nvec_zero d) value.

Lemma doubled_ordinary_blocks : forall d (value : NVec d),
    doubled_marker (doubled_ordinary value) = marker00 /\
    doubled_input (doubled_ordinary value) = nvec_zero d /\
    doubled_output (doubled_ordinary value) = value.
Proof. intros. apply doubled_unpack_pack. Qed.

Lemma doubled_ordinary_marker_sum : forall d (values : list (NVec d)),
    nvec_sum (List.map doubled_marker
      (List.map doubled_ordinary values)) = marker00.
Proof.
  intros. rewrite nvec_sum_rsum_stateful, List.map_map.
  replace (List.map (fun x : NVec d => doubled_marker (doubled_ordinary x))
      values) with (List.map (fun _ : NVec d => nvec_zero 2) values).
  - apply nvec_rsum_map_zero.
  - apply List.map_ext. intro value.
    apply (proj1 (doubled_ordinary_blocks d value)).
Qed.

Lemma doubled_ordinary_input_sum : forall d (values : list (NVec d)),
    nvec_sum (List.map doubled_input
      (List.map doubled_ordinary values)) = nvec_zero d.
Proof.
  intros. rewrite nvec_sum_rsum_stateful, List.map_map.
  replace (List.map (fun x : NVec d => doubled_input (doubled_ordinary x))
      values) with (List.map (fun _ : NVec d => nvec_zero d) values).
  - apply nvec_rsum_map_zero.
  - apply List.map_ext. intro value.
    symmetry. apply (proj1 (proj2 (doubled_ordinary_blocks d value))).
Qed.

Lemma doubled_ordinary_output_map : forall d (values : list (NVec d)),
    List.map doubled_output (List.map doubled_ordinary values) = values.
Proof.
  intros. rewrite List.map_map. induction values as [|value values IH];
    cbn [List.map].
  - reflexivity.
  - rewrite (proj2 (proj2 (doubled_ordinary_blocks d value))), IH.
    reflexivity.
Qed.

Lemma reach_doubled_ordinary_mut : forall d (system : IBVAS d),
  (forall value, Reach system value ->
    Reach (doubled_system system) (doubled_ordinary value)) /\
  (forall values, ReachChildren system values ->
    ReachChildren (doubled_system system)
      (List.map doubled_ordinary values)).
Proof.
  intros d system. apply Reach_mutind.
  - intros index value Hinitial. apply reach_initial_member.
    change (List.In (doubled_ordinary value)
      (List.map doubled_ordinary (initial_vectors system) ++
        [doubled_pack marker10 (nvec_zero d) (nvec_zero d);
         doubled_pack marker01 (nvec_zero d) (nvec_zero d)])).
    apply in_or_app; left.
    apply in_map. now apply nth_error_In in Hinitial.
  - intros index action children value Haction Hchildren IHchildren Happly.
    eapply reach_action_member with (action := doubled_lift_action action)
      (children := List.map doubled_ordinary children).
    + apply doubled_lift_action_in. now apply nth_error_In in Haction.
    + exact IHchildren.
    + change (apply_action (doubled_lift_action action)
        (List.map doubled_ordinary children) =
        Some (doubled_pack marker00 (nvec_zero d) value)).
      rewrite doubled_lift_apply_intro with (output := value).
      * now rewrite doubled_ordinary_marker_sum,
          doubled_ordinary_input_sum.
      * now rewrite doubled_ordinary_output_map.
  - constructor.
  - intros value values Hvalue IHvalue Hvalues IHvalues.
    constructor; assumption.
Qed.

Lemma reach_doubled_ordinary : forall d (system : IBVAS d) value,
    Reach system value ->
    Reach (doubled_system system) (doubled_ordinary value).
Proof. intros; now apply (proj1 (reach_doubled_ordinary_mut d system)). Qed.

Lemma reach_children_app : forall d (system : IBVAS d) left right,
    ReachChildren system left -> ReachChildren system right ->
    ReachChildren system (left ++ right).
Proof.
  intros d system left right Hleft. induction Hleft; intro Hright; cbn; auto.
  constructor; auto.
Qed.

Lemma reach_children_forall : forall d (system : IBVAS d) values,
    List.Forall (Reach system) values -> ReachChildren system values.
Proof.
  intros d system values Hall. induction Hall; constructor; assumption.
Qed.

Lemma doubled_single_marker_blocks : forall d (prefix suffix : list (NVec d))
    marker input middle,
    let children := List.map doubled_ordinary prefix ++
      doubled_pack marker input middle :: List.map doubled_ordinary suffix in
    nvec_sum (List.map doubled_marker children) = marker /\
    nvec_sum (List.map doubled_input children) = input /\
    List.map doubled_output children = prefix ++ middle :: suffix.
Proof.
  intros d prefix suffix marker input middle children. subst children.
  split.
  - rewrite !List.map_app, !nvec_sum_rsum, !nvec_rsum_app.
    change (nvec_add
      (nvec_rsum (List.map doubled_marker (List.map doubled_ordinary prefix)))
      (nvec_add (doubled_marker (doubled_pack marker input middle))
        (nvec_rsum (List.map doubled_marker
          (List.map doubled_ordinary suffix)))) = marker).
    rewrite <- !nvec_sum_rsum, doubled_ordinary_marker_sum,
      (proj1 (doubled_unpack_pack d marker input middle)),
      doubled_ordinary_marker_sum.
    rewrite !nvec_add_zero_left, nvec_add_zero_right. reflexivity.
  - split.
    + rewrite !List.map_app, !nvec_sum_rsum, !nvec_rsum_app.
      change (nvec_add
        (nvec_rsum (List.map doubled_input (List.map doubled_ordinary prefix)))
        (nvec_add (doubled_input (doubled_pack marker input middle))
          (nvec_rsum (List.map doubled_input
            (List.map doubled_ordinary suffix)))) = input).
      rewrite <- !nvec_sum_rsum, doubled_ordinary_input_sum,
        (proj1 (proj2 (doubled_unpack_pack d marker input middle))),
        doubled_ordinary_input_sum.
      rewrite !nvec_add_zero_left, nvec_add_zero_right. reflexivity.
    + rewrite !List.map_app, doubled_ordinary_output_map. cbn [List.map].
      rewrite (proj2 (proj2 (doubled_unpack_pack d marker input middle))),
        doubled_ordinary_output_map. reflexivity.
Qed.

Lemma special_leaf_doubled : forall d (system : IBVAS d) input output,
    SpecialLeafReach system input output ->
    exists marker, MarkerOne marker /\
      Reach (doubled_system system) (doubled_pack marker input output).
Proof.
  intros d system input output Hspecial.
  induction Hspecial as
    [input|input action prefix middle suffix output Hin Hprefix Hmiddle IH
      Hsuffix Happly].
  - apply doubled_special_diagonal.
  - destruct IH as [marker [Hmarker Hmiddle_reach]].
    exists marker. split; [exact Hmarker|].
    set (children := List.map doubled_ordinary prefix ++
      doubled_pack marker input middle :: List.map doubled_ordinary suffix).
    eapply reach_action_member with (action := doubled_lift_action action)
      (children := children).
    + now apply doubled_lift_action_in.
    + unfold children. apply reach_children_app.
      * apply (proj2 (reach_doubled_ordinary_mut d system)).
        now apply reach_children_forall.
      * constructor; [exact Hmiddle_reach|].
        apply (proj2 (reach_doubled_ordinary_mut d system)).
        now apply reach_children_forall.
    + rewrite doubled_lift_apply_intro with (output := output).
      * destruct (doubled_single_marker_blocks d prefix suffix marker input middle)
          as [Hmarker_sum [Hinput_sum Houtput_map]].
        unfold children. now rewrite Hmarker_sum, Hinput_sum.
      * destruct (doubled_single_marker_blocks d prefix suffix marker input middle)
          as [_ [_ Houtput_map]].
        unfold children. now rewrite Houtput_map.
Qed.

Lemma doubled_action_cases : forall d (system : IBVAS d)
    (action : Action (doubled_dimension d)),
    List.In action (system_actions (doubled_system system)) ->
    (exists original, List.In original (system_actions system) /\
       action = doubled_lift_action original) \/
    (exists coordinate, action = doubled_move_action zmarker_move_ab coordinate) \/
    (exists coordinate, action = doubled_move_action zmarker_move_ba coordinate).
Proof.
  intros d system action Hin. unfold doubled_system in Hin; cbn in Hin.
  apply in_app_iff in Hin as [Hin|Hin].
  - apply in_map_iff in Hin as [original [Haction Horiginal]].
    left. exists original. auto.
  - apply in_app_iff in Hin as [Hin|Hin].
    + apply in_map_iff in Hin as [coordinate [Haction _]].
      right; left. exists coordinate. symmetry; exact Haction.
    + apply in_map_iff in Hin as [coordinate [Haction _]].
      right; right. exists coordinate. symmetry; exact Haction.
Qed.

Fixpoint zvec_total_local {d} (value : ZVec d) : Z :=
  match value with
  | Vector.nil => 0%Z
  | Vector.cons head _ tail => (head + zvec_total_local tail)%Z
  end.

Lemma zvec_total_local_add : forall d (left right : ZVec d),
    zvec_total_local (zvec_add left right) =
      (zvec_total_local left + zvec_total_local right)%Z.
Proof.
  intros d left. induction left as [|head d tail IH]; intro right.
  - refine (StdVector.case0 (fun right => _) _ right). reflexivity.
  - refine (StdVector.caseS' right (fun right => _) _).
    intros rhead rtail. cbn. rewrite IH. lia.
Qed.

Lemma zvec_total_local_nvec : forall d (value : NVec d),
    zvec_total_local (nvec_to_zvec value) = Z.of_nat (nvec_total value).
Proof.
  intros d value. induction value as [|head d tail IH]; cbn.
  - reflexivity.
  - rewrite Nat2Z.inj_add. cbn. f_equal. exact IH.
Qed.

Lemma nvec_nth_le_total : forall d (value : NVec d) (index : Fin.t d),
    StdVector.nth value index <= nvec_total value.
Proof.
  intros d value. induction value as [|head d tail IH]; intro index.
  - exact (Fin.case0 (fun index => StdVector.nth (StdVector.nil nat) index <=
      nvec_total (StdVector.nil nat)) index).
  - refine (Fin.caseS' index (fun index =>
      StdVector.nth (StdVector.cons nat head d tail) index <=
        nvec_total (StdVector.cons nat head d tail)) _ _).
    + cbn. lia.
    + intro tail_index. cbn. specialize (IH tail_index). lia.
Qed.

Lemma move_marker_mass_preserved : forall delta child result,
    zvec_total_local delta = 0%Z ->
    zvec_add delta (nvec_to_zvec child) = nvec_to_zvec result ->
    marker_mass child = marker_mass result.
Proof.
  intros delta child result Hdelta Heq.
  apply (f_equal zvec_total_local) in Heq.
  rewrite zvec_total_local_add, !zvec_total_local_nvec, Hdelta in Heq.
  unfold marker_mass. lia.
Qed.

Lemma move_ab_marker_mass : forall child result : NVec 2,
    zvec_add zmarker_move_ab (nvec_to_zvec child) = nvec_to_zvec result ->
    marker_mass result = 1 -> marker_mass child = 1.
Proof.
  intros child result Heq Hmass.
  pose proof (move_marker_mass_preserved zmarker_move_ab child result
    eq_refl Heq) as Hpreserved. lia.
Qed.

Lemma move_ba_marker_mass : forall child result : NVec 2,
    zvec_add zmarker_move_ba (nvec_to_zvec child) = nvec_to_zvec result ->
    marker_mass result = 1 -> marker_mass child = 1.
Proof.
  intros child result Heq Hmass.
  pose proof (move_marker_mass_preserved zmarker_move_ba child result
    eq_refl Heq) as Hpreserved. lia.
Qed.

Lemma doubled_move_apply_elim : forall d marker_delta (coordinate : Fin.t d)
    children result,
    (marker_delta = zmarker_move_ab \/ marker_delta = zmarker_move_ba) ->
    apply_action (doubled_move_action marker_delta coordinate) children =
      Some result ->
    marker_mass (doubled_marker result) = 1 ->
    exists child,
      children = [child] /\
      marker_mass (doubled_marker child) = 1 /\
      doubled_input result =
        nvec_add (doubled_input child) (nunit coordinate) /\
      doubled_output result =
        nvec_add (doubled_output child) (nunit coordinate).
Proof.
  intros d marker_delta coordinate children result Hdelta Happly Hmass.
  pose proof (apply_action_length _ _ _ _ Happly) as Hlength. cbn in Hlength.
  destruct children as [|child children]; [discriminate|].
  destruct children as [|extra children]; [|cbn in Hlength; lia].
  exists child. split; [reflexivity|].
  pose proof (apply_action_displacement _ _ _ _ Happly) as Hdisp.
  apply add_displacement_exact in Hdisp.
  rewrite nvec_sum_rsum in Hdisp. cbn in Hdisp.
  rewrite nvec_add_zero_right in Hdisp.
  rewrite <- (doubled_repack d child), <- (doubled_repack d result) in Hdisp.
  apply zvec_pack_add in Hdisp as [Hmarker [Hinput Houtput]].
  split.
  - destruct Hdelta as [Hdelta|Hdelta]; subst marker_delta.
    + eapply move_ab_marker_mass; eauto.
    + eapply move_ba_marker_mass; eauto.
  - split.
    + apply nvec_to_zvec_inj. rewrite <- Hinput, zunit_nunit.
      apply zvec_add_nvec_commute.
    + apply nvec_to_zvec_inj. rewrite <- Houtput, zunit_nunit.
      apply zvec_add_nvec_commute.
Qed.

Lemma move_ab_result_mass_positive : forall child result : NVec 2,
    zvec_add zmarker_move_ab (nvec_to_zvec child) = nvec_to_zvec result ->
    0 < marker_mass result.
Proof.
  intros child result Heq.
  pose proof (f_equal (fun value => StdVector.nth value (Fin.FS Fin.F1)) Heq)
    as Hcoordinate.
  unfold zvec_add, nvec_to_zvec in Hcoordinate.
  rewrite (Vector.nth_map2 Z.add _ _ (Fin.FS Fin.F1)
      (Fin.FS Fin.F1) (Fin.FS Fin.F1) eq_refl eq_refl),
    (Vector.nth_map Z.of_nat child (Fin.FS Fin.F1)
      (Fin.FS Fin.F1) eq_refl),
    (Vector.nth_map Z.of_nat result (Fin.FS Fin.F1)
      (Fin.FS Fin.F1) eq_refl) in Hcoordinate.
  change (1 + Z.of_nat (StdVector.nth child (Fin.FS Fin.F1)) =
    Z.of_nat (StdVector.nth result (Fin.FS Fin.F1)))%Z in Hcoordinate.
  assert (Hpositive : 0 < StdVector.nth result (Fin.FS Fin.F1)).
  { apply (proj2 (Nat2Z.inj_lt 0 _)). cbn. lia. }
  unfold marker_mass.
  eapply Nat.lt_le_trans; [exact Hpositive|].
  apply nvec_nth_le_total.
Qed.

Lemma move_ba_result_mass_positive : forall child result : NVec 2,
    zvec_add zmarker_move_ba (nvec_to_zvec child) = nvec_to_zvec result ->
    0 < marker_mass result.
Proof.
  intros child result Heq.
  pose proof (f_equal (fun value => StdVector.nth value Fin.F1) Heq)
    as Hcoordinate.
  unfold zvec_add, nvec_to_zvec in Hcoordinate.
  rewrite (Vector.nth_map2 Z.add _ _ Fin.F1 Fin.F1 Fin.F1 eq_refl eq_refl),
    (Vector.nth_map Z.of_nat child Fin.F1 Fin.F1 eq_refl),
    (Vector.nth_map Z.of_nat result Fin.F1 Fin.F1 eq_refl) in Hcoordinate.
  change (1 + Z.of_nat (StdVector.nth child Fin.F1) =
    Z.of_nat (StdVector.nth result Fin.F1))%Z in Hcoordinate.
  assert (Hpositive : 0 < StdVector.nth result Fin.F1).
  { apply (proj2 (Nat2Z.inj_lt 0 _)). cbn. lia. }
  unfold marker_mass.
  eapply Nat.lt_le_trans; [exact Hpositive|].
  apply nvec_nth_le_total.
Qed.

Lemma doubled_move_result_mass_positive : forall d marker_delta
    (coordinate : Fin.t d) children result,
    (marker_delta = zmarker_move_ab \/ marker_delta = zmarker_move_ba) ->
    apply_action (doubled_move_action marker_delta coordinate) children =
      Some result ->
    0 < marker_mass (doubled_marker result).
Proof.
  intros d marker_delta coordinate children result Hdelta Happly.
  pose proof (apply_action_length _ _ _ _ Happly) as Hlength. cbn in Hlength.
  destruct children as [|child children]; [discriminate|].
  destruct children as [|extra children]; [|cbn in Hlength; lia].
  pose proof (apply_action_displacement _ _ _ _ Happly) as Hdisp.
  apply add_displacement_exact in Hdisp.
  rewrite nvec_sum_rsum in Hdisp. cbn in Hdisp.
  rewrite nvec_add_zero_right in Hdisp.
  rewrite <- (doubled_repack d child), <- (doubled_repack d result) in Hdisp.
  apply zvec_pack_add in Hdisp as [Hmarker _].
  destruct Hdelta as [Hdelta|Hdelta]; subst marker_delta.
  - now apply move_ab_result_mass_positive in Hmarker.
  - now apply move_ba_result_mass_positive in Hmarker.
Qed.

Lemma nat_list_sum_zero : forall (values : list nat),
    List.fold_right Nat.add 0 values = 0 ->
    List.Forall (fun value => value = 0) values.
Proof.
  intros values. induction values as [|value values IH]; intro Hsum.
  - constructor.
  - cbn in Hsum. constructor; [lia|]. apply IH. lia.
Qed.

Lemma nat_list_sum_one_split : forall (values : list nat),
    List.fold_right Nat.add 0 values = 1 ->
    exists prefix middle suffix,
      values = prefix ++ middle :: suffix /\
      middle = 1 /\
      List.Forall (fun value => value = 0) prefix /\
      List.Forall (fun value => value = 0) suffix.
Proof.
  intros values. induction values as [|value values IH]; intro Hsum.
  - discriminate.
  - cbn in Hsum. destruct value as [|value].
    + destruct (IH Hsum) as [prefix [middle [suffix
        [Heq [Hmiddle [Hprefix Hsuffix]]]]]].
      exists (0 :: prefix), middle, suffix. repeat split; cbn; auto.
      now rewrite Heq.
    + assert (value = 0 /\ List.fold_right Nat.add 0 values = 0) by lia.
      destruct H as [Hvalue Htail]. subst value.
      exists [], 1, values. repeat split; auto.
      now apply nat_list_sum_zero.
Qed.

Lemma list_weights_zero : forall A (weight : A -> nat) (values : list A),
    List.fold_right Nat.add 0 (List.map weight values) = 0 ->
    List.Forall (fun value => weight value = 0) values.
Proof.
  intros A weight values. induction values as [|value values IH]; intro Hsum.
  - constructor.
  - cbn in Hsum. constructor; [lia|]. apply IH. lia.
Qed.

Lemma list_weights_one_split : forall A (weight : A -> nat) (values : list A),
    List.fold_right Nat.add 0 (List.map weight values) = 1 ->
    exists prefix middle suffix,
      values = prefix ++ middle :: suffix /\
      weight middle = 1 /\
      List.Forall (fun value => weight value = 0) prefix /\
      List.Forall (fun value => weight value = 0) suffix.
Proof.
  intros A weight values Hsum.
  induction values as [|value values IH]; cbn in Hsum.
  - discriminate.
  - destruct (weight value) as [|count] eqn:Hweight.
    + destruct (IH Hsum) as [prefix [middle [suffix
        [Heq [Hmiddle [Hprefix Hsuffix]]]]]].
      exists (value :: prefix), middle, suffix. repeat split; cbn; auto.
      now rewrite Heq.
    + assert (count = 0 /\
        List.fold_right Nat.add 0 (List.map weight values) = 0) by lia.
      destruct H as [Hcount Htail]. subst count.
      exists [], value, values. repeat split; auto.
      now apply list_weights_zero.
Qed.

Definition DoubledClass {d} (system : IBVAS d)
    (value : NVec (doubled_dimension d)) : Prop :=
  (marker_mass (doubled_marker value) = 0 ->
    doubled_input value = nvec_zero d /\ Reach system (doubled_output value)) /\
  (marker_mass (doubled_marker value) = 1 ->
    SpecialLeafReach system (doubled_input value) (doubled_output value)).

Lemma doubled_initial_cases : forall d (system : IBVAS d) value,
    List.In value (initial_vectors (doubled_system system)) ->
    (exists original, List.In original (initial_vectors system) /\
       value = doubled_ordinary original) \/
    value = doubled_pack marker10 (nvec_zero d) (nvec_zero d) \/
    value = doubled_pack marker01 (nvec_zero d) (nvec_zero d).
Proof.
  intros d system value Hin.
  change (List.In value
    (List.map doubled_ordinary (initial_vectors system) ++
      [doubled_pack marker10 (nvec_zero d) (nvec_zero d);
       doubled_pack marker01 (nvec_zero d) (nvec_zero d)])) in Hin.
  apply in_app_iff in Hin as [Hin|Hin].
  - apply in_map_iff in Hin as [original [Hvalue Horiginal]].
    left. exists original. split; [exact Horiginal|now symmetry].
  - cbn in Hin. destruct Hin as [Hin|[Hin|Hin]].
    + right; left. now symmetry.
    + right; right. now symmetry.
    + contradiction.
Qed.

Lemma doubled_children_zero : forall d (system : IBVAS d) values,
    List.Forall (DoubledClass system) values ->
    List.Forall
      (fun value => marker_mass (doubled_marker value) = 0) values ->
    nvec_sum (List.map doubled_input values) = nvec_zero d /\
    ReachChildren system (List.map doubled_output values).
Proof.
  intros d system values Hclass Hzero. induction Hclass.
  - split; [reflexivity|constructor].
  - inversion Hzero; subst. destruct H as [Hzero_case _].
    destruct (Hzero_case H2) as [Hinput Hreach].
    destruct IHHclass as [Hsum Hchildren]; [exact H3|].
    split.
    + rewrite nvec_sum_rsum_stateful in Hsum |- *.
      change (nvec_add (doubled_input x)
        (nvec_rsum_stateful (List.map doubled_input l)) = nvec_zero d).
      rewrite Hinput, Hsum. apply nvec_add_zero_left_stateful.
    + constructor; assumption.
Qed.

Lemma nvec_sum_map_middle : forall d A (project : A -> NVec d)
    prefix middle suffix,
    nvec_sum (List.map project prefix) = nvec_zero d ->
    nvec_sum (List.map project suffix) = nvec_zero d ->
    nvec_sum (List.map project (prefix ++ middle :: suffix)) = project middle.
Proof.
  intros d A project prefix middle suffix Hprefix Hsuffix.
  rewrite List.map_app, !nvec_sum_rsum_stateful, nvec_rsum_app.
  cbn [List.map nvec_rsum].
  rewrite <- !nvec_sum_rsum_stateful, Hprefix, Hsuffix.
  rewrite nvec_add_zero_left_stateful, nvec_add_zero_right. reflexivity.
Qed.

Lemma doubled_reach_classified_mut : forall d (system : IBVAS d),
  (forall value, Reach (doubled_system system) value ->
    DoubledClass system value) /\
  (forall values, ReachChildren (doubled_system system) values ->
    List.Forall (DoubledClass system) values).
Proof.
  intros d system. apply Reach_mutind.
  - intros index value Hinitial. unfold DoubledClass.
    apply nth_error_In in Hinitial.
    destruct (doubled_initial_cases d system value Hinitial) as
      [[original [Horiginal Hvalue]]|[Hvalue|Hvalue]].
    + subst value.
      split.
      * intro Hzero. rewrite (proj1 (proj2 (doubled_ordinary_blocks d original))),
          (proj2 (proj2 (doubled_ordinary_blocks d original))).
        split; [reflexivity|now apply reach_initial_member].
      * intro Hmass. rewrite (proj1 (doubled_ordinary_blocks d original))
          in Hmass. discriminate.
    + subst value. split.
      * intro Hmass. rewrite marker_mass_pack in Hmass. discriminate.
      * intro Hone. destruct (doubled_unpack_pack d marker10
           (nvec_zero d) (nvec_zero d)) as [_ [Hinput Houtput]].
        rewrite Hinput, Houtput. constructor.
    + subst value. split.
      * intro Hmass. rewrite marker_mass_pack in Hmass. discriminate.
      * intro Hone. destruct (doubled_unpack_pack d marker01
           (nvec_zero d) (nvec_zero d)) as [_ [Hinput Houtput]].
        rewrite Hinput, Houtput. constructor.
  - intros index action children value Haction Hchildren Hclass Happly.
    apply nth_error_In in Haction.
    destruct (doubled_action_cases d system action Haction) as
      [[original [Horiginal Haction_eq]]|
       [[coordinate Haction_eq]|[coordinate Haction_eq]]]; subst action.
    + pose proof (doubled_lift_apply_elim d original children value Happly)
        as [Hmarker [Hinput Houtput]].
      unfold DoubledClass. split.
      * intro Hmass. rewrite Hmarker, marker_mass_sum in Hmass.
        pose proof (list_weights_zero (NVec (doubled_dimension d))
          (fun child : NVec (doubled_dimension d) =>
            marker_mass (doubled_marker child)) children Hmass) as Hzero.
        destruct (doubled_children_zero d system children Hclass Hzero)
          as [Hinput_zero Hreach_children].
        split; [now rewrite Hinput, Hinput_zero|].
        eapply reach_action_member; eauto.
      * intro Hmass. rewrite Hmarker, marker_mass_sum in Hmass.
        destruct (list_weights_one_split (NVec (doubled_dimension d))
          (fun child : NVec (doubled_dimension d) =>
            marker_mass (doubled_marker child)) children Hmass)
          as [prefix [middle [suffix
            [Hchildren_eq [Hmiddle_mass [Hprefix_mass Hsuffix_mass]]]]]].
        subst children. apply List.Forall_app in Hclass as [Hprefix_class Hrest].
        inversion Hrest as [|middle' suffix' Hmiddle_full Hsuffix_class]; subst.
        destruct Hmiddle_full as [_ Hmiddle_class].
        destruct (doubled_children_zero d system prefix Hprefix_class
          Hprefix_mass) as [Hprefix_input Hprefix_reach].
        destruct (doubled_children_zero d system suffix Hsuffix_class
          Hsuffix_mass) as [Hsuffix_input Hsuffix_reach].
        pose proof (Hmiddle_class Hmiddle_mass) as Hmiddle_special.
        assert (Hroot_input : doubled_input value = doubled_input middle).
        { rewrite Hinput. apply nvec_sum_map_middle; assumption. }
        rewrite Hroot_input. eapply special_action with
          (action := original)
          (prefix := List.map doubled_output prefix)
          (middle := doubled_output middle)
          (suffix := List.map doubled_output suffix).
        -- exact Horiginal.
        -- clear -Hprefix_reach. induction Hprefix_reach; constructor; auto.
        -- exact Hmiddle_special.
        -- clear -Hsuffix_reach. induction Hsuffix_reach; constructor; auto.
        -- rewrite <- Houtput. rewrite !List.map_app. reflexivity.
    + unfold DoubledClass. split.
      * intro Hmass. exfalso.
        pose proof (doubled_move_result_mass_positive d zmarker_move_ab
          coordinate children value (or_introl eq_refl) Happly). lia.
      * intro Hmass.
        destruct (doubled_move_apply_elim d zmarker_move_ab coordinate
          children value (or_introl eq_refl) Happly Hmass)
          as [child [Hchildren_eq [Hchild_mass [Hinput Houtput]]]].
        subst children.
        inversion Hclass as [|child' tail Hchild_full Htail]; subst.
        destruct Hchild_full as [_ Hchild_class].
        pose proof (Hchild_class Hchild_mass) as Hspecial.
        rewrite Hinput, Houtput. now apply special_leaf_reach_shift.
    + unfold DoubledClass. split.
      * intro Hmass. exfalso.
        pose proof (doubled_move_result_mass_positive d zmarker_move_ba
          coordinate children value (or_intror eq_refl) Happly). lia.
      * intro Hmass.
        destruct (doubled_move_apply_elim d zmarker_move_ba coordinate
          children value (or_intror eq_refl) Happly Hmass)
          as [child [Hchildren_eq [Hchild_mass [Hinput Houtput]]]].
        subst children.
        inversion Hclass as [|child' tail Hchild_full Htail]; subst.
        destruct Hchild_full as [_ Hchild_class].
        pose proof (Hchild_class Hchild_mass) as Hspecial.
        rewrite Hinput, Houtput. now apply special_leaf_reach_shift.
  - constructor.
  - intros value values Hvalue IHvalue Hvalues IHvalues.
    constructor; assumption.
Qed.

Lemma doubled_reach_classified : forall d (system : IBVAS d) value,
    Reach (doubled_system system) value -> DoubledClass system value.
Proof. intros; now apply (proj1 (doubled_reach_classified_mut d system)). Qed.

Theorem doubled_marker_one_iff : forall d (system : IBVAS d) input output,
    SpecialLeafReach system input output <->
    exists marker, MarkerOne marker /\
      Reach (doubled_system system) (doubled_pack marker input output).
Proof.
  intros d system input output. split; [apply special_leaf_doubled|].
  intros [marker [Hmarker Hreach]].
  pose proof (doubled_reach_classified d system _ Hreach) as [_ Hone].
  pose proof (Hone (eq_trans (marker_mass_pack d marker input output)
    ((proj2 (marker_mass_one_iff marker)) Hmarker))) as Hspecial.
  destruct (doubled_unpack_pack d marker input output) as [_ [Hinput Houtput]].
  now rewrite Hinput, Houtput in Hspecial.
Qed.

Definition DoubledRestriction {d} (H : NRelation d)
    (value : NVec (doubled_dimension d)) : Prop :=
  MarkerOne (doubled_marker value) /\
  H (doubled_input value) (doubled_output value).

Lemma doubled_restriction_semilinear : forall d (H : NRelation d),
    SemilinearNRelation H ->
    Semilinear (@DoubledRestriction d H).
Proof.
  intros d H HH.
  pose proof (finite_nvec_set_semilinear 2 [marker10; marker01]) as Hmarker.
  pose proof (semilinear_product 2 (d + d)
    (fun marker => List.In marker [marker10; marker01])
    (fun pair => H (npair_left pair) (npair_right pair))
    Hmarker HH) as Hproduct.
  destruct Hproduct as [code Hcode]. exists code. intro value.
  rewrite <- Hcode.
  unfold DoubledRestriction, MarkerOne, doubled_marker, doubled_input,
    doubled_output, doubled_pair, doubled_dimension.
  cbn [List.In]. split.
  - intros [[Heq | Heq] Hrelation].
    + split; [left; symmetry; exact Heq | exact Hrelation].
    + split; [right; left; symmetry; exact Heq | exact Hrelation].
  - intros [[Heq | [Heq | Hfalse]] Hrelation].
    + split; [left; symmetry; exact Heq | exact Hrelation].
    + split; [right; symmetry; exact Heq | exact Hrelation].
    + contradiction.
Qed.

Lemma doubled_restriction_stateful_semilinear : forall d
    (H : NRelation d),
    SemilinearNRelation H ->
    StatefulSemilinear (fun config : SConfig (doubled_dimension d) 1 =>
      DoubledRestriction H (snd config)).
Proof.
  intros d H HH state. apply doubled_restriction_semilinear. exact HH.
Qed.

Definition doubled_pair_selection (d : nat) :
    Fin.t (d + d) -> Fin.t (doubled_dimension d) :=
  fun index => Fin.R 2 index.

Lemma doubled_pair_selection_correct : forall d
    (value : NVec (doubled_dimension d)) index,
    StdVector.nth (doubled_pair value) index =
      StdVector.nth value (doubled_pair_selection d index).
Proof.
  intros d value index. unfold doubled_pair_selection.
  pose proof (f_equal
    (fun vector : NVec (2 + (d + d)) => StdVector.nth vector (Fin.R 2 index))
    (append_shiftin 2 (d + d) value)) as Heq.
  unfold doubled_pair, doubled_dimension.
  cbn beta in Heq. rewrite VectorSpec.nth_append_R in Heq. exact Heq.
Qed.

Definition NRelationPairSet {d} (relation : NRelation d) :
    NVec (d + d) -> Prop :=
  fun pair => relation (npair_left pair) (npair_right pair).

Definition PairSetRelation {d} (set : NVec (d + d) -> Prop) :
    NRelation d :=
  fun source target => set (npair_pack source target).

Lemma pair_set_periodic_relation : forall d (set : NVec (d + d) -> Prop),
    PeriodicNSet set -> PeriodicNRelation (PairSetRelation set).
Proof.
  intros d set [Hzero Hadd]. split.
  - unfold PairSetRelation, npair_pack. rewrite <- nvec_zero_append_local.
    exact Hzero.
  - intros x1 y1 x2 y2 H1 H2. unfold PairSetRelation in *.
    rewrite <- npair_pack_add. now apply Hadd.
Qed.

Lemma pair_set_as_z_same : forall d (set : NVec (d + d) -> Prop),
    SameSet
      (ZRelationPairs (NRelationAsZ (PairSetRelation set)))
      (NSetAsZ set).
Proof.
  intros d set pair. split.
  - intros [left [right [Hleft [Hright Hset]]]].
    exists (npair_pack left right). split; [|exact Hset].
    unfold ZRelationPairs in Hleft, Hright.
    rewrite <- (zpair_pack_split d pair), Hleft, Hright.
    symmetry. apply nvec_to_zvec_append.
  - intros [natural [-> Hset]].
    unfold ZRelationPairs, NRelationAsZ, PairSetRelation.
    exists (npair_left natural), (npair_right natural). repeat split.
    + pose proof (nvec_to_zvec_append d d
        (npair_left natural) (npair_right natural)) as Heq.
      change (nvec_to_zvec (npair_pack (npair_left natural)
        (npair_right natural)) = zpair_pack (nvec_to_zvec (npair_left natural))
        (nvec_to_zvec (npair_right natural))) in Heq.
      rewrite npair_pack_split in Heq.
      pose proof (f_equal (@zpair_left d) Heq) as Hleft.
      now rewrite zpair_left_pack in Hleft.
    + pose proof (nvec_to_zvec_append d d
        (npair_left natural) (npair_right natural)) as Heq.
      change (nvec_to_zvec (npair_pack (npair_left natural)
        (npair_right natural)) = zpair_pack (nvec_to_zvec (npair_left natural))
        (nvec_to_zvec (npair_right natural))) in Heq.
      rewrite npair_pack_split in Heq.
      pose proof (f_equal (@zpair_right d) Heq) as Hright.
      now rewrite zpair_right_pack in Hright.
    + now rewrite npair_pack_split.
Qed.

Lemma pair_set_asymptotically_definable_relation : forall d
    (set : NVec (d + d) -> Prop),
    AsymptoticallyDefinableNSet set ->
    AsymptoticallyDefinableNRelation (PairSetRelation set).
Proof.
  intros d set [Hperiodic Hdef]. split.
  - now apply pair_set_periodic_relation.
  - eapply qdefinable_congr; [|exact Hdef]. intro point.
    symmetry. apply cone_same_generators. intro integer.
    exact (pair_set_as_z_same d set integer).
Qed.

Definition pair_set_component {d}
    (component : AlmostSemilinearNComponentSet (d + d)) :
    AlmostSemilinearNComponent d :=
  {| AlmostBaseInput := npair_left (AlmostSetBase component);
     AlmostBaseOutput := npair_right (AlmostSetBase component);
     AlmostPeriodRelation := PairSetRelation (AlmostSetPeriod component) |}.

Lemma almost_semilinear_pair_set_relation : forall d
    (set : NVec (d + d) -> Prop),
    AlmostSemilinearNSet set ->
    AlmostSemilinearNRelation (PairSetRelation set).
Proof.
  intros d set [components [Hasym Hset]].
  exists (List.map pair_set_component components). split.
  - apply List.Forall_forall. intros projected Hin.
    apply in_map_iff in Hin as [component [<- Hin]]. cbn.
    apply pair_set_asymptotically_definable_relation.
    exact (proj1 (List.Forall_forall _ _) Hasym component Hin).
  - intros source target. unfold PairSetRelation. rewrite Hset. split.
    + intros [component [Hin [offset [Hperiod Heq]]]].
      exists (pair_set_component component). split; [now apply in_map|].
      exists (npair_left offset), (npair_right offset). cbn. repeat split.
      * unfold PairSetRelation. now rewrite npair_pack_split.
      * pose proof (f_equal (@npair_left d) Heq) as Hleft.
        now rewrite npair_left_pack, npair_left_add in Hleft.
      * pose proof (f_equal (@npair_right d) Heq) as Hright.
        now rewrite npair_right_pack, npair_right_add in Hright.
    + intros [projected [Hin [left [right [Hperiod [Hleft Hright]]]]]].
      apply in_map_iff in Hin as [component [Heq Hin]].
      subst projected. cbn in *. exists component. split; [exact Hin|].
      exists (npair_pack left right). split; [exact Hperiod|].
      rewrite Hleft, Hright, <- npair_pack_add, npair_pack_split.
      reflexivity.
Qed.

Definition DoubledReachRestricted {d} (system : IBVAS d)
    (H : NRelation d) (value : NVec (doubled_dimension d)) : Prop :=
  DoubledRestriction H value /\
  SReach (one_state_sbvas (doubled_system system)) Fin.F1 value.

Lemma doubled_projection_iff : forall d (system : IBVAS d)
    (H : NRelation d) pair,
    ProjectNSet (doubled_pair_selection d)
      (DoubledReachRestricted system H) pair <->
    H (npair_left pair) (npair_right pair) /\
      SpecialLeafReach system (npair_left pair) (npair_right pair).
Proof.
  intros d system H pair. split.
  - intros [value [[[Hmarker Hrelation] Hreach] Hcoordinates]].
    assert (Epair : pair = doubled_pair value).
    { apply StdVector.eq_nth_iff. intros index index' <-.
      rewrite (Hcoordinates index), doubled_pair_selection_correct.
      reflexivity. }
    split.
    + subst pair. exact Hrelation.
    + rewrite Epair. apply (proj2 (doubled_marker_one_iff d system
        (doubled_input value) (doubled_output value))).
      exists (doubled_marker value). split; [exact Hmarker|].
      rewrite doubled_repack. now apply one_state_reach_backward in Hreach.
  - intros [Hrelation Hspecial].
    apply (proj1 (doubled_marker_one_iff d system
      (npair_left pair) (npair_right pair))) in Hspecial.
    destruct Hspecial as [marker [Hmarker Hreach]].
    exists (doubled_pack marker (npair_left pair) (npair_right pair)). split.
    + split.
      * split.
        -- now rewrite (proj1 (doubled_unpack_pack d marker
             (npair_left pair) (npair_right pair))).
        -- destruct (doubled_unpack_pack d marker
             (npair_left pair) (npair_right pair)) as [_ [Hin Hout]].
           now rewrite Hin, Hout.
      * apply one_state_reach_forward. exact Hreach.
    + intro index. rewrite <- doubled_pair_selection_correct.
      unfold doubled_pair, doubled_pack. rewrite shiftin_right_append.
      now rewrite npair_pack_split.
Qed.

Theorem lemma_4_6_special_leaf_inter_semilinear : forall d
    (system : IBVAS d) (H : NRelation d),
    SemilinearNRelation H ->
    AlmostSemilinearNRelation
      (fun input output => H input output /\
        SpecialLeafReach system input output).
Proof.
  intros d system H HH.
  pose proof (bvass_reach_inter_semilinear
    (doubled_dimension d) 1 (one_state_sbvas (doubled_system system))
    (fun config => DoubledRestriction H (snd config))
    (doubled_restriction_stateful_semilinear d H HH)) as Hreach.
  specialize (Hreach Fin.F1).
  pose proof (almost_semilinear_nset_coordinate_projection
    (doubled_dimension d) (d + d) (doubled_pair_selection d)
    (DoubledReachRestricted system H) Hreach) as Hprojected.
  pose proof (almost_semilinear_pair_set_relation d
    (ProjectNSet (doubled_pair_selection d)
      (DoubledReachRestricted system H)) Hprojected) as Hpair.
  eapply (almost_semilinear_nrelation_congr d
    (PairSetRelation (ProjectNSet (doubled_pair_selection d)
      (DoubledReachRestricted system H)))
    (fun input output => H input output /\
      SpecialLeafReach system input output)).
  - intros input output. unfold PairSetRelation.
    rewrite doubled_projection_iff, npair_left_pack, npair_right_pack.
    reflexivity.
  - exact Hpair.
Qed.
