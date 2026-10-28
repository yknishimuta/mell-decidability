From Coq Require Import List Vector ZArith Lia Bool Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVASS Require Import Stateful VASSSection BoundedVASSSection.
From Mell.VAS Require Import Runs StatefulVAS.
From Mell.Reduction Require Import StateErasure FullZeroSystem MELLToABVASS.

Import ListNotations.
Local Open Scope nat_scope.

(** A proof-relevant, branch-local bound on the number of full zero tests.
    The bound is consumed only by a test; unary and split rules preserve it. *)
Inductive FullZeroReachBounded {d State}
    (system : FullZeroBVASS d State) : nat -> State -> NVec d -> Prop :=
| full_zero_bounded_leaf : forall fuel state,
    List.In state (full_zero_leaves system) ->
    FullZeroReachBounded system fuel state (nvec_zero d)
| full_zero_bounded_unary : forall fuel rule source_counters target_counters,
    List.In rule (full_zero_unary_rules system) ->
    add_displacement (unary_zero_delta d State rule) [source_counters] =
      Some target_counters ->
    FullZeroReachBounded system fuel
      (unary_zero_target d State rule) target_counters ->
    FullZeroReachBounded system fuel
      (unary_zero_source d State rule) source_counters
| full_zero_bounded_split : forall fuel rule source_counters
      left_counters right_counters,
    List.In rule (full_zero_split_rules system) ->
    source_counters = nvec_add left_counters right_counters ->
    FullZeroReachBounded system fuel
      (split_zero_left State rule) left_counters ->
    FullZeroReachBounded system fuel
      (split_zero_right State rule) right_counters ->
    FullZeroReachBounded system fuel
      (split_zero_source State rule) source_counters
| full_zero_bounded_test : forall fuel rule,
    List.In rule (full_zero_test_rules system) ->
    FullZeroReachBounded system fuel
      (full_zero_target State rule) (nvec_zero d) ->
    FullZeroReachBounded system (S fuel)
      (full_zero_source State rule) (nvec_zero d).

Lemma full_zero_bounded_reach : forall d State
    (system : FullZeroBVASS d State) fuel state counters,
  FullZeroReachBounded system fuel state counters ->
  FullZeroReach system state counters.
Proof.
  intros d State system fuel state counters H.
  induction H.
  - now constructor.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
Qed.

Lemma full_zero_bounded_mono : forall d State
    (system : FullZeroBVASS d State) fuel state counters,
  FullZeroReachBounded system fuel state counters ->
  forall extra, FullZeroReachBounded system (fuel + extra) state counters.
Proof.
  intros d State system fuel state counters H.
  induction H; intro extra.
  - constructor; assumption.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - replace (S fuel + extra) with (S (fuel + extra)) by lia.
    econstructor 4; eauto.
Qed.

(** The finite state support of a concrete machine.  Duplicates are harmless:
    they merely create unreachable duplicate numeric codes. *)
Definition unary_zero_states {d State} (rule : UnaryZeroRule d State) :=
  [unary_zero_source d State rule; unary_zero_target d State rule].

Definition split_zero_states {State} (rule : SplitZeroRule State) :=
  [split_zero_source State rule; split_zero_left State rule;
   split_zero_right State rule].

Definition test_zero_states {State} (rule : FullZeroRule State) :=
  [full_zero_source State rule; full_zero_target State rule].

Definition full_zero_states {d State} (system : FullZeroBVASS d State) :
    list State :=
  full_zero_leaves system ++
  List.flat_map unary_zero_states (full_zero_unary_rules system) ++
  List.flat_map split_zero_states (full_zero_split_rules system) ++
  List.flat_map test_zero_states (full_zero_test_rules system).

Definition full_zero_state_count {d State}
    (system : FullZeroBVASS d State) : nat :=
  S (length (full_zero_states system)).

Fixpoint state_index_nat {State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (values : list State) (value : State) : nat :=
  match values with
  | [] => 0
  | head :: tail =>
      if eq_dec value head then 0 else S (state_index_nat eq_dec tail value)
  end.

Lemma state_index_nat_bound : forall State eq_dec values value,
  state_index_nat (State := State) eq_dec values value < S (length values).
Proof.
  intros State eq_dec values; induction values as [|head tail IH]; intro value;
    cbn; [lia|]. destruct (eq_dec value head); [lia|]. specialize (IH value); lia.
Qed.

Definition state_index {State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (values : list State) (value : State) : Fin.t (S (length values)) :=
  Fin.of_nat_lt (state_index_nat_bound State eq_dec values value).

Lemma state_index_nat_in : forall (State : Type)
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (values : list State) (value : State),
  List.In value values ->
  List.nth_error values (state_index_nat eq_dec values value) = Some value.
Proof.
  intros State eq_dec values; induction values as [|head tail IH];
    intros value Hin; cbn in *; [contradiction|].
  destruct (eq_dec value head) as [->|Hneq]; cbn; [reflexivity|].
  apply IH. destruct Hin as [Heq|Hin]; [exfalso; apply Hneq; symmetry; exact Heq|assumption].
Qed.

Definition layered_state_count {d State}
    (system : FullZeroBVASS d State) : nat :=
  full_zero_state_count system * full_zero_state_count system.

Definition layered_dimension {d State}
    (system : FullZeroBVASS d State) : nat :=
  full_zero_state_count system * d.

Definition layered_state {d State} (system : FullZeroBVASS d State)
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (layer : Fin.t (full_zero_state_count system)) (state : State) :
    Fin.t (layered_state_count system).
Proof.
  unfold layered_state_count.
  refine (Fin.of_nat_lt (p :=
    proj1_sig (Fin.to_nat layer) * full_zero_state_count system +
    proj1_sig (Fin.to_nat
      (state_index eq_dec (full_zero_states system) state))) _).
  pose proof (proj2_sig (Fin.to_nat layer)) as Hlayer.
  pose proof (proj2_sig (Fin.to_nat
    (state_index eq_dec (full_zero_states system) state))) as Hstate.
  eapply Nat.lt_le_trans.
  - apply Nat.add_lt_mono_l. exact Hstate.
  - rewrite <- Nat.mul_succ_l. apply Nat.mul_le_mono_r.
    exact Hlayer.
Defined.

Definition layered_nvec {d State} (system : FullZeroBVASS d State)
    (layer : nat) (value : NVec d) : NVec (layered_dimension system) :=
  block_n_at (full_zero_state_count system) layer value.

Definition layered_zvec {d State} (system : FullZeroBVASS d State)
    (layer : nat) (value : ZVec d) : ZVec (layered_dimension system) :=
  block_z_at (full_zero_state_count system) layer value.

Definition zvec_opp {d} (value : ZVec d) : ZVec d := Vector.map Z.opp value.

Definition fin_of_lt (n value : nat) (bound : value < n) : Fin.t n :=
  Fin.of_nat_lt bound.

Definition layered_unary_rule {d State} (system : FullZeroBVASS d State)
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (layer : Fin.t (full_zero_state_count system))
    (rule : UnaryZeroRule d State) :
    SRule (layered_dimension system) (layered_state_count system) :=
  {| input_states := [layered_state system eq_dec layer
        (unary_zero_target d State rule)];
     input_nonempty := fun H => match H with end;
     output_state := layered_state system eq_dec layer
        (unary_zero_source d State rule);
     rule_delta := layered_zvec system (proj1_sig (Fin.to_nat layer))
        (zvec_opp (unary_zero_delta d State rule)) |}.

Definition layered_split_rule {d State} (system : FullZeroBVASS d State)
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (layer : Fin.t (full_zero_state_count system))
    (rule : SplitZeroRule State) :
    SRule (layered_dimension system) (layered_state_count system) :=
  {| input_states :=
       [layered_state system eq_dec layer (split_zero_left State rule);
        layered_state system eq_dec layer (split_zero_right State rule)];
     input_nonempty := fun H => match H with end;
     output_state := layered_state system eq_dec layer
        (split_zero_source State rule);
     rule_delta := zvec_zero (layered_dimension system) |}.

Definition layered_test_rule {d State} (system : FullZeroBVASS d State)
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (layer : Fin.t (length (full_zero_states system)))
    (rule : FullZeroRule State) :
    SRule (layered_dimension system) (layered_state_count system).
Proof.
  assert (Hcurrent : proj1_sig (Fin.to_nat layer) <
      full_zero_state_count system).
  { unfold full_zero_state_count. apply Nat.lt_lt_succ_r.
    exact (proj2_sig (Fin.to_nat layer)). }
  set (current := Fin.of_nat_lt Hcurrent : Fin.t (full_zero_state_count system)).
  set (next := Fin.FS layer : Fin.t (full_zero_state_count system)).
  refine {| input_states := [layered_state system eq_dec next
               (full_zero_target State rule)];
            input_nonempty := _;
            output_state := layered_state system eq_dec current
               (full_zero_source State rule);
            rule_delta := zvec_zero (layered_dimension system) |}.
  discriminate.
Defined.

Definition layered_initials {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) :=
  List.flat_map (fun layer =>
    List.map (fun state =>
      (layered_state system eq_dec layer state,
       nvec_zero (layered_dimension system)))
      (full_zero_leaves system))
    (all_fin (full_zero_state_count system)).

Definition layered_unary_rules {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) :=
  List.flat_map (fun layer =>
    List.map (layered_unary_rule system eq_dec layer)
      (full_zero_unary_rules system))
    (all_fin (full_zero_state_count system)).

Definition layered_split_rules {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) :=
  List.flat_map (fun layer =>
    List.map (layered_split_rule system eq_dec layer)
      (full_zero_split_rules system))
    (all_fin (full_zero_state_count system)).

Definition layered_test_rules {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) :=
  List.flat_map (fun layer =>
    List.map (layered_test_rule system eq_dec layer)
      (full_zero_test_rules system))
    (all_fin (length (full_zero_states system))).

Definition remove_zero_tests {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) :
    SBVAS (layered_dimension system) (layered_state_count system) :=
  {| initial_configs := layered_initials eq_dec system;
     stateful_rules := layered_unary_rules eq_dec system ++
       layered_split_rules eq_dec system ++ layered_test_rules eq_dec system |}.

Definition zero_test_root_state {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) (state : State) :
    Fin.t (layered_state_count system) :=
  layered_state system eq_dec Fin.F1 state.

Definition zero_test_root_counters {d State}
    (system : FullZeroBVASS d State) (value : NVec d) :
    NVec (layered_dimension system) :=
  layered_nvec system 0 value.

Theorem remove_zero_tests_fork_free : forall d State
    (system : FullZeroBVASS d State),
  ForkFreeFullZeroBVASS system.
Proof. intros; exact I. Qed.

(** Explicit witnesses are used only to normalize repeated zero-labelled
    states.  They do not change the public [FullZeroReach] semantics. *)
Inductive FullZeroRun (d : nat) (State : Type) : Type :=
| fzrun_leaf : State -> FullZeroRun d State
| fzrun_unary : UnaryZeroRule d State -> NVec d -> NVec d ->
    FullZeroRun d State -> FullZeroRun d State
| fzrun_split : SplitZeroRule State -> NVec d -> NVec d -> NVec d ->
    FullZeroRun d State -> FullZeroRun d State -> FullZeroRun d State
| fzrun_test : FullZeroRule State -> FullZeroRun d State ->
    FullZeroRun d State.

Arguments fzrun_leaf {d State} _.
Arguments fzrun_unary {d State} _ _ _ _.
Arguments fzrun_split {d State} _ _ _ _ _ _.
Arguments fzrun_test {d State} _ _.

Definition full_zero_run_root {d State} (run : FullZeroRun d State) :
    State * NVec d :=
  match run with
  | fzrun_leaf state => (state, nvec_zero d)
  | fzrun_unary rule source _ _ =>
      (unary_zero_source d State rule, source)
  | fzrun_split rule source _ _ _ _ =>
      (split_zero_source State rule, source)
  | fzrun_test rule _ =>
      (full_zero_source State rule, nvec_zero d)
  end.

Inductive ValidFullZeroRun {d State} (system : FullZeroBVASS d State) :
    FullZeroRun d State -> Prop :=
| valid_fzrun_leaf : forall state,
    List.In state (full_zero_leaves system) ->
    ValidFullZeroRun system (fzrun_leaf state)
| valid_fzrun_unary : forall rule source target child,
    List.In rule (full_zero_unary_rules system) ->
    add_displacement (unary_zero_delta d State rule) [source] = Some target ->
    ValidFullZeroRun system child ->
    full_zero_run_root child = (unary_zero_target d State rule, target) ->
    ValidFullZeroRun system (fzrun_unary rule source target child)
| valid_fzrun_split : forall rule source left right left_run right_run,
    List.In rule (full_zero_split_rules system) ->
    source = nvec_add left right ->
    ValidFullZeroRun system left_run ->
    full_zero_run_root left_run = (split_zero_left State rule, left) ->
    ValidFullZeroRun system right_run ->
    full_zero_run_root right_run = (split_zero_right State rule, right) ->
    ValidFullZeroRun system
      (fzrun_split rule source left right left_run right_run)
| valid_fzrun_test : forall rule child,
    List.In rule (full_zero_test_rules system) ->
    ValidFullZeroRun system child ->
    full_zero_run_root child =
      (full_zero_target State rule, nvec_zero d) ->
    ValidFullZeroRun system (fzrun_test rule child).

Lemma full_zero_reach_has_run : forall d State
    (system : FullZeroBVASS d State) state counters,
  FullZeroReach system state counters ->
  exists run, ValidFullZeroRun system run /\
    full_zero_run_root run = (state, counters).
Proof.
  intros d State system state counters Hreach. induction Hreach.
  - exists (fzrun_leaf state). split; [constructor; assumption|reflexivity].
  - destruct IHHreach as [child [Hvalid Hroot]].
    exists (fzrun_unary rule source_counters target_counters child).
    split; [econstructor; eauto|reflexivity].
  - destruct IHHreach1 as [left_run [Hleft Hleftroot]].
    destruct IHHreach2 as [right_run [Hright Hrightroot]].
    exists (fzrun_split rule source_counters left_counters right_counters
      left_run right_run). split; [econstructor; eauto|reflexivity].
  - destruct IHHreach as [child [Hvalid Hroot]].
    exists (fzrun_test rule child). split; [econstructor; eauto|reflexivity].
Qed.

Lemma valid_full_zero_run_reach : forall d State
    (system : FullZeroBVASS d State) run,
  ValidFullZeroRun system run ->
  FullZeroReach system (fst (full_zero_run_root run))
    (snd (full_zero_run_root run)).
Proof.
  intros d State system run Hvalid.
  induction Hvalid as
    [state Hin
    |rule source target child Hin Hadd Hchild IH Hroot
    |rule source left right left_run right_run Hin Hsum
       Hleft IHleft Hleftroot Hright IHright Hrightroot
    |rule child Hin Hchild IH Hroot]; cbn.
  - constructor; assumption.
  - rewrite Hroot in IH. cbn in IH.
    econstructor 2; eauto.
  - rewrite Hleftroot in IHleft. rewrite Hrightroot in IHright.
    cbn in IHleft, IHright. econstructor 3; eauto.
  - rewrite Hroot in IH. cbn in IH.
    econstructor 4; eauto.
Qed.

Fixpoint full_zero_run_size {d State} (run : FullZeroRun d State) : nat :=
  match run with
  | fzrun_leaf _ => 1
  | fzrun_unary _ _ _ child => S (full_zero_run_size child)
  | fzrun_split _ _ _ _ left_run right_run =>
      S (full_zero_run_size left_run + full_zero_run_size right_run)
  | fzrun_test _ child => S (full_zero_run_size child)
  end.

Inductive FullZeroSubrun {d State} : FullZeroRun d State ->
    FullZeroRun d State -> Prop :=
| fzsub_here : forall run, FullZeroSubrun run run
| fzsub_unary : forall rule source target child sub,
    FullZeroSubrun child sub ->
    FullZeroSubrun (fzrun_unary rule source target child) sub
| fzsub_split_left : forall rule source left right left_run right_run sub,
    FullZeroSubrun left_run sub ->
    FullZeroSubrun
      (fzrun_split rule source left right left_run right_run) sub
| fzsub_split_right : forall rule source left right left_run right_run sub,
    FullZeroSubrun right_run sub ->
    FullZeroSubrun
      (fzrun_split rule source left right left_run right_run) sub
| fzsub_test : forall rule child sub,
    FullZeroSubrun child sub -> FullZeroSubrun (fzrun_test rule child) sub.

Lemma valid_full_zero_subrun : forall d State
    (system : FullZeroBVASS d State) run sub,
  ValidFullZeroRun system run -> FullZeroSubrun run sub ->
  ValidFullZeroRun system sub.
Proof.
  intros d State system run sub Hvalid Hsub.
  induction Hsub; inversion Hvalid; subst; auto.
Qed.

Fixpoint find_root_state {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (state : State) (run : FullZeroRun d State) : option (FullZeroRun d State) :=
  let below :=
    match run with
    | fzrun_leaf _ => None
    | fzrun_unary _ _ _ child => find_root_state eq_dec state child
    | fzrun_split _ _ _ _ left_run right_run =>
        match find_root_state eq_dec state left_run with
        | Some found => Some found
        | None => find_root_state eq_dec state right_run
        end
    | fzrun_test _ child => find_root_state eq_dec state child
    end in
  if eq_dec (fst (full_zero_run_root run)) state then
    if nvec_eq_dec (snd (full_zero_run_root run)) (nvec_zero d)
    then Some run else below
  else below.

Lemma find_root_state_sound : forall d State eq_dec state
    (run found : FullZeroRun d State),
  find_root_state eq_dec state run = Some found ->
  FullZeroSubrun run found /\
  full_zero_run_root found = (state, nvec_zero d).
Proof.
  intros d State eq_dec state run.
  induction run as [leaf|rule source target child IH
    |rule source left_value right_value left_run IHleft right_run IHright
    |rule child IH]; intro found; cbn [find_root_state full_zero_run_root].
  - destruct (eq_dec leaf state) as [Heq|Hneq] eqn:Hstate.
    + destruct (nvec_eq_dec (nvec_zero d) (nvec_zero d)) as [Hzero|Hbad]
        eqn:Hzero_dec.
      * intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec in H. inversion H.
        split; [constructor|].
        subst leaf. reflexivity.
      * exfalso. apply Hbad. reflexivity.
    + intro H. cbn in H. rewrite ?Hstate in H. discriminate.
  - destruct (eq_dec (unary_zero_source d State rule) state) as [Heq|Hneq]
      eqn:Hstate.
    + destruct (nvec_eq_dec source (nvec_zero d)) as [Hzero|Hnotzero]
        eqn:Hzero_dec.
      * intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec in H. inversion H.
        split; [constructor|].
        subst. reflexivity.
      * intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec in H.
        apply IH in H as [Hsub Hroot]. split; [now constructor|exact Hroot].
    + intro H. cbn in H. rewrite ?Hstate in H.
      apply IH in H as [Hsub Hroot]. split; [now constructor|exact Hroot].
  - destruct (find_root_state eq_dec state left_run) as [left_found|] eqn:Hfindleft.
    + destruct (eq_dec (split_zero_source State rule) state) as [Heq|Hneq]
        eqn:Hstate.
      * destruct (nvec_eq_dec source (nvec_zero d)) as [Hzero|Hnotzero]
          eqn:Hzero_dec.
        -- intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec in H. inversion H; subst found.
           split; [constructor|]. subst. reflexivity.
        -- intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec in H. inversion H; subst found.
           destruct (IHleft left_found eq_refl) as [Hsub Hroot].
           split; [eapply fzsub_split_left; exact Hsub|exact Hroot].
      * intro H. cbn in H. rewrite ?Hstate in H. inversion H; subst found.
        destruct (IHleft left_found eq_refl) as [Hsub Hroot].
        split; [eapply fzsub_split_left; exact Hsub|exact Hroot].
    + destruct (eq_dec (split_zero_source State rule) state) as [Heq|Hneq]
        eqn:Hstate.
      * destruct (nvec_eq_dec source (nvec_zero d)) as [Hzero|Hnotzero]
          eqn:Hzero_dec.
        -- intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec in H. inversion H.
           split; [constructor|]. subst. reflexivity.
        -- intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec, ?Hfindleft in H.
           apply IHright in H as [Hsub Hroot].
           split; [eapply fzsub_split_right; exact Hsub|exact Hroot].
      * intro H. cbn in H. rewrite ?Hstate, ?Hfindleft in H.
        apply IHright in H as [Hsub Hroot].
        split; [eapply fzsub_split_right; exact Hsub|exact Hroot].
  - destruct (eq_dec (full_zero_source State rule) state) as [Heq|Hneq]
      eqn:Hstate.
    + destruct (nvec_eq_dec (nvec_zero d) (nvec_zero d)) as [Hzero|Hbad]
        eqn:Hzero_dec.
      * intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec in H. inversion H.
        split; [constructor|]. subst. reflexivity.
      * exfalso. apply Hbad. reflexivity.
    + intro H. cbn in H. rewrite ?Hstate in H.
      apply IH in H as [Hsub Hroot]. split; [now constructor|exact Hroot].
Qed.

Fixpoint normalize_full_zero_run {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (run : FullZeroRun d State) : FullZeroRun d State :=
  match run with
  | fzrun_leaf state => fzrun_leaf state
  | fzrun_unary rule source target child =>
      fzrun_unary rule source target (normalize_full_zero_run eq_dec child)
  | fzrun_split rule source left_value right_value left_run right_run =>
      fzrun_split rule source left_value right_value
        (normalize_full_zero_run eq_dec left_run)
        (normalize_full_zero_run eq_dec right_run)
  | fzrun_test rule child =>
      let child' := normalize_full_zero_run eq_dec child in
      match find_root_state eq_dec (full_zero_source State rule) child' with
      | Some found => found
      | None => fzrun_test rule child'
      end
  end.

Lemma normalize_full_zero_run_valid_root : forall d State eq_dec
    (system : FullZeroBVASS d State) run,
  ValidFullZeroRun system run ->
  ValidFullZeroRun system (normalize_full_zero_run eq_dec run) /\
  full_zero_run_root (normalize_full_zero_run eq_dec run) =
    full_zero_run_root run.
Proof.
  intros d State eq_dec system run Hvalid.
  induction Hvalid as
    [state Hin
    |rule source target child Hin Hadd Hchild [IHvalid IHroot] Hroot
    |rule source left right left_run right_run Hin Hsum
       Hleft [IHleft IHleftroot] Hleftroot
       Hright [IHright IHrightroot] Hrightroot
    |rule child Hin Hchild [IHvalid IHroot] Hroot]; cbn.
  - split; [constructor; assumption|reflexivity].
  - split.
    + econstructor; eauto. now rewrite IHroot.
    + reflexivity.
  - split.
    + econstructor; eauto; [now rewrite IHleftroot|now rewrite IHrightroot].
    + reflexivity.
  - remember (normalize_full_zero_run eq_dec child) as child' eqn:Hchild'.
    destruct (find_root_state eq_dec (full_zero_source State rule) child')
      as [found|] eqn:Hfind.
    + pose proof (find_root_state_sound d State eq_dec
        (full_zero_source State rule) child' found Hfind) as [Hsub Hfoundroot].
      split.
      * eapply valid_full_zero_subrun; eauto.
      * cbn. exact Hfoundroot.
    + split.
      * econstructor; eauto. rewrite IHroot. exact Hroot.
      * reflexivity.
Qed.

Definition root_is_zero_state {d State} (state : State)
    (run : FullZeroRun d State) : Prop :=
  full_zero_run_root run = (state, nvec_zero d).

Inductive ZeroStateAbsent {d State} (state : State) :
    FullZeroRun d State -> Prop :=
| zero_absent_leaf : forall leaf,
    leaf <> state -> ZeroStateAbsent state (fzrun_leaf leaf)
| zero_absent_unary : forall rule source target child,
    (unary_zero_source d State rule <> state \/ source <> nvec_zero d) ->
    ZeroStateAbsent state child ->
    ZeroStateAbsent state (fzrun_unary rule source target child)
| zero_absent_split : forall rule source left right left_run right_run,
    (split_zero_source State rule <> state \/ source <> nvec_zero d) ->
    ZeroStateAbsent state left_run -> ZeroStateAbsent state right_run ->
    ZeroStateAbsent state
      (fzrun_split rule source left right left_run right_run)
| zero_absent_test : forall rule child,
    full_zero_source State rule <> state ->
    ZeroStateAbsent state child ->
    ZeroStateAbsent state (fzrun_test rule child).

Lemma find_root_state_none_absent : forall d State eq_dec state
    (run : FullZeroRun d State),
  find_root_state eq_dec state run = None -> ZeroStateAbsent state run.
Proof.
  intros d State eq_dec state run.
  induction run as [leaf|rule source target child IH
    |rule source left right left_run IHleft right_run IHright
    |rule child IH]; cbn [find_root_state full_zero_run_root].
  - destruct (eq_dec leaf state) as [Heq|Hneq] eqn:Hstate.
    + destruct (nvec_eq_dec (nvec_zero d) (nvec_zero d)) as [Hz|Hbad]
        eqn:Hzero.
      * intro H. cbn in H. rewrite ?Hstate, ?Hzero in H. discriminate.
      * exfalso. apply Hbad. reflexivity.
    + intro Hnone. constructor; exact Hneq.
  - destruct (eq_dec (unary_zero_source d State rule) state) as [Heq|Hneq]
      eqn:Hstate.
    + destruct (nvec_eq_dec source (nvec_zero d)) as [Hzero|Hnotzero]
        eqn:Hzero_dec.
      * intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec in H. discriminate.
      * intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec in H.
        constructor; [now right|]. apply IH. exact H.
    + intro H. cbn in H. rewrite ?Hstate in H.
      constructor; [now left|]. apply IH. exact H.
  - destruct (find_root_state eq_dec state left_run) eqn:Hleft.
    + destruct (eq_dec (split_zero_source State rule) state) eqn:Hstate.
      * destruct (nvec_eq_dec source (nvec_zero d)) eqn:Hzero.
        -- intro H. cbn in H. rewrite ?Hstate, ?Hzero in H. discriminate.
        -- intro H. cbn in H. rewrite ?Hstate, ?Hzero, ?Hleft in H. discriminate.
      * intro H. cbn in H. rewrite ?Hstate, ?Hleft in H. discriminate.
    + destruct (eq_dec (split_zero_source State rule) state) as [Heq|Hneq]
        eqn:Hstate.
      * destruct (nvec_eq_dec source (nvec_zero d)) as [Hzero|Hnotzero]
          eqn:Hzero_dec.
        -- intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec, ?Hleft in H.
           discriminate.
        -- intro H. cbn in H. rewrite ?Hstate, ?Hzero_dec, ?Hleft in H.
           eapply zero_absent_split; [now right|apply IHleft; exact eq_refl|].
           apply IHright. exact H.
      * intro H. cbn in H. rewrite ?Hstate, ?Hleft in H.
        eapply zero_absent_split; [now left|apply IHleft; exact eq_refl|].
        apply IHright. exact H.
  - destruct (eq_dec (full_zero_source State rule) state) as [Heq|Hneq]
      eqn:Hstate.
    + destruct (nvec_eq_dec (nvec_zero d) (nvec_zero d)) as [Hz|Hbad]
        eqn:Hzero.
      * intro H. cbn in H. rewrite ?Hstate, ?Hzero in H. discriminate.
      * exfalso. apply Hbad. reflexivity.
    + intro H. cbn in H. rewrite ?Hstate in H.
      constructor; [exact Hneq|]. apply IH. exact H.
Qed.

Inductive ZeroSimple {d State} : FullZeroRun d State -> Prop :=
| zero_simple_leaf : forall state, ZeroSimple (fzrun_leaf state)
| zero_simple_unary : forall rule source target child,
    ZeroSimple child -> ZeroSimple (fzrun_unary rule source target child)
| zero_simple_split : forall rule source left right left_run right_run,
    ZeroSimple left_run -> ZeroSimple right_run ->
    ZeroSimple (fzrun_split rule source left right left_run right_run)
| zero_simple_test : forall rule child,
    ZeroSimple child ->
    ZeroStateAbsent (full_zero_source State rule) child ->
    ZeroSimple (fzrun_test rule child).

Lemma normalize_full_zero_run_simple : forall d State eq_dec
    (run : FullZeroRun d State),
  ZeroSimple (normalize_full_zero_run eq_dec run).
Proof.
  intros d State eq_dec run. induction run as
    [state|rule source target child IH
    |rule source left right left_run IHleft right_run IHright
    |rule child IH]; cbn.
  - constructor.
  - now constructor.
  - now constructor.
  - remember (normalize_full_zero_run eq_dec child) as child' eqn:Hchild'.
    destruct (find_root_state eq_dec (full_zero_source State rule) child')
      as [found|] eqn:Hfind.
    + pose proof (find_root_state_sound d State eq_dec
        (full_zero_source State rule) child' found Hfind) as [Hsub _].
      clear Hfind. subst child'.
      induction Hsub; inversion IH; subst; auto using ZeroSimple.
    + constructor; [exact IH|].
      now apply (find_root_state_none_absent d State eq_dec
        (full_zero_source State rule) child').
Qed.

Fixpoint full_zero_test_depth {d State} (run : FullZeroRun d State) : nat :=
  match run with
  | fzrun_leaf _ => 0
  | fzrun_unary _ _ _ child => full_zero_test_depth child
  | fzrun_split _ _ _ _ left_run right_run =>
      Nat.max (full_zero_test_depth left_run) (full_zero_test_depth right_run)
  | fzrun_test _ child => S (full_zero_test_depth child)
  end.

Inductive FullZeroTrace {d State} : FullZeroRun d State -> list State -> Prop :=
| fztrace_leaf : forall state, FullZeroTrace (fzrun_leaf state) []
| fztrace_unary : forall rule source target child trace,
    FullZeroTrace child trace ->
    FullZeroTrace (fzrun_unary rule source target child) trace
| fztrace_split_left : forall rule source left right left_run right_run trace,
    FullZeroTrace left_run trace ->
    FullZeroTrace (fzrun_split rule source left right left_run right_run) trace
| fztrace_split_right : forall rule source left right left_run right_run trace,
    FullZeroTrace right_run trace ->
    FullZeroTrace (fzrun_split rule source left right left_run right_run) trace
| fztrace_test : forall rule child trace,
    FullZeroTrace child trace ->
    FullZeroTrace (fzrun_test rule child)
      (full_zero_source State rule :: trace).

Lemma full_zero_trace_max : forall d State (run : FullZeroRun d State),
  exists trace, FullZeroTrace run trace /\
    length trace = full_zero_test_depth run.
Proof.
  intros d State run. induction run as
    [state|rule source target child [trace [Htrace Hlength]]
    |rule source left right left_run [left_trace [Hleft Hleftlen]]
       right_run [right_trace [Hright Hrightlen]]
    |rule child [trace [Htrace Hlength]]]; cbn.
  - exists []; split; [constructor|reflexivity].
  - exists trace; split; [now constructor|exact Hlength].
  - destruct (Nat.max_dec (full_zero_test_depth left_run)
        (full_zero_test_depth right_run)) as [Hmax|Hmax].
    + exists left_trace. split; [now apply fztrace_split_left|].
      now rewrite Hleftlen, Hmax.
    + exists right_trace. split; [now apply fztrace_split_right|].
      now rewrite Hrightlen, Hmax.
  - exists (full_zero_source State rule :: trace).
    split; [now constructor|cbn; now rewrite Hlength].
Qed.

Lemma zero_absent_trace_notin : forall d State state
    (run : FullZeroRun d State) trace,
  ZeroStateAbsent state run -> FullZeroTrace run trace ->
  ~ List.In state trace.
Proof.
  intros d State state run trace Habs.
  revert trace. induction Habs; intros trace Htrace; inversion Htrace; subst; cbn.
  - tauto.
  - match goal with
    | IH : forall tr, FullZeroTrace ?r tr -> _,
      HT : FullZeroTrace ?r ?tr |- _ => exact (IH tr HT)
    end.
  - match goal with
    | IH : forall tr, FullZeroTrace ?r tr -> _,
      HT : FullZeroTrace ?r ?tr |- _ => exact (IH tr HT)
    end.
  - match goal with
    | IH : forall tr, FullZeroTrace ?r tr -> _,
      HT : FullZeroTrace ?r ?tr |- _ => exact (IH tr HT)
    end.
  - intros [Heq|Hin].
    + apply H. exact Heq.
    + exact (IHHabs trace0 H3 Hin).
Qed.

Lemma zero_simple_trace_nodup : forall d State
    (run : FullZeroRun d State) trace,
  ZeroSimple run -> FullZeroTrace run trace -> NoDup trace.
Proof.
  intros d State run trace Hsimple Htrace.
  induction Htrace; inversion Hsimple; subst; auto using NoDup.
  constructor.
  - eapply zero_absent_trace_notin; eauto.
  - auto.
Qed.

Lemma test_rule_source_in_states : forall d State
    (system : FullZeroBVASS d State) rule,
  List.In rule (full_zero_test_rules system) ->
  List.In (full_zero_source State rule) (full_zero_states system).
Proof.
  intros d State system rule Hin. unfold full_zero_states.
  apply in_or_app. right.
  apply in_or_app. right.
  apply in_or_app. right.
  apply in_flat_map. exists rule. split; [exact Hin|]. cbn; auto.
Qed.

Lemma valid_trace_in_states : forall d State
    (system : FullZeroBVASS d State) run trace,
  ValidFullZeroRun system run -> FullZeroTrace run trace ->
  incl trace (full_zero_states system).
Proof.
  intros d State system run trace Hvalid Htrace.
  revert Hvalid. induction Htrace; intro Hvalid; inversion Hvalid; subst; cbn.
  - apply incl_nil_l.
  - eauto.
  - eauto.
  - eauto.
  - intros state [Heq|Hin].
    + subst state. now apply test_rule_source_in_states.
    + eapply IHHtrace; eauto.
Qed.

Lemma zero_simple_test_depth_bound : forall d State
    (system : FullZeroBVASS d State) run,
  ValidFullZeroRun system run -> ZeroSimple run ->
  full_zero_test_depth run <= length (full_zero_states system).
Proof.
  intros d State system run Hvalid Hsimple.
  destruct (full_zero_trace_max d State run) as [trace [Htrace Hlength]].
  rewrite <- Hlength. eapply NoDup_incl_length.
  - eapply zero_simple_trace_nodup; eauto.
  - eapply valid_trace_in_states; eauto.
Qed.

Lemma valid_run_bounded_reach : forall d State
    (system : FullZeroBVASS d State) run,
  ValidFullZeroRun system run ->
  FullZeroReachBounded system (full_zero_test_depth run)
    (fst (full_zero_run_root run)) (snd (full_zero_run_root run)).
Proof.
  intros d State system run Hvalid.
  induction Hvalid as
    [state Hin
    |rule source target child Hin Hadd Hchild IH Hroot
    |rule source left right left_run right_run Hin Hsum
       Hleft IHleft Hleftroot Hright IHright Hrightroot
    |rule child Hin Hchild IH Hroot]; cbn.
  - constructor; assumption.
  - rewrite Hroot in IH. cbn in IH. econstructor 2; eauto.
  - rewrite Hleftroot in IHleft. rewrite Hrightroot in IHright.
    cbn in IHleft, IHright.
    set (fuel := Nat.max (full_zero_test_depth left_run)
      (full_zero_test_depth right_run)).
    econstructor 3; eauto.
    + eapply full_zero_bounded_mono with
        (extra := fuel - full_zero_test_depth left_run) in IHleft.
      replace (full_zero_test_depth left_run +
        (fuel - full_zero_test_depth left_run)) with fuel in IHleft by
        (unfold fuel; pose proof (Nat.le_max_l
          (full_zero_test_depth left_run)
          (full_zero_test_depth right_run)); lia).
      exact IHleft.
    + eapply full_zero_bounded_mono with
        (extra := fuel - full_zero_test_depth right_run) in IHright.
      replace (full_zero_test_depth right_run +
        (fuel - full_zero_test_depth right_run)) with fuel in IHright by
        (unfold fuel; pose proof (Nat.le_max_r
          (full_zero_test_depth left_run)
          (full_zero_test_depth right_run)); lia).
      exact IHright.
  - rewrite Hroot in IH. cbn in IH. econstructor 4; eauto.
Qed.

Theorem full_zero_reach_bounded : forall d State
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State) state counters,
  FullZeroReach system state counters ->
  FullZeroReachBounded system (length (full_zero_states system))
    state counters.
Proof.
  intros d State eq_dec system state counters Hreach.
  destruct (full_zero_reach_has_run d State system state counters Hreach)
    as [run [Hvalid Hroot]].
  pose proof (normalize_full_zero_run_valid_root d State eq_dec system run Hvalid)
    as [Hnormal Hnormalroot].
  pose proof (normalize_full_zero_run_simple d State eq_dec run) as Hsimple.
  pose proof (valid_run_bounded_reach d State system _ Hnormal) as Hbounded.
  pose proof (zero_simple_test_depth_bound d State system _ Hnormal Hsimple)
    as Hdepth.
  eapply full_zero_bounded_mono with
    (extra := length (full_zero_states system) -
      full_zero_test_depth (normalize_full_zero_run eq_dec run)) in Hbounded.
  replace (full_zero_test_depth (normalize_full_zero_run eq_dec run) +
      (length (full_zero_states system) -
       full_zero_test_depth (normalize_full_zero_run eq_dec run)))
    with (length (full_zero_states system)) in Hbounded by
      lia.
  rewrite Hnormalroot, Hroot in Hbounded. exact Hbounded.
Qed.

(** Projection of one counter block. *)
Definition block_coordinate {width count} (block : Fin.t count)
    (coordinate : Fin.t width) : Fin.t (count * width).
Proof.
  refine (Fin.of_nat_lt (p :=
    proj1_sig (Fin.to_nat block) * width +
    proj1_sig (Fin.to_nat coordinate)) _).
  pose proof (proj2_sig (Fin.to_nat block)) as Hblock.
  pose proof (proj2_sig (Fin.to_nat coordinate)) as Hcoordinate.
  assert (Hmul : S (proj1_sig (Fin.to_nat block)) * width <=
      count * width).
  { apply Nat.mul_le_mono_r. exact Hblock. }
  rewrite Nat.mul_succ_l in Hmul.
  eapply Nat.lt_le_trans; [apply Nat.add_lt_mono_l; exact Hcoordinate|exact Hmul].
Defined.

Definition block_project_n {width count} (block : Fin.t count)
    (value : NVec (count * width)) : NVec width :=
  vector_of_function width (fun coordinate =>
    Vector.nth value (block_coordinate block coordinate)).

Lemma block_project_n_block : forall width count (block : Fin.t count)
    (value : NVec width),
  block_project_n block
    (block_n_at count (proj1_sig (Fin.to_nat block)) value) = value.
Proof.
  intros width count block value.
  apply (proj1 (Vector.eq_nth_iff nat width _ _)).
  intros coordinate coordinate' Heq; subst coordinate'.
  unfold block_project_n. rewrite nth_vector_of_function.
  unfold block_n_at. rewrite nth_vector_of_function.
  unfold block_coordinate. rewrite Fin.to_nat_of_nat. cbn [proj1_sig].
  set (block_index := proj1_sig (Fin.to_nat block)).
  set (coordinate_index := proj1_sig (Fin.to_nat coordinate)).
  assert (Hlower : (block_index * width <=?
      block_index * width + coordinate_index)%nat = true).
  { apply Nat.leb_le. lia. }
  assert (Hupper : (block_index * width + coordinate_index <?
      S block_index * width)%nat = true).
  { apply Nat.ltb_lt. rewrite Nat.mul_succ_l.
    apply Nat.add_lt_mono_l. unfold coordinate_index.
    exact (proj2_sig (Fin.to_nat coordinate)). }
  rewrite Hlower, Hupper. cbn.
  replace (block_index * width + coordinate_index - block_index * width)%nat
    with coordinate_index by lia.
  symmetry. unfold coordinate_index.
  rewrite <- (to_list_nth_order nat width value
    (proj1_sig (Fin.to_nat coordinate))
    (proj2_sig (Fin.to_nat coordinate)) 0%nat).
  unfold Vector.nth_order. f_equal. apply Fin.to_nat_inj.
  rewrite Fin.to_nat_of_nat. reflexivity.
Qed.

Lemma block_n_at_injective : forall width count (block : Fin.t count)
    (left right : NVec width),
  block_n_at count (proj1_sig (Fin.to_nat block)) left =
  block_n_at count (proj1_sig (Fin.to_nat block)) right ->
  left = right.
Proof.
  intros width count block left right Heq.
  pose proof (f_equal (block_project_n block) Heq) as H.
  now rewrite !block_project_n_block in H.
Qed.

Lemma full_zero_leaf_in_states : forall d State
    (system : FullZeroBVASS d State) state,
  List.In state (full_zero_leaves system) ->
  List.In state (full_zero_states system).
Proof.
  intros. unfold full_zero_states. apply in_or_app. now left.
Qed.

Lemma unary_zero_source_in_states : forall d State
    (system : FullZeroBVASS d State) rule,
  List.In rule (full_zero_unary_rules system) ->
  List.In (unary_zero_source d State rule) (full_zero_states system).
Proof.
  intros d State system rule Hin. unfold full_zero_states.
  apply in_or_app. right. apply in_or_app. left.
  apply in_flat_map. exists rule. split; [exact Hin|]. cbn; auto.
Qed.

Lemma unary_zero_target_in_states : forall d State
    (system : FullZeroBVASS d State) rule,
  List.In rule (full_zero_unary_rules system) ->
  List.In (unary_zero_target d State rule) (full_zero_states system).
Proof.
  intros d State system rule Hin. unfold full_zero_states.
  apply in_or_app. right. apply in_or_app. left.
  apply in_flat_map. exists rule. split; [exact Hin|]. cbn; auto.
Qed.

Lemma split_zero_states_in : forall d State
    (system : FullZeroBVASS d State) rule,
  List.In rule (full_zero_split_rules system) ->
  List.In (split_zero_source State rule) (full_zero_states system) /\
  List.In (split_zero_left State rule) (full_zero_states system) /\
  List.In (split_zero_right State rule) (full_zero_states system).
Proof.
  intros d State system rule Hin. unfold full_zero_states.
  assert (Hsource : List.In (split_zero_source State rule)
      (List.flat_map split_zero_states (full_zero_split_rules system))).
  { apply in_flat_map. exists rule. split; [exact Hin|]. cbn; auto. }
  assert (Hleft : List.In (split_zero_left State rule)
      (List.flat_map split_zero_states (full_zero_split_rules system))).
  { apply in_flat_map. exists rule. split; [exact Hin|]. cbn; auto. }
  assert (Hright : List.In (split_zero_right State rule)
      (List.flat_map split_zero_states (full_zero_split_rules system))).
  { apply in_flat_map. exists rule. split; [exact Hin|]. cbn; auto. }
  repeat split; apply in_or_app; right; apply in_or_app; right;
    apply in_or_app; left; assumption.
Qed.

Lemma test_zero_target_in_states : forall d State
    (system : FullZeroBVASS d State) rule,
  List.In rule (full_zero_test_rules system) ->
  List.In (full_zero_target State rule) (full_zero_states system).
Proof.
  intros d State system rule Hin. unfold full_zero_states.
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
  apply in_flat_map. exists rule. split; [exact Hin|]. cbn; auto.
Qed.

Lemma state_index_injective_on_list : forall (State : Type)
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (values : list State) (left right : State),
  List.In left values -> List.In right values ->
  state_index_nat eq_dec values left = state_index_nat eq_dec values right ->
  left = right.
Proof.
  intros State eq_dec values left right Hleft Hright Heq.
  pose proof (state_index_nat_in State eq_dec values left Hleft) as Hl.
  pose proof (state_index_nat_in State eq_dec values right Hright) as Hr.
  rewrite Heq in Hl. congruence.
Qed.

Lemma fin_value_of_nat : forall n p (bound : p < n),
  proj1_sig (Fin.to_nat (Fin.of_nat_lt bound)) = p.
Proof.
  intros n p bound. pose proof (Fin.to_nat_of_nat bound) as H.
  exact (f_equal (@proj1_sig nat (fun i => i < n)) H).
Qed.

Lemma state_index_value : forall State eq_dec values value,
  proj1_sig (Fin.to_nat (state_index (State := State) eq_dec values value)) =
  state_index_nat eq_dec values value.
Proof.
  intros. unfold state_index. apply fin_value_of_nat.
Qed.

Lemma layered_state_injective : forall d State
    (system : FullZeroBVASS d State)
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (left_layer right_layer : Fin.t (full_zero_state_count system))
    left_state right_state,
  List.In left_state (full_zero_states system) ->
  List.In right_state (full_zero_states system) ->
  layered_state system eq_dec left_layer left_state =
    layered_state system eq_dec right_layer right_state ->
  left_layer = right_layer /\ left_state = right_state.
Proof.
  intros d State system eq_dec left_layer right_layer left_state right_state
    Hleft Hright Heq.
  unfold layered_state in Heq.
  pose proof (f_equal (fun index => proj1_sig (Fin.to_nat index)) Heq)
    as Hnat.
  cbn beta in Hnat. repeat rewrite fin_value_of_nat in Hnat.
  set (count := full_zero_state_count system) in *.
  pose proof (proj2_sig (Fin.to_nat
    (state_index eq_dec (full_zero_states system) left_state))) as Hlbound.
  pose proof (proj2_sig (Fin.to_nat
    (state_index eq_dec (full_zero_states system) right_state))) as Hrbound.
  assert (Hpacked : count * proj1_sig (Fin.to_nat left_layer) +
      proj1_sig (Fin.to_nat
        (state_index eq_dec (full_zero_states system) left_state)) =
      count * proj1_sig (Fin.to_nat right_layer) +
      proj1_sig (Fin.to_nat
        (state_index eq_dec (full_zero_states system) right_state))).
  { rewrite (Nat.mul_comm count (proj1_sig (Fin.to_nat left_layer))),
      (Nat.mul_comm count (proj1_sig (Fin.to_nat right_layer))). exact Hnat. }
  destruct (Nat.div_mod_unique count
    (proj1_sig (Fin.to_nat left_layer))
    (proj1_sig (Fin.to_nat right_layer))
    (proj1_sig (Fin.to_nat
      (state_index eq_dec (full_zero_states system) left_state)))
    (proj1_sig (Fin.to_nat
      (state_index eq_dec (full_zero_states system) right_state)))
    Hlbound Hrbound Hpacked) as [Hlayers Hremainders].
  split.
  - apply Fin.to_nat_inj. exact Hlayers.
  - eapply state_index_injective_on_list with
      (eq_dec := eq_dec) (values := full_zero_states system).
    + exact Hleft.
    + exact Hright.
    + rewrite <- !state_index_value. exact Hremainders.
Qed.

Lemma displacement_singleton_step_action : forall d (delta : ZVec d)
    source target,
  add_displacement delta [source] = Some target ->
  delta = StepAction source target.
Proof.
  intros d delta source target Happly.
  pose proof (add_displacement_exact_reduction d delta [source] target Happly)
    as Hexact.
  rewrite nvec_sum_singleton_reduction in Hexact.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  pose proof (f_equal (fun value => Vector.nth value index) Hexact) as Hnth.
  unfold zvec_add, nvec_to_zvec in Hnth.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (nth_map Z.of_nat source index index eq_refl),
    (nth_map Z.of_nat target index index eq_refl) in Hnth.
  unfold StepAction, zvec_sub_run, nvec_to_zvec.
  rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl),
    (nth_map Z.of_nat target index index eq_refl),
    (nth_map Z.of_nat source index index eq_refl). lia.
Qed.

Lemma zvec_opp_step_action : forall d (source target : NVec d),
  zvec_opp (StepAction source target) = StepAction target source.
Proof.
  intros d source target. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  unfold zvec_opp, StepAction, zvec_sub_run, nvec_to_zvec.
  rewrite (nth_map Z.opp _ index index eq_refl).
  repeat rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl).
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl). lia.
Qed.

Lemma layered_unary_apply : forall d State
    (system : FullZeroBVASS d State) layer rule source target,
  add_displacement (unary_zero_delta d State rule) [source] = Some target ->
  add_displacement
    (layered_zvec system layer (zvec_opp (unary_zero_delta d State rule)))
    [layered_nvec system layer target] =
  Some (layered_nvec system layer source).
Proof.
  intros d State system layer rule source target Happly.
  apply displacement_singleton_step_action in Happly.
  apply unary_add_displacement_of_action.
  unfold layered_zvec, layered_nvec.
  rewrite Happly, zvec_opp_step_action, block_z_at_step_action. reflexivity.
Qed.

Lemma layered_split_sum : forall d State
    (system : FullZeroBVASS d State) layer left right,
  nvec_add (layered_nvec system layer left)
    (layered_nvec system layer right) =
  layered_nvec system layer (nvec_add left right).
Proof.
  intros. unfold layered_nvec. symmetry. apply block_n_at_add.
Qed.

Lemma zero_displacement_two : forall d (left right : NVec d),
  add_displacement (zvec_zero d) [left; right] =
    Some (nvec_add left right).
Proof.
  intros. apply add_displacement_of_exact_reduction.
  rewrite nvec_sum_rsum_stateful. cbn [nvec_rsum_stateful].
  rewrite (nvec_add_comm_stateful d right (nvec_zero d)),
    nvec_add_zero_left_stateful, zvec_zero_add_reduction.
  reflexivity.
Qed.

Lemma zero_displacement_one : forall d (value : NVec d),
  add_displacement (zvec_zero d) [value] = Some value.
Proof.
  intros. apply add_displacement_of_exact_reduction.
  rewrite nvec_sum_singleton_reduction, zvec_zero_add_reduction. reflexivity.
Qed.

Lemma layered_initial_in : forall d State eq_dec
    (system : FullZeroBVASS d State)
    (layer : Fin.t (full_zero_state_count system)) state,
  List.In state (full_zero_leaves system) ->
  List.In (layered_state system eq_dec layer state,
      nvec_zero (layered_dimension system))
    (initial_configs (remove_zero_tests eq_dec system)).
Proof.
  intros. change (List.In
    (layered_state system eq_dec layer state,
     nvec_zero (layered_dimension system)) (layered_initials eq_dec system)).
  unfold layered_initials.
  apply in_flat_map. exists layer. split.
  - apply all_fin_complete.
  - apply List.in_map_iff. exists state. split; [reflexivity|assumption].
Qed.

Lemma layered_unary_rule_in : forall d State eq_dec
    (system : FullZeroBVASS d State)
    (layer : Fin.t (full_zero_state_count system)) rule,
  List.In rule (full_zero_unary_rules system) ->
  List.In (layered_unary_rule system eq_dec layer rule)
    (stateful_rules (remove_zero_tests eq_dec system)).
Proof.
  intros. change (List.In (layered_unary_rule system eq_dec layer rule)
    (layered_unary_rules eq_dec system ++ layered_split_rules eq_dec system ++
     layered_test_rules eq_dec system)).
  apply in_or_app. left.
  unfold layered_unary_rules.
  apply in_flat_map. exists layer. split; [apply all_fin_complete|].
  apply List.in_map_iff. exists rule. split; [reflexivity|assumption].
Qed.

Lemma layered_split_rule_in : forall d State eq_dec
    (system : FullZeroBVASS d State)
    (layer : Fin.t (full_zero_state_count system)) rule,
  List.In rule (full_zero_split_rules system) ->
  List.In (layered_split_rule system eq_dec layer rule)
    (stateful_rules (remove_zero_tests eq_dec system)).
Proof.
  intros. change (List.In (layered_split_rule system eq_dec layer rule)
    (layered_unary_rules eq_dec system ++ layered_split_rules eq_dec system ++
     layered_test_rules eq_dec system)).
  apply in_or_app. right. apply in_or_app. left.
  unfold layered_split_rules.
  apply in_flat_map. exists layer. split; [apply all_fin_complete|].
  apply List.in_map_iff. exists rule. split; [reflexivity|assumption].
Qed.

Lemma layered_test_rule_in : forall d State eq_dec
    (system : FullZeroBVASS d State)
    (layer : Fin.t (length (full_zero_states system))) rule,
  List.In rule (full_zero_test_rules system) ->
  List.In (layered_test_rule system eq_dec layer rule)
    (stateful_rules (remove_zero_tests eq_dec system)).
Proof.
  intros. change (List.In (layered_test_rule system eq_dec layer rule)
    (layered_unary_rules eq_dec system ++ layered_split_rules eq_dec system ++
     layered_test_rules eq_dec system)).
  apply in_or_app. right. apply in_or_app. right.
  unfold layered_test_rules.
  apply in_flat_map. exists layer. split; [apply all_fin_complete|].
  apply List.in_map_iff. exists rule. split; [reflexivity|assumption].
Qed.

Lemma full_zero_bounded_layered_reach : forall d State eq_dec
    (system : FullZeroBVASS d State) fuel state counters,
  FullZeroReachBounded system fuel state counters ->
  forall (layer : Fin.t (full_zero_state_count system)),
    proj1_sig (Fin.to_nat layer) + fuel < full_zero_state_count system ->
    SReach (remove_zero_tests eq_dec system)
      (layered_state system eq_dec layer state)
      (layered_nvec system (proj1_sig (Fin.to_nat layer)) counters).
Proof.
  intros d State eq_dec system fuel state counters Hbounded.
  induction Hbounded as
    [fuel state Hin
    |fuel rule source target Hin Hadd Hchild IH
    |fuel rule source left right Hin Hsum Hleft IHleft Hright IHright
    |fuel rule Hin Hchild IH]; intros layer Hlayer.
  - unfold layered_nvec. rewrite block_n_at_zero. apply sreach_initial.
    apply layered_initial_in. exact Hin.
  - eapply sreach_rule with
      (rule := layered_unary_rule system eq_dec layer rule)
      (child_configs := [(layered_state system eq_dec layer
          (unary_zero_target d State rule),
        layered_nvec system (proj1_sig (Fin.to_nat layer)) target)]).
    + apply layered_unary_rule_in. exact Hin.
    + constructor; [apply IH; exact Hlayer|constructor].
    + reflexivity.
    + apply layered_unary_apply. exact Hadd.
  - subst source. eapply sreach_rule with
      (rule := layered_split_rule system eq_dec layer rule)
      (child_configs :=
        [(layered_state system eq_dec layer (split_zero_left State rule),
          layered_nvec system (proj1_sig (Fin.to_nat layer)) left);
         (layered_state system eq_dec layer (split_zero_right State rule),
          layered_nvec system (proj1_sig (Fin.to_nat layer)) right)]).
    + apply layered_split_rule_in. exact Hin.
    + apply sreach_children_cons.
      * apply IHleft. exact Hlayer.
      * apply sreach_children_cons.
        -- apply IHright. exact Hlayer.
        -- apply sreach_children_nil.
    + reflexivity.
    + cbn [layered_split_rule].
      change (add_displacement (zvec_zero (layered_dimension system))
        [layered_nvec system (proj1_sig (Fin.to_nat layer)) left;
         layered_nvec system (proj1_sig (Fin.to_nat layer)) right] =
        Some (layered_nvec system (proj1_sig (Fin.to_nat layer))
          (nvec_add left right))).
      rewrite zero_displacement_two, layered_split_sum. reflexivity.
  - assert (Hsmall : proj1_sig (Fin.to_nat layer) <
        length (full_zero_states system)).
    { apply Nat.succ_lt_mono.
      eapply Nat.le_lt_trans; [|exact Hlayer].
      replace (S (proj1_sig (Fin.to_nat layer))) with
        (proj1_sig (Fin.to_nat layer) + 1) by lia.
      apply Nat.add_le_mono_l. lia. }
    set (small := Fin.of_nat_lt Hsmall :
      Fin.t (length (full_zero_states system))).
    assert (Hcurrent_bound : proj1_sig (Fin.to_nat layer) <
        full_zero_state_count system).
    { exact (proj2_sig (Fin.to_nat layer)). }
    set (current := Fin.of_nat_lt Hcurrent_bound :
      Fin.t (full_zero_state_count system)).
    set (next := Fin.FS small : Fin.t (full_zero_state_count system)).
    assert (Hcurrent :
      current = layer).
    { apply Fin.to_nat_inj. unfold current. rewrite Fin.to_nat_of_nat. reflexivity. }
    assert (Hnext : proj1_sig (Fin.to_nat next) =
        S (proj1_sig (Fin.to_nat layer))).
    { change (proj1_sig (Fin.to_nat (Fin.FS small)) =
          S (proj1_sig (Fin.to_nat layer))).
      rewrite fin_to_nat_FS_value.
      unfold small. rewrite Fin.to_nat_of_nat. reflexivity. }
    assert (Houtput : output_state (layered_test_rule system eq_dec small rule) =
        layered_state system eq_dec layer (full_zero_source State rule)).
    { apply Fin.to_nat_inj.
      cbv [output_state layered_test_rule layered_state].
      repeat rewrite fin_value_of_nat.
      unfold small. rewrite Fin.to_nat_of_nat.
      reflexivity. }
    rewrite <- Houtput.
    eapply sreach_rule with
      (rule := layered_test_rule system eq_dec small rule)
      (child_configs :=
        [(layered_state system eq_dec next (full_zero_target State rule),
          nvec_zero (layered_dimension system))]).
    + apply layered_test_rule_in. exact Hin.
    + constructor.
      * assert (Hchild_reach := IH next).
        assert (Hchild_bound :
            proj1_sig (Fin.to_nat next) + fuel < full_zero_state_count system).
        { rewrite Hnext. lia. }
        specialize (Hchild_reach Hchild_bound).
        unfold layered_nvec in Hchild_reach.
        rewrite block_n_at_zero in Hchild_reach. exact Hchild_reach.
      * constructor.
    + reflexivity.
    + unfold layered_nvec. rewrite block_n_at_zero.
      apply zero_displacement_one.
Qed.

Theorem remove_zero_tests_forward : forall d State eq_dec
    (system : FullZeroBVASS d State) state counters,
  FullZeroReach system state counters ->
  SReach (remove_zero_tests eq_dec system)
    (zero_test_root_state eq_dec system state)
    (zero_test_root_counters system counters).
Proof.
  intros d State eq_dec system state counters Hreach.
  pose proof (full_zero_reach_bounded d State eq_dec system state counters Hreach)
    as Hbounded.
  unfold zero_test_root_state, zero_test_root_counters.
  eapply full_zero_bounded_layered_reach; [exact Hbounded|].
  cbn. unfold full_zero_state_count. lia.
Qed.

(** Inversion principles for the finite lists generated by the compiler. *)
Lemma layered_initials_spec : forall d State eq_dec
    (system : FullZeroBVASS d State) config,
  List.In config (layered_initials eq_dec system) ->
  exists layer state,
    List.In state (full_zero_leaves system) /\
    config = (layered_state system eq_dec layer state,
      nvec_zero (layered_dimension system)).
Proof.
  intros d State eq_dec system config Hin.
  unfold layered_initials in Hin. apply in_flat_map in Hin.
  destruct Hin as [layer [Hlayer Hin]]. apply in_map_iff in Hin.
  destruct Hin as [state [<- Hstate]]. eauto.
Qed.

Lemma layered_unary_rules_spec : forall d State eq_dec
    (system : FullZeroBVASS d State) generated,
  List.In generated (layered_unary_rules eq_dec system) ->
  exists layer rule,
    List.In rule (full_zero_unary_rules system) /\
    generated = layered_unary_rule system eq_dec layer rule.
Proof.
  intros d State eq_dec system generated Hin.
  unfold layered_unary_rules in Hin. apply in_flat_map in Hin.
  destruct Hin as [layer [_ Hin]]. apply in_map_iff in Hin.
  destruct Hin as [rule [<- Hrule]]. eauto.
Qed.

Lemma layered_split_rules_spec : forall d State eq_dec
    (system : FullZeroBVASS d State) generated,
  List.In generated (layered_split_rules eq_dec system) ->
  exists layer rule,
    List.In rule (full_zero_split_rules system) /\
    generated = layered_split_rule system eq_dec layer rule.
Proof.
  intros d State eq_dec system generated Hin.
  unfold layered_split_rules in Hin. apply in_flat_map in Hin.
  destruct Hin as [layer [_ Hin]]. apply in_map_iff in Hin.
  destruct Hin as [rule [<- Hrule]]. eauto.
Qed.

Lemma layered_test_rules_spec : forall d State eq_dec
    (system : FullZeroBVASS d State) generated,
  List.In generated (layered_test_rules eq_dec system) ->
  exists layer rule,
    List.In rule (full_zero_test_rules system) /\
    generated = layered_test_rule system eq_dec layer rule.
Proof.
  intros d State eq_dec system generated Hin.
  unfold layered_test_rules in Hin. apply in_flat_map in Hin.
  destruct Hin as [layer [_ Hin]]. apply in_map_iff in Hin.
  destruct Hin as [rule [<- Hrule]]. eauto.
Qed.

Lemma remove_zero_tests_rule_spec : forall d State eq_dec
    (system : FullZeroBVASS d State) generated,
  List.In generated (stateful_rules (remove_zero_tests eq_dec system)) ->
  (exists layer rule,
      List.In rule (full_zero_unary_rules system) /\
      generated = layered_unary_rule system eq_dec layer rule) \/
  (exists layer rule,
      List.In rule (full_zero_split_rules system) /\
      generated = layered_split_rule system eq_dec layer rule) \/
  (exists layer rule,
      List.In rule (full_zero_test_rules system) /\
      generated = layered_test_rule system eq_dec layer rule).
Proof.
  intros d State eq_dec system generated Hin.
  change (List.In generated
    (layered_unary_rules eq_dec system ++ layered_split_rules eq_dec system ++
      layered_test_rules eq_dec system)) in Hin.
  apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - left. now apply layered_unary_rules_spec.
  - apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + right; left. now apply layered_split_rules_spec.
    + right; right. now apply layered_test_rules_spec.
Qed.

Definition block_project_z {width count} (block : Fin.t count)
    (value : ZVec (count * width)) : ZVec width :=
  vector_of_function width (fun coordinate =>
    Vector.nth value (block_coordinate block coordinate)).

Lemma block_project_z_block : forall width count (block : Fin.t count)
    (value : ZVec width),
  block_project_z block
    (block_z_at count (proj1_sig (Fin.to_nat block)) value) = value.
Proof.
  intros width count block value.
  apply (proj1 (Vector.eq_nth_iff Z width _ _)).
  intros coordinate coordinate' Heq; subst coordinate'.
  unfold block_project_z. rewrite nth_vector_of_function.
  unfold block_z_at. rewrite nth_vector_of_function.
  unfold block_coordinate. rewrite Fin.to_nat_of_nat. cbn [proj1_sig].
  set (block_index := proj1_sig (Fin.to_nat block)).
  set (coordinate_index := proj1_sig (Fin.to_nat coordinate)).
  assert (Hlower : (block_index * width <=?
      block_index * width + coordinate_index)%nat = true).
  { apply Nat.leb_le. lia. }
  assert (Hupper : (block_index * width + coordinate_index <?
      S block_index * width)%nat = true).
  { apply Nat.ltb_lt. rewrite Nat.mul_succ_l.
    apply Nat.add_lt_mono_l. unfold coordinate_index.
    exact (proj2_sig (Fin.to_nat coordinate)). }
  rewrite Hlower, Hupper. cbn.
  replace (block_index * width + coordinate_index - block_index * width)%nat
    with coordinate_index by lia.
  symmetry. unfold coordinate_index.
  rewrite <- (to_list_nth_order Z width value
    (proj1_sig (Fin.to_nat coordinate))
    (proj2_sig (Fin.to_nat coordinate)) 0%Z).
  unfold Vector.nth_order. f_equal. apply Fin.to_nat_inj.
  rewrite Fin.to_nat_of_nat. reflexivity.
Qed.

Lemma block_z_at_injective : forall width count (block : Fin.t count)
    (left right : ZVec width),
  block_z_at count (proj1_sig (Fin.to_nat block)) left =
  block_z_at count (proj1_sig (Fin.to_nat block)) right ->
  left = right.
Proof.
  intros width count block left right Heq.
  pose proof (f_equal (block_project_z block) Heq) as H.
  now rewrite !block_project_z_block in H.
Qed.

Lemma zvec_opp_involutive : forall d (value : ZVec d),
  zvec_opp (zvec_opp value) = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'. unfold zvec_opp.
  repeat rewrite (nth_map Z.opp _ index index eq_refl). lia.
Qed.

Lemma block_n_at_project_of_outside_zero : forall width count
    (block : Fin.t count) (value : NVec (count * width)),
  (forall position,
    (Nat.leb (proj1_sig (Fin.to_nat block) * width)
       (proj1_sig (Fin.to_nat position)) &&
     Nat.ltb (proj1_sig (Fin.to_nat position))
       (S (proj1_sig (Fin.to_nat block)) * width))%bool = false ->
    Vector.nth value position = 0) ->
  block_n_at count (proj1_sig (Fin.to_nat block))
    (block_project_n block value) = value.
Proof.
  intros width count block value Houtside.
  apply (proj1 (Vector.eq_nth_iff nat (count * width) _ _)).
  intros position position' Heq; subst position'.
  unfold block_n_at. rewrite nth_vector_of_function.
  remember (Nat.leb (proj1_sig (Fin.to_nat block) * width)
      (proj1_sig (Fin.to_nat position)) &&
    Nat.ltb (proj1_sig (Fin.to_nat position))
      (S (proj1_sig (Fin.to_nat block)) * width))%bool as inside eqn:Hinside.
  destruct inside.
  - symmetry in Hinside. apply andb_true_iff in Hinside as [Hlower Hupper].
    apply Nat.leb_le in Hlower. apply Nat.ltb_lt in Hupper.
    assert (Hoffset : proj1_sig (Fin.to_nat position) -
        proj1_sig (Fin.to_nat block) * width < width) by nia.
    rewrite <- (to_list_nth_order nat width (block_project_n block value)
      _ Hoffset 0%nat). unfold Vector.nth_order, block_project_n.
    rewrite nth_vector_of_function. f_equal. apply Fin.to_nat_inj.
    unfold block_coordinate. repeat rewrite Fin.to_nat_of_nat.
    cbn [proj1_sig]. lia.
  - symmetry. apply Houtside. symmetry. exact Hinside.
Qed.

Lemma layered_unary_apply_reverse : forall d State
    (system : FullZeroBVASS d State)
    (layer : Fin.t (full_zero_state_count system)) rule source target,
  add_displacement
    (layered_zvec system (proj1_sig (Fin.to_nat layer))
      (zvec_opp (unary_zero_delta d State rule)))
    [layered_nvec system (proj1_sig (Fin.to_nat layer)) target] =
    Some (layered_nvec system (proj1_sig (Fin.to_nat layer)) source) ->
  add_displacement (unary_zero_delta d State rule) [source] = Some target.
Proof.
  intros d State system layer rule source target Happly.
  apply displacement_singleton_step_action in Happly.
  unfold layered_zvec, layered_nvec in Happly.
  change (block_z_at (full_zero_state_count system)
      (proj1_sig (Fin.to_nat layer))
      (zvec_opp (unary_zero_delta d State rule)) =
    StepAction
      (block_n_at (full_zero_state_count system)
        (proj1_sig (Fin.to_nat layer)) target)
      (block_n_at (full_zero_state_count system)
        (proj1_sig (Fin.to_nat layer)) source)) in Happly.
  rewrite <- (block_z_at_step_action d (full_zero_state_count system)
    (proj1_sig (Fin.to_nat layer)) target source) in Happly.
  apply (block_z_at_injective d (full_zero_state_count system) layer) in Happly.
  assert (Hdelta : unary_zero_delta d State rule = StepAction source target).
  { pose proof (f_equal (@zvec_opp d) Happly) as Hopp.
    now rewrite zvec_opp_involutive, zvec_opp_step_action in Hopp. }
  apply add_displacement_of_exact_reduction.
  rewrite nvec_sum_singleton_reduction.
  rewrite Hdelta. unfold StepAction, zvec_sub_run, zvec_add, nvec_to_zvec.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
  repeat rewrite (nth_map _ _ index index eq_refl). lia.
Qed.

Lemma layered_unary_preimage : forall d State
    (system : FullZeroBVASS d State)
    (layer : Fin.t (full_zero_state_count system)) rule source child,
  add_displacement
    (layered_zvec system (proj1_sig (Fin.to_nat layer))
      (zvec_opp (unary_zero_delta d State rule))) [child] =
    Some (layered_nvec system (proj1_sig (Fin.to_nat layer)) source) ->
  exists target,
    child = layered_nvec system (proj1_sig (Fin.to_nat layer)) target /\
    add_displacement (unary_zero_delta d State rule) [source] = Some target.
Proof.
  intros d State system layer rule source child Happly.
  set (target := block_project_n layer child).
  assert (Hshape : child = layered_nvec system
      (proj1_sig (Fin.to_nat layer)) target).
  { symmetry. unfold layered_nvec, target.
    apply block_n_at_project_of_outside_zero. intros position Houtside.
    pose proof (add_displacement_exact_reduction _ _ _ _ Happly) as Hexact.
    rewrite nvec_sum_singleton_reduction in Hexact.
    pose proof (f_equal (fun value => Vector.nth value position) Hexact) as Hnth.
    unfold zvec_add, nvec_to_zvec in Hnth.
    rewrite (nth_map2 Z.add _ _ position position position eq_refl eq_refl),
      (nth_map Z.of_nat _ position position eq_refl),
      (nth_map Z.of_nat _ position position eq_refl) in Hnth.
    unfold layered_zvec, layered_nvec, block_z_at, block_n_at in Hnth.
    rewrite nth_vector_of_function, nth_vector_of_function in Hnth.
    rewrite Houtside in Hnth. cbn in Hnth.
    apply Nat2Z.inj. cbn. lia. }
  exists target. split; [exact Hshape|].
  rewrite Hshape in Happly. now apply layered_unary_apply_reverse in Happly.
Qed.

Lemma nvec_add_block_preimages : forall width count (block : Fin.t count)
    (left right : NVec (count * width)) (result : NVec width),
  nvec_add left right =
    block_n_at count (proj1_sig (Fin.to_nat block)) result ->
  exists left_value right_value,
    left = block_n_at count (proj1_sig (Fin.to_nat block)) left_value /\
    right = block_n_at count (proj1_sig (Fin.to_nat block)) right_value /\
    result = nvec_add left_value right_value.
Proof.
  intros width count block left right result Hsum.
  set (left_value := block_project_n block left).
  set (right_value := block_project_n block right).
  assert (Hleft : left = block_n_at count
      (proj1_sig (Fin.to_nat block)) left_value).
  { symmetry. unfold left_value. apply block_n_at_project_of_outside_zero.
    intros position Houtside.
    pose proof (f_equal (fun value => Vector.nth value position) Hsum) as Hnth.
    unfold nvec_add, block_n_at in Hnth.
    rewrite (nth_map2 Nat.add _ _ position position position eq_refl eq_refl),
      nth_vector_of_function, Houtside in Hnth. cbn in Hnth. lia. }
  assert (Hright : right = block_n_at count
      (proj1_sig (Fin.to_nat block)) right_value).
  { symmetry. unfold right_value. apply block_n_at_project_of_outside_zero.
    intros position Houtside.
    pose proof (f_equal (fun value => Vector.nth value position) Hsum) as Hnth.
    unfold nvec_add, block_n_at in Hnth.
    rewrite (nth_map2 Nat.add _ _ position position position eq_refl eq_refl),
      nth_vector_of_function, Houtside in Hnth. cbn in Hnth. lia. }
  exists left_value, right_value. repeat split; try assumption.
  rewrite Hleft, Hright, <- block_n_at_add in Hsum.
  symmetry. eapply block_n_at_injective; exact Hsum.
Qed.

Lemma block_project_n_add : forall width count (block : Fin.t count)
    (left right : NVec (count * width)),
  block_project_n block (nvec_add left right) =
    nvec_add (block_project_n block left) (block_project_n block right).
Proof.
  intros. apply (proj1 (Vector.eq_nth_iff nat width _ _)).
  intros coordinate coordinate' Heq; subst coordinate'.
  unfold block_project_n, nvec_add. repeat rewrite nth_vector_of_function.
  repeat rewrite (nth_map2 Nat.add _ _ _ _ _ eq_refl eq_refl).
  repeat rewrite nth_vector_of_function. reflexivity.
Qed.

Lemma block_interval_other_false : forall width count
    (active other : Fin.t count) (coordinate : Fin.t width),
  active <> other ->
  (Nat.leb (proj1_sig (Fin.to_nat active) * width)
      (proj1_sig (Fin.to_nat other) * width +
       proj1_sig (Fin.to_nat coordinate)) &&
   Nat.ltb (proj1_sig (Fin.to_nat other) * width +
       proj1_sig (Fin.to_nat coordinate))
      (S (proj1_sig (Fin.to_nat active)) * width))%bool = false.
Proof.
  intros width count active other coordinate Hneq.
  destruct (Nat.lt_trichotomy (proj1_sig (Fin.to_nat active))
      (proj1_sig (Fin.to_nat other))) as [Hlt|[Heq|Hgt]].
  - apply andb_false_iff. right. apply Nat.ltb_ge.
    assert (Hsucc : S (proj1_sig (Fin.to_nat active)) <=
        proj1_sig (Fin.to_nat other)) by lia.
    pose proof (Nat.mul_le_mono_r _ _ width Hsucc) as Hblocks.
    rewrite Nat.mul_succ_l in Hblocks. lia.
  - exfalso. apply Hneq. apply Fin.to_nat_inj. exact Heq.
  - apply andb_false_iff. left. apply Nat.leb_gt.
    assert (Hsucc : S (proj1_sig (Fin.to_nat other)) <=
        proj1_sig (Fin.to_nat active)) by lia.
    pose proof (Nat.mul_le_mono_r _ _ width Hsucc) as Hblocks.
    rewrite Nat.mul_succ_l in Hblocks.
    pose proof (proj2_sig (Fin.to_nat coordinate)) as Hcoordinate.
    eapply Nat.lt_le_trans.
    + apply Nat.add_lt_mono_l. exact Hcoordinate.
    + exact Hblocks.
Qed.

Lemma block_project_n_other_zero : forall width count
    (active other : Fin.t count) (value : NVec width),
  active <> other ->
  block_project_n other
    (block_n_at count (proj1_sig (Fin.to_nat active)) value) = nvec_zero width.
Proof.
  intros width count active other value Hneq.
  apply (proj1 (Vector.eq_nth_iff nat width _ _)).
  intros coordinate coordinate' Heq; subst coordinate'.
  unfold block_project_n, block_n_at, nvec_zero.
  rewrite nth_vector_of_function, nth_vector_of_function, const_nth.
  unfold block_coordinate. rewrite Fin.to_nat_of_nat. cbn [proj1_sig].
  rewrite block_interval_other_false; [reflexivity|exact Hneq].
Qed.

Lemma block_action_preserves_other_projection : forall width count
    (active other : Fin.t count) (delta : ZVec width)
    (child result : NVec (count * width)),
  active <> other ->
  add_displacement
    (block_z_at count (proj1_sig (Fin.to_nat active)) delta) [child] =
    Some result ->
  block_project_n other child = block_project_n other result.
Proof.
  intros width count active other delta child result Hneq Happly.
  pose proof (add_displacement_exact_reduction _ _ _ _ Happly) as Hexact.
  rewrite nvec_sum_singleton_reduction in Hexact.
  apply (proj1 (Vector.eq_nth_iff nat width _ _)).
  intros coordinate coordinate' Heq; subst coordinate'.
  pose proof (f_equal (fun value => Vector.nth value
    (block_coordinate other coordinate)) Hexact) as Hnth.
  unfold zvec_add, nvec_to_zvec in Hnth.
  rewrite (nth_map2 Z.add _ _ _ _ _ eq_refl eq_refl),
    (nth_map Z.of_nat _ _ _ eq_refl),
    (nth_map Z.of_nat _ _ _ eq_refl) in Hnth.
  unfold block_z_at in Hnth. rewrite nth_vector_of_function in Hnth.
  unfold block_coordinate in Hnth. rewrite Fin.to_nat_of_nat in Hnth.
  cbn [proj1_sig] in Hnth.
  assert (Houtside :
    (Nat.leb (proj1_sig (Fin.to_nat active) * width)
       (proj1_sig (Fin.to_nat other) * width +
        proj1_sig (Fin.to_nat coordinate)) &&
     Nat.ltb (proj1_sig (Fin.to_nat other) * width +
        proj1_sig (Fin.to_nat coordinate))
       (S (proj1_sig (Fin.to_nat active)) * width))%bool = false).
  { apply block_interval_other_false. exact Hneq. }
  rewrite Houtside in Hnth. cbn in Hnth.
  unfold block_project_n. repeat rewrite nth_vector_of_function.
  apply Nat2Z.inj. cbn. exact Hnth.
Qed.

Lemma layered_split_preimages : forall d State
    (system : FullZeroBVASS d State)
    (layer : Fin.t (full_zero_state_count system)) source left right,
  add_displacement (zvec_zero (layered_dimension system)) [left; right] =
    Some (layered_nvec system (proj1_sig (Fin.to_nat layer)) source) ->
  exists left_value right_value,
    left = layered_nvec system (proj1_sig (Fin.to_nat layer)) left_value /\
    right = layered_nvec system (proj1_sig (Fin.to_nat layer)) right_value /\
    source = nvec_add left_value right_value.
Proof.
  intros d State system layer source left right Happly.
  pose proof (add_displacement_exact_reduction _ _ _ _ Happly) as Hexact.
  rewrite zvec_zero_add_reduction in Hexact.
  apply nvec_to_zvec_injective in Hexact.
  rewrite nvec_sum_rsum_stateful in Hexact. cbn [nvec_rsum_stateful] in Hexact.
  rewrite (nvec_add_comm_stateful _ right (nvec_zero _)),
    nvec_add_zero_left_stateful in Hexact.
  unfold layered_nvec in Hexact.
  now apply nvec_add_block_preimages in Hexact.
Qed.

Definition LayeredReachProperty {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State)
    (state : Fin.t (layered_state_count system))
    (counters : NVec (layered_dimension system)) : Prop :=
  forall layer original value,
    List.In original (full_zero_states system) ->
    state = layered_state system eq_dec layer original ->
    counters = layered_nvec system (proj1_sig (Fin.to_nat layer)) value ->
    FullZeroReach system original value.

Definition LayeredChildrenProperty {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State)
    (configs : list (SConfig (layered_dimension system)
      (layered_state_count system))) : Prop :=
  List.Forall (fun config =>
    LayeredReachProperty eq_dec system (fst config) (snd config)) configs.

Definition LayeredLowerZero {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State)
    (state : Fin.t (layered_state_count system))
    (counters : NVec (layered_dimension system)) : Prop :=
  forall layer original lower,
    List.In original (full_zero_states system) ->
    state = layered_state system eq_dec layer original ->
    proj1_sig (Fin.to_nat lower) < proj1_sig (Fin.to_nat layer) ->
    block_project_n lower counters = nvec_zero d.

Definition LayeredChildrenLowerZero {d State}
    (eq_dec : forall x y : State, {x = y} + {x <> y})
    (system : FullZeroBVASS d State)
    (configs : list (SConfig (layered_dimension system)
      (layered_state_count system))) : Prop :=
  List.Forall (fun config =>
    LayeredLowerZero eq_dec system (fst config) (snd config)) configs.

Lemma zero_displacement_singleton_eq : forall d (child result : NVec d),
  add_displacement (zvec_zero d) [child] = Some result -> child = result.
Proof.
  intros d child result H.
  pose proof (add_displacement_exact_reduction _ _ _ _ H) as Hexact.
  rewrite zvec_zero_add_reduction, nvec_sum_singleton_reduction in Hexact.
  now apply nvec_to_zvec_injective in Hexact.
Qed.

Lemma zero_displacement_pair_eq : forall d (left right result : NVec d),
  add_displacement (zvec_zero d) [left; right] = Some result ->
  nvec_add left right = result.
Proof.
  intros d left right result H.
  pose proof (add_displacement_exact_reduction _ _ _ _ H) as Hexact.
  rewrite zvec_zero_add_reduction in Hexact.
  apply nvec_to_zvec_injective in Hexact.
  rewrite nvec_sum_rsum_stateful in Hexact. cbn [nvec_rsum_stateful] in Hexact.
  rewrite (nvec_add_comm_stateful _ right (nvec_zero _)),
    nvec_add_zero_left_stateful in Hexact. exact Hexact.
Qed.

Lemma sreach_children_singleton_inv : forall d q (S : SBVAS d q) config,
  SReachChildren S [config] -> SReach S (fst config) (snd config).
Proof.
  intros d q S [state counters] H. cbn. inversion H; subst. assumption.
Qed.

Lemma layered_test_rule_shape : forall d State eq_dec
    (system : FullZeroBVASS d State)
    (small : Fin.t (length (full_zero_states system))) rule,
  exists current next,
    output_state (layered_test_rule system eq_dec small rule) =
      layered_state system eq_dec current (full_zero_source State rule) /\
    input_states (layered_test_rule system eq_dec small rule) =
      [layered_state system eq_dec next (full_zero_target State rule)] /\
    proj1_sig (Fin.to_nat current) = proj1_sig (Fin.to_nat small) /\
    proj1_sig (Fin.to_nat next) = S (proj1_sig (Fin.to_nat small)).
Proof.
  intros d State eq_dec system small rule.
  assert (Hcurrent : proj1_sig (Fin.to_nat small) <
      full_zero_state_count system).
  { unfold full_zero_state_count. apply Nat.lt_lt_succ_r.
    exact (proj2_sig (Fin.to_nat small)). }
  exists (Fin.of_nat_lt Hcurrent), (Fin.FS small).
  repeat split.
  - apply Fin.to_nat_inj.
    cbv [output_state layered_test_rule layered_state].
    repeat rewrite fin_value_of_nat. reflexivity.
  - rewrite Fin.to_nat_of_nat. reflexivity.
  - change (proj1_sig (Fin.to_nat (Fin.FS small)) =
      S (proj1_sig (Fin.to_nat small))).
    rewrite fin_to_nat_FS_value. reflexivity.
Qed.

Lemma remove_zero_tests_lower_zero_mut : forall d State eq_dec
    (system : FullZeroBVASS d State),
  (forall state counters,
    SReach (remove_zero_tests eq_dec system) state counters ->
    LayeredLowerZero eq_dec system state counters) /\
  (forall configs,
    SReachChildren (remove_zero_tests eq_dec system) configs ->
    LayeredChildrenLowerZero eq_dec system configs).
Proof.
  intros d State eq_dec system. apply SReach_mutind.
  - intros state counters Hinitial layer original lower Horiginal Hstate Hlt.
    apply layered_initials_spec in Hinitial.
    destruct Hinitial as [initial_layer [leaf [Hleaf Hconfig]]].
    injection Hconfig as _ Hcounter. rewrite Hcounter.
    unfold block_project_n, nvec_zero.
    apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros coordinate coordinate' Heq; subst coordinate'.
    rewrite nth_vector_of_function, !const_nth. reflexivity.
  - intros generated child_configs result Hgenerated Hchildren IHchildren
      Hstates Happly layer original lower Horiginal Houtput Hlt.
    apply remove_zero_tests_rule_spec in Hgenerated.
    destruct Hgenerated as
      [[rule_layer [rule [Hrule ->]]]|
       [[rule_layer [rule [Hrule ->]]]|
        [small [rule [Hrule ->]]]]].
    + cbn [output_state] in Houtput.
      pose proof (layered_state_injective d State system eq_dec
        rule_layer layer (unary_zero_source d State rule) original
        (unary_zero_source_in_states d State system rule Hrule)
        Horiginal Houtput) as [Hlayer _]. subst layer.
      destruct child_configs as [|child rest].
      { apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      destruct rest as [|extra rest].
      2:{ apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      inversion IHchildren as [|? ? Hchild _]; subst.
      apply Permutation_sym, Permutation_length_1_inv in Hstates.
      inversion Hstates; subst.
      assert (Hneq : rule_layer <> lower).
      { intro Heq. subst lower. lia. }
      rewrite <- (block_action_preserves_other_projection d
        (full_zero_state_count system) rule_layer lower
        (zvec_opp (unary_zero_delta d State rule))
        (snd child) result Hneq Happly).
      apply Hchild with (layer := rule_layer)
        (original := unary_zero_target d State rule).
      * now apply unary_zero_target_in_states with (rule := rule).
      * exact H0.
      * exact Hlt.
    + cbn [output_state] in Houtput.
      destruct (split_zero_states_in d State system rule Hrule)
        as [Hsource [Hleft Hright]].
      pose proof (layered_state_injective d State system eq_dec
        rule_layer layer (split_zero_source State rule) original
        Hsource Horiginal Houtput) as [Hlayer _]. subst layer.
      destruct child_configs as [|first rest].
      { apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      destruct rest as [|second rest].
      { apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      destruct rest as [|extra rest].
      2:{ apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      inversion IHchildren as [|? ? IHfirst IHtail]; subst.
      inversion IHtail as [|? ? IHsecond _]; subst.
      apply Permutation_sym, Permutation_length_2_inv in Hstates.
      pose proof (zero_displacement_pair_eq _ (snd first) (snd second)
        result Happly) as Hsum.
      rewrite <- Hsum, block_project_n_add.
      destruct Hstates as [Horder|Horder]; inversion Horder; subst.
      * rewrite (IHfirst rule_layer (split_zero_left State rule) lower
          Hleft H0 Hlt),
          (IHsecond rule_layer (split_zero_right State rule) lower
          Hright H1 Hlt). apply nvec_add_zero_left_stateful.
      * rewrite (IHfirst rule_layer (split_zero_right State rule) lower
          Hright H0 Hlt),
          (IHsecond rule_layer (split_zero_left State rule) lower
          Hleft H1 Hlt). apply nvec_add_zero_left_stateful.
    + destruct (layered_test_rule_shape d State eq_dec system small rule)
        as [current [next [Houtshape [Hinshape [Hcurrent Hnext]]]]].
      rewrite Houtshape in Houtput.
      pose proof (layered_state_injective d State system eq_dec
        current layer (full_zero_source State rule) original
        (test_rule_source_in_states d State system rule Hrule)
        Horiginal Houtput) as [Hlayer _]. subst layer.
      destruct child_configs as [|child rest].
      { rewrite Hinshape in Hstates. apply Permutation_length in Hstates.
        cbn in Hstates. discriminate. }
      destruct rest as [|extra rest].
      2:{ rewrite Hinshape in Hstates. apply Permutation_length in Hstates.
          cbn in Hstates. discriminate. }
      inversion IHchildren as [|? ? Hchild _]; subst.
      rewrite Hinshape in Hstates.
      apply Permutation_sym, Permutation_length_1_inv in Hstates.
      inversion Hstates; subst.
      pose proof (zero_displacement_singleton_eq _ (snd child) result Happly)
        as Heq. rewrite <- Heq.
      apply Hchild with (layer := next)
        (original := full_zero_target State rule).
      * now apply test_zero_target_in_states with (rule := rule).
      * exact H0.
      * lia.
  - constructor.
  - intros state counters configs Hhead IHhead Htail IHtail.
    constructor; assumption.
Qed.

Lemma remove_zero_tests_backward_mut : forall d State eq_dec
    (system : FullZeroBVASS d State),
  (forall state counters,
    SReach (remove_zero_tests eq_dec system) state counters ->
    LayeredReachProperty eq_dec system state counters) /\
  (forall configs,
    SReachChildren (remove_zero_tests eq_dec system) configs ->
    LayeredChildrenProperty eq_dec system configs).
Proof.
  intros d State eq_dec system. apply SReach_mutind.
  - intros state counters Hinitial layer original value Horiginal Hstate Hcounters.
    apply layered_initials_spec in Hinitial.
    destruct Hinitial as [initial_layer [leaf [Hleaf Hconfig]]].
    injection Hconfig as Hstate0 Hcounters0.
    rewrite Hstate0 in Hstate. rewrite Hcounters0 in Hcounters.
    pose proof (layered_state_injective d State system eq_dec
      initial_layer layer leaf original
      (full_zero_leaf_in_states d State system leaf Hleaf) Horiginal Hstate)
      as [Hlayers Hstates]. subst original layer.
    assert (Hvalue : value = nvec_zero d).
    { apply (block_n_at_injective d (full_zero_state_count system)
        initial_layer). rewrite block_n_at_zero. symmetry. exact Hcounters. }
    subst value. constructor. exact Hleaf.
  - intros generated child_configs result Hgenerated Hchildren IHchildren
      Hstates Happly layer original value Horiginal Houtput Hresult.
    apply remove_zero_tests_rule_spec in Hgenerated.
    destruct Hgenerated as
      [[rule_layer [rule [Hrule ->]]]|
       [[rule_layer [rule [Hrule ->]]]|
        [small [rule [Hrule ->]]]]].
    + cbn [output_state] in Houtput.
      pose proof (layered_state_injective d State system eq_dec
        rule_layer layer (unary_zero_source d State rule) original
        (unary_zero_source_in_states d State system rule Hrule)
        Horiginal Houtput) as [Hlayer Hsource]. subst layer original.
      destruct child_configs as [|child rest].
      { apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      destruct rest as [|extra rest].
      2:{ apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      inversion IHchildren as [|? ? Hchild _]; subst.
      assert (Hchild_state : fst child = layered_state system eq_dec rule_layer
          (unary_zero_target d State rule)).
      { apply Permutation_sym, Permutation_length_1_inv in Hstates.
        now inversion Hstates. }
      destruct (layered_unary_preimage d State system rule_layer rule value
        (snd child) Happly) as [target [Htarget Hadd]].
      eapply full_zero_reach_unary with (target_counters := target).
      * exact Hrule.
      * exact Hadd.
      * apply Hchild with (layer := rule_layer).
        -- now apply unary_zero_target_in_states with (rule := rule).
        -- exact Hchild_state.
        -- exact Htarget.
    + cbn [output_state] in Houtput.
      destruct (split_zero_states_in d State system rule Hrule)
        as [Hsplit_source [Hsplit_left Hsplit_right]].
      pose proof (layered_state_injective d State system eq_dec
        rule_layer layer (split_zero_source State rule) original
        Hsplit_source
        Horiginal Houtput) as [Hlayer Hsource]. subst layer original.
      destruct child_configs as [|first rest].
      { apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      destruct rest as [|second rest].
      { apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      destruct rest as [|extra rest].
      2:{ apply Permutation_length in Hstates. cbn in Hstates. discriminate. }
      inversion IHchildren as [|? ? Hfirst Htail]; subst.
      inversion Htail as [|? ? Hsecond _]; subst.
      destruct (layered_split_preimages d State system rule_layer value
        (snd first) (snd second) Happly)
        as [first_value [second_value [Hfirst_value [Hsecond_value Hsum]]]].
      apply Permutation_sym, Permutation_length_2_inv in Hstates.
      destruct Hstates as [Horder|Horder]; inversion Horder; subst.
      * eapply full_zero_reach_split with (left_counters := first_value)
          (right_counters := second_value).
        -- exact Hrule.
        -- reflexivity.
        -- apply Hfirst with (layer := rule_layer);
             [exact Hsplit_left|exact H0|exact Hfirst_value].
        -- apply Hsecond with (layer := rule_layer);
             [exact Hsplit_right|exact H1|exact Hsecond_value].
      * eapply full_zero_reach_split with (left_counters := second_value)
          (right_counters := first_value).
        -- exact Hrule.
        -- apply nvec_add_comm_stateful.
        -- apply Hsecond with (layer := rule_layer);
             [exact Hsplit_left|exact H1|exact Hsecond_value].
        -- apply Hfirst with (layer := rule_layer);
             [exact Hsplit_right|exact H0|exact Hfirst_value].
    + destruct (layered_test_rule_shape d State eq_dec system small rule)
        as [current [next [Houtshape [Hinshape [Hcurrent Hnext]]]]].
      rewrite Houtshape in Houtput.
      pose proof (layered_state_injective d State system eq_dec
        current layer (full_zero_source State rule) original
        (test_rule_source_in_states d State system rule Hrule)
        Horiginal Houtput) as [Hlayer Hsource]. subst layer original.
      destruct child_configs as [|child rest].
      { rewrite Hinshape in Hstates. apply Permutation_length in Hstates.
        cbn in Hstates. discriminate. }
      destruct rest as [|extra rest].
      2:{ rewrite Hinshape in Hstates. apply Permutation_length in Hstates.
          cbn in Hstates. discriminate. }
      change (List.Forall (fun config => LayeredReachProperty eq_dec system
        (fst config) (snd config)) [child]) in IHchildren.
      inversion IHchildren as [|? ? Hchild _].
      pose proof (sreach_children_singleton_inv _ _ _ child Hchildren)
        as Hchild_reach'.
      rewrite Hinshape in Hstates.
      apply Permutation_sym, Permutation_length_1_inv in Hstates.
      injection Hstates as Hchild_state.
      pose proof (zero_displacement_singleton_eq _ (snd child) result Happly)
        as Hchild_result.
      pose proof ((proj1 (remove_zero_tests_lower_zero_mut
        d State eq_dec system)) _ _ Hchild_reach') as Hlower_child.
      assert (Hcurrent_lt_next : proj1_sig (Fin.to_nat current) <
          proj1_sig (Fin.to_nat next)) by lia.
      specialize (Hlower_child next (full_zero_target State rule) current
        (test_zero_target_in_states d State system rule Hrule)
        Hchild_state Hcurrent_lt_next).
      assert (Hvalue : value = nvec_zero d).
      { rewrite Hchild_result, Hresult in Hlower_child.
        unfold layered_nvec in Hlower_child.
        rewrite block_project_n_block in Hlower_child. exact Hlower_child. }
      subst value. eapply full_zero_reach_test; [exact Hrule|].
      apply Hchild with (layer := next).
      * now apply test_zero_target_in_states with (rule := rule).
      * exact Hchild_state.
      * rewrite Hchild_result, Hresult. unfold layered_nvec.
        rewrite !block_n_at_zero. reflexivity.
  - constructor.
  - intros state counters configs Hhead IHhead Htail IHtail.
    constructor; assumption.
Qed.

Lemma full_zero_reach_state_in_states : forall d State
    (system : FullZeroBVASS d State) state counters,
  FullZeroReach system state counters ->
  List.In state (full_zero_states system).
Proof.
  intros d State system state counters Hreach. induction Hreach.
  - now apply full_zero_leaf_in_states.
  - now apply unary_zero_source_in_states with (rule := rule).
  - now destruct (split_zero_states_in d State system rule H) as [? _].
  - now apply test_rule_source_in_states with (rule := rule).
Qed.

Theorem remove_zero_tests_backward : forall d State eq_dec
    (system : FullZeroBVASS d State) state counters,
  List.In state (full_zero_states system) ->
  SReach (remove_zero_tests eq_dec system)
    (zero_test_root_state eq_dec system state)
    (zero_test_root_counters system counters) ->
  FullZeroReach system state counters.
Proof.
  intros d State eq_dec system state counters Hstate Hreach.
  pose proof ((proj1 (remove_zero_tests_backward_mut
    d State eq_dec system)) _ _ Hreach) as Hmeaning.
  apply Hmeaning with (layer := @Fin.F1 (length (full_zero_states system))).
  - exact Hstate.
  - reflexivity.
  - reflexivity.
Qed.

Theorem remove_zero_tests_correct : forall d State eq_dec
    (system : FullZeroBVASS d State) state counters,
  List.In state (full_zero_states system) ->
  FullZeroReach system state counters <->
  SReach (remove_zero_tests eq_dec system)
    (zero_test_root_state eq_dec system state)
    (zero_test_root_counters system counters).
Proof.
  intros d State eq_dec system state counters Hstate. split.
  - apply remove_zero_tests_forward.
  - now apply remove_zero_tests_backward.
Qed.
