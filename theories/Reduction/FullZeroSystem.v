From Coq Require Import List.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System.

Import ListNotations.

Record UnaryZeroRule (d : nat) (State : Type) : Type := {
  unary_zero_source : State;
  unary_zero_delta : ZVec d;
  unary_zero_target : State
}.

Record SplitZeroRule (State : Type) : Type := {
  split_zero_source : State;
  split_zero_left : State;
  split_zero_right : State
}.

Record FullZeroRule (State : Type) : Type := {
  full_zero_source : State;
  full_zero_target : State
}.

Record FullZeroBVASS (d : nat) (State : Type) : Type := {
  full_zero_leaves : list State;
  full_zero_unary_rules : list (UnaryZeroRule d State);
  full_zero_split_rules : list (SplitZeroRule State);
  full_zero_test_rules : list (FullZeroRule State)
}.

Arguments full_zero_leaves {d State} _.
Arguments full_zero_unary_rules {d State} _.
Arguments full_zero_split_rules {d State} _.
Arguments full_zero_test_rules {d State} _.

Inductive FullZeroReach {d State}
    (system : FullZeroBVASS d State) : State -> NVec d -> Prop :=
| full_zero_reach_leaf : forall state,
    List.In state (full_zero_leaves system) ->
    FullZeroReach system state (nvec_zero d)
| full_zero_reach_unary : forall rule source_counters target_counters,
    List.In rule (full_zero_unary_rules system) ->
    add_displacement (unary_zero_delta d State rule) [source_counters] =
      Some target_counters ->
    FullZeroReach system (unary_zero_target d State rule) target_counters ->
    FullZeroReach system (unary_zero_source d State rule) source_counters
| full_zero_reach_split : forall rule source_counters left_counters right_counters,
    List.In rule (full_zero_split_rules system) ->
    source_counters = nvec_add left_counters right_counters ->
    FullZeroReach system (split_zero_left State rule) left_counters ->
    FullZeroReach system (split_zero_right State rule) right_counters ->
    FullZeroReach system (split_zero_source State rule) source_counters
| full_zero_reach_test : forall rule,
    List.In rule (full_zero_test_rules system) ->
    FullZeroReach system (full_zero_target State rule) (nvec_zero d) ->
    FullZeroReach system (full_zero_source State rule) (nvec_zero d).

Definition ForkFreeFullZeroBVASS {d State}
    (_ : FullZeroBVASS d State) : Prop := True.

Theorem every_full_zero_bvass_fork_free : forall d State
    (system : FullZeroBVASS d State),
  ForkFreeFullZeroBVASS system.
Proof. exact (fun _ _ _ => I). Qed.
