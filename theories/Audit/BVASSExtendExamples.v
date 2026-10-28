From Mell.BVASS Require Import Stateful Extend.
From Mell.Core Require Import Vector.

From Coq Require Import List Vector ZArith Sorting.Permutation.

Import ListNotations.

Definition extend_state0 : Fin.t 1 := Fin.F1.
Definition extend_nvec1 (value : nat) : NVec 1 := Vector.of_list [value].
Definition extend_zvec1 (value : Z) : ZVec 1 := Vector.of_list [value].

Definition extend_unary_rule (delta : Z) : SRule 1 1 :=
  {| input_states := [extend_state0];
     input_nonempty := fun H => List.nil_cons (eq_sym H);
     output_state := extend_state0;
     rule_delta := extend_zvec1 delta |}.

Definition extend_base : SBVAS 1 1 :=
  {| initial_configs := [(extend_state0, extend_nvec1 0)];
     stateful_rules := [extend_unary_rule 1] |}.

Definition extend_available : list (SConfig 1 1) :=
  [(extend_state0, extend_nvec1 2); (extend_state0, extend_nvec1 2)].

Example extend_all_keep_is_enumerated :
    List.In ([extend_state0], [])
      (enumerate_omissions extend_available [extend_state0]).
Proof. vm_compute. auto. Qed.

Example extend_duplicate_available_keeps_occurrences :
    length (enumerate_omissions extend_available [extend_state0]) = 3.
Proof. reflexivity. Qed.

Example extend_three_equal_children_have_eight_positional_choices :
    length (enumerate_omissions
      [(extend_state0, extend_nvec1 0)]
      [extend_state0; extend_state0; extend_state0]) = 8.
Proof. reflexivity. Qed.

Example extend_partial_omission_preserves_one_occurrence :
    OmissionSelection [(extend_state0, extend_nvec1 2)]
      [extend_state0; extend_state0]
      [extend_state0] [(extend_state0, extend_nvec1 2)].
Proof. constructor. constructor; [cbn; auto|constructor]. Qed.

Example extend_all_omission_positive_initial :
    make_extended_initial (extend_unary_rule 1) []
      [(extend_state0, extend_nvec1 2)] =
    Some (extend_state0, extend_nvec1 3).
Proof. reflexivity. Qed.

Example extend_all_omission_negative_rejected :
    make_extended_initial (extend_unary_rule (-3)) []
      [(extend_state0, extend_nvec1 2)] = None.
Proof. reflexivity. Qed.

Example extend_no_omission_preserves_rule :
    List.In (extend_unary_rule 1)
      (stateful_rules (extend_bvass extend_base extend_available)).
Proof. apply original_rule_in_extension. cbn. auto. Qed.

Example extend_empty_available_reach_iff : forall state counters,
    SReach (extend_bvass extend_base []) state counters <->
    SReach extend_base state counters.
Proof.
  intros. apply extend_bvass_reach_iff.
  intros config H. contradiction.
Qed.

Definition extend_state0_d0 : Fin.t 1 := Fin.F1.
Definition extend_rule_d0 : SRule 0 1 :=
  {| input_states := [extend_state0_d0];
     input_nonempty := fun H => List.nil_cons (eq_sym H);
     output_state := extend_state0_d0;
     rule_delta := Vector.nil Z |}.

Example extend_dimension_zero_total_omission :
    make_extended_initial extend_rule_d0 []
      [(extend_state0_d0, Vector.nil nat)] =
    Some (extend_state0_d0, Vector.nil nat).
Proof. reflexivity. Qed.

Definition extend_q0_system : SBVAS 0 0 :=
  {| initial_configs := []; stateful_rules := [] |}.

Example extend_state_count_zero_vacuous : forall state : Fin.t 0,
    forall counters,
      SReach (extend_bvass extend_q0_system []) state counters <->
      SReach extend_q0_system state counters.
Proof.
  intros state. inversion state.
Qed.

Definition extend_unreachable_base : SBVAS 1 1 :=
  {| initial_configs := []; stateful_rules := [extend_unary_rule 1] |}.

Example extend_unreachable_f_adds_initial :
    SReach
      (extend_bvass extend_unreachable_base
        [(extend_state0, extend_nvec1 0)])
      extend_state0 (extend_nvec1 1).
Proof.
  constructor. apply extend_initial_membership_spec. right.
  exists (extend_unary_rule 1). split; [cbn; auto|].
  exists [], [(extend_state0, extend_nvec1 0)]. split.
  - constructor; [cbn; auto|constructor].
  - reflexivity.
Qed.

Example extend_unreachable_f_fails_reachability_hypothesis :
    ~ ReachableConfigurations extend_unreachable_base
      [(extend_state0, extend_nvec1 0)].
Proof.
  intro Hreachable.
  specialize (Hreachable (extend_state0, extend_nvec1 0) (or_introl eq_refl)).
  assert (Hnone :
      (forall state counters, SReach extend_unreachable_base state counters -> False) /\
      (forall configs, SReachChildren extend_unreachable_base configs -> configs = [])).
  { apply SReach_mutind.
    - intros state counters Hinitial. cbn in Hinitial. contradiction.
    - intros rule child_configs result Hrule Hchildren IHchildren Hstates Happly.
      destruct Hrule as [Heq|Hfalse]; [subst rule|contradiction].
      subst child_configs. apply Permutation_length in Hstates. cbn in Hstates.
      discriminate.
    - reflexivity.
    - intros state counters configs Hhead IHhead Htail IHtail. contradiction. }
  exact ((proj1 Hnone) _ _ Hreachable).
Qed.

Example extend_local_shortening_total_omission :
    exists shortened,
      ValidSRun (extend_bvass extend_base
        [(extend_state0, extend_nvec1 2)]) shortened /\
      root_config shortened = (extend_state0, extend_nvec1 3).
Proof.
  destruct (extend_local_root_shortening 1 1 extend_base
    [(extend_state0, extend_nvec1 2)] (extend_unary_rule 1)
    [] [(extend_state0, extend_nvec1 2)] sruns_nil (extend_nvec1 3))
    as [shortened [Hvalid [Hroot _]]].
  - cbn. auto.
  - constructor; [cbn; auto|constructor].
  - constructor.
  - constructor.
  - reflexivity.
  - eauto.
Qed.

Check OmissionSelection.
Check enumerate_omissions.
Check extend_bvass.
Check extend_original_reach.
Check extend_bvass_reach_iff.
Check extend_local_root_shortening.
Check basis_root_configs_reachable.

Check extend_rule_membership_spec.
Check extend_initial_membership_spec.
Check omission_selection_length.

Print Assumptions extend_bvass_reach_iff.
Print Assumptions extend_local_root_shortening.
