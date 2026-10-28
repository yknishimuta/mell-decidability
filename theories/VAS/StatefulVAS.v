From Coq Require Import Lia List Vector ZArith Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.Order Require Import PeriodicOrder.
From Mell.Reduction Require Import StateErasure.
From Mell.VAS Require Import Runs.

Import ListNotations.

Definition SConfig (d q : nat) := (Fin.t q * NVec d)%type.

Record VASTransition (d q : nat) := {
  VASTransitionSource : Fin.t q;
  VASTransitionAction : ZVec d;
  VASTransitionTarget : Fin.t q
}.

Arguments VASTransitionSource {d q} _.
Arguments VASTransitionAction {d q} _.
Arguments VASTransitionTarget {d q} _.

Definition VAS (d q : nat) := list (VASTransition d q).

Definition stateful_encoded_dimension d q (system : VAS d q) :=
  (d + q + List.length system)%nat.

Definition encode_vas_config {d q} (system : VAS d q)
    (state : Fin.t q) (counters : NVec d) :
    NVec (stateful_encoded_dimension d q system) :=
  Vector.append (Vector.append counters (one_hot_state state))
    (nvec_zero (List.length system)).

Definition encode_vas_gate {d q} (system : VAS d q)
    (index : nat) (counters : NVec d) :
    NVec (stateful_encoded_dimension d q system) :=
  Vector.append (Vector.append counters (nvec_zero q))
    (one_hot_nat (List.length system) index).

Definition vas_start_action {d q} (system : VAS d q)
    (index : nat) (transition : VASTransition d q) :
    ZVec (stateful_encoded_dimension d q system) :=
  Vector.append
    (Vector.append (VASTransitionAction transition)
      (state_debit [VASTransitionSource transition]))
    (one_hot_z (List.length system) index).

Definition vas_finish_action {d q} (system : VAS d q)
    (index : nat) (transition : VASTransition d q) :
    ZVec (stateful_encoded_dimension d q system) :=
  Vector.append
    (Vector.append (zvec_zero d)
      (state_credit (VASTransitionTarget transition)))
    (gate_debit (List.length system) index).

Fixpoint encode_vas_transitions {d q} (system : VAS d q)
    (index : nat) (transitions : list (VASTransition d q)) :
    PlainVAS (stateful_encoded_dimension d q system) :=
  match transitions with
  | [] => []
  | transition :: tail =>
      vas_start_action system index transition ::
      vas_finish_action system index transition ::
      encode_vas_transitions system (S index) tail
  end.

Definition erase_vas_states {d q} (system : VAS d q) :
    PlainVAS (stateful_encoded_dimension d q system) :=
  encode_vas_transitions system 0 system.

Lemma encode_vas_config_inj : forall d q (system : VAS d q)
    left_state left_counters right_state right_counters,
    encode_vas_config system left_state left_counters =
      encode_vas_config system right_state right_counters ->
    left_state = right_state /\ left_counters = right_counters.
Proof.
  intros d q system left_state left_counters right_state right_counters Heq.
  unfold encode_vas_config in Heq.
  apply Vector.append_inj in Heq as [Hprefix _].
  apply Vector.append_inj in Hprefix as [Hcounters Hstates].
  split; [now apply one_hot_state_inj in Hstates|exact Hcounters].
Qed.

Lemma encode_vas_gate_state_distinct : forall d q (system : VAS d q)
    index gate_counters state state_counters,
    encode_vas_gate system index gate_counters <>
      encode_vas_config system state state_counters.
Proof.
  intros d q system index gate_counters state state_counters Heq.
  unfold encode_vas_gate, encode_vas_config in Heq.
  apply Vector.append_inj in Heq as [Hprefix _].
  apply Vector.append_inj in Hprefix as [_ Hstates].
  pose proof (f_equal nvec_total Hstates) as Htotal.
  rewrite nvec_total_zero, one_hot_state_total in Htotal. discriminate.
Qed.

(** The public finite-control reach relation is defined by the standard
    two-phase state/gate encoding.  In particular, a self loop still consumes
    its source-state token before it may restore the target token. *)
Definition VASReach {d q} (system : VAS d q)
    (source_state : Fin.t q) (source : NVec d)
    (target_state : Fin.t q) (target : NVec d) : Prop :=
  PlainVASReach (erase_vas_states system)
    (encode_vas_config system source_state source)
    (encode_vas_config system target_state target).

Inductive DirectVASReach {d q} (system : VAS d q) :
    Fin.t q -> NVec d -> Fin.t q -> NVec d -> Prop :=
| direct_vas_reach_refl : forall state counters,
    DirectVASReach system state counters state counters
| direct_vas_reach_step : forall transition source target final_state final,
    List.In transition system ->
    VASTransitionAction transition = StepAction source target ->
    DirectVASReach system (VASTransitionTarget transition) target
      final_state final ->
    DirectVASReach system (VASTransitionSource transition) source
      final_state final.

Lemma encode_vas_transitions_nth : forall d q (system : VAS d q)
    transitions start position transition,
    nth_error transitions position = Some transition ->
    List.In (vas_start_action system (start + position) transition)
      (encode_vas_transitions system start transitions) /\
    List.In (vas_finish_action system (start + position) transition)
      (encode_vas_transitions system start transitions).
Proof.
  intros d q system transitions. induction transitions as [|head tail IH];
    intros start position transition Hnth.
  - destruct position; discriminate.
  - destruct position as [|position]; cbn in Hnth.
    + inversion Hnth; subst. replace (start + 0)%nat with start by lia.
      cbn. auto.
    + specialize (IH (S start) position transition Hnth).
      rewrite Nat.add_succ_r. cbn. destruct IH. split; right; right; assumption.
Qed.

Lemma encode_vas_transitions_in : forall d q (system : VAS d q)
    transitions start action,
    List.In action (encode_vas_transitions system start transitions) ->
    exists position transition,
      nth_error transitions position = Some transition /\
      (action = vas_start_action system (start + position) transition \/
       action = vas_finish_action system (start + position) transition).
Proof.
  intros d q system transitions. induction transitions as [|head tail IH];
    intros start action Hin; cbn in Hin; [contradiction|].
  destruct Hin as [<-|[<-|Hin]].
  - exists 0%nat, head. cbn. split; [reflexivity|]. left.
    now rewrite Nat.add_0_r.
  - exists 0%nat, head. cbn. split; [reflexivity|]. right.
    now rewrite Nat.add_0_r.
  - destruct (IH (S start) action Hin) as [position [transition [Hnth Hkind]]].
    exists (S position), transition. split; [exact Hnth|].
    replace (start + S position)%nat with (S start + position)%nat by lia.
    exact Hkind.
Qed.

Lemma erase_vas_states_in : forall d q (system : VAS d q) action,
    List.In action (erase_vas_states system) ->
    exists position transition,
      nth_error system position = Some transition /\
      (action = vas_start_action system position transition \/
       action = vas_finish_action system position transition).
Proof.
  intros d q system action Hin.
  destruct (encode_vas_transitions_in d q system system 0 action Hin)
    as [position [transition [Hnth Hkind]]].
  exists position, transition. split; [exact Hnth|].
  now replace (0 + position)%nat with position in Hkind by lia.
Qed.

Lemma state_debit_single_cancels : forall q (state : Fin.t q),
    zvec_add (state_debit [state]) (nvec_to_zvec (one_hot_state state)) =
    zvec_zero q.
Proof.
  intros q state.
  assert (Hcount : state_count [state] = one_hot_state state).
  { rewrite state_count_cons, state_count_nil, nvec_add_zero. reflexivity. }
  rewrite <- Hcount. apply state_debit_cancels.
Qed.

(** Indexed form used by the simulation theorem. *)
Lemma vas_start_step_nth : forall d q (system : VAS d q) index transition
    source target,
    nth_error system index = Some transition ->
    VASTransitionAction transition = StepAction source target ->
    PlainVASStep (erase_vas_states system)
      (encode_vas_config system (VASTransitionSource transition) source)
      (vas_start_action system index transition)
      (encode_vas_gate system index target).
Proof.
  intros d q system index transition source target Hnth Haction. split.
  - pose proof (encode_vas_transitions_nth d q system system 0 index
      transition Hnth) as [Hstart _].
    now replace (0 + index)%nat with index in Hstart by lia.
  - apply step_equation_action. unfold encode_vas_config, encode_vas_gate,
      vas_start_action, stateful_encoded_dimension.
    repeat rewrite nvec_to_zvec_append. repeat rewrite zvec_add_append.
    rewrite Haction.
    rewrite (step_action_equation d source target),
      (zvec_add_comm q
        (nvec_to_zvec (one_hot_state (VASTransitionSource transition)))
        (state_debit [VASTransitionSource transition])),
      state_debit_single_cancels,
      one_hot_z_of_nat, !nvec_to_zvec_zero, zvec_zero_add.
    reflexivity.
Qed.

Lemma vas_finish_step_nth : forall d q (system : VAS d q) index transition
    counters,
    nth_error system index = Some transition ->
    PlainVASStep (erase_vas_states system)
      (encode_vas_gate system index counters)
      (vas_finish_action system index transition)
      (encode_vas_config system (VASTransitionTarget transition) counters).
Proof.
  intros d q system index transition counters Hnth. split.
  - pose proof (encode_vas_transitions_nth d q system system 0 index
      transition Hnth) as [_ Hfinish].
    now replace (0 + index)%nat with index in Hfinish by lia.
  - apply step_equation_action. unfold encode_vas_config, encode_vas_gate,
      vas_finish_action, stateful_encoded_dimension.
    repeat rewrite nvec_to_zvec_append. repeat rewrite zvec_add_append.
    rewrite !nvec_to_zvec_zero, zvec_add_zero, zvec_zero_add, state_credit_of_nat,
      (zvec_add_comm (List.length system)
        (nvec_to_zvec (one_hot_nat (List.length system) index))
        (gate_debit (List.length system) index)),
      gate_debit_cancels. reflexivity.
Qed.

Lemma vas_finish_not_from_normal : forall d q (system : VAS d q)
    index transition state counters target,
    nth_error system index = Some transition ->
    ~ PlainVASStep (erase_vas_states system)
        (encode_vas_config system state counters)
        (vas_finish_action system index transition) target.
Proof.
  intros d q system index transition state counters target Hnth
    [_ Haction].
  pose proof (step_action_equation _
    (encode_vas_config system state counters) target) as Heq.
  rewrite <- Haction in Heq.
  destruct (vector_three_parts nat d q (List.length system) target)
    as [out_counters [out_states [out_gates Htarget]]].
  unfold encode_vas_config, vas_finish_action,
    stateful_encoded_dimension in Heq.
  rewrite Htarget in Heq. repeat rewrite nvec_to_zvec_append in Heq.
  repeat rewrite zvec_add_append in Heq.
  apply Vector.append_inj in Heq as [_ Hgate].
  assert (Hindex : (index < List.length system)%nat).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  pose (position := Fin.of_nat_lt Hindex).
  pose proof (f_equal (fun vector => Vector.nth vector position) Hgate)
    as Hcoord.
  unfold nvec_to_zvec, nvec_zero, gate_debit, zvec_add in Hcoord.
  rewrite (nth_map2 Z.add _ _ position position position eq_refl eq_refl),
    (nth_map Z.opp _ position position eq_refl) in Hcoord.
  repeat rewrite (nth_map Z.of_nat _ position position eq_refl) in Hcoord.
  rewrite (const_nth nat 0%nat _ position) in Hcoord.
  unfold one_hot_z, position in Hcoord.
  rewrite nth_vector_of_function, Fin.to_nat_of_nat, Nat.eqb_refl in Hcoord.
  lia.
Qed.

Lemma vas_start_from_normal_inverse : forall d q (system : VAS d q)
    index transition state counters target,
    PlainVASStep (erase_vas_states system)
      (encode_vas_config system state counters)
      (vas_start_action system index transition) target ->
    state = VASTransitionSource transition /\
    exists next_counters,
      target = encode_vas_gate system index next_counters /\
      VASTransitionAction transition = StepAction counters next_counters.
Proof.
  intros d q system index transition state counters target [_ Haction].
  pose proof (step_action_equation _
    (encode_vas_config system state counters) target) as Heq.
  rewrite <- Haction in Heq.
  destruct (vector_three_parts nat d q (List.length system) target)
    as [out_counters [out_states [out_gates Htarget]]].
  unfold encode_vas_config, vas_start_action,
    stateful_encoded_dimension in Heq.
  rewrite Htarget in Heq. repeat rewrite nvec_to_zvec_append in Heq.
  repeat rewrite zvec_add_append in Heq.
  apply Vector.append_inj in Heq as [Hprefix Hgate].
  apply Vector.append_inj in Hprefix as [Hcounter Hstate].
  assert (Hstate_count :
      state_count [state] = one_hot_state state).
  { rewrite state_count_cons, state_count_nil, nvec_add_zero. reflexivity. }
  assert (Hstate_exact :
      zvec_add (state_debit [VASTransitionSource transition])
        (nvec_to_zvec (state_count [state])) = nvec_to_zvec out_states).
  { rewrite Hstate_count, zvec_add_comm. symmetry. exact Hstate. }
  destruct (state_debit_exact q [VASTransitionSource transition] [state]
    out_states eq_refl Hstate_exact) as [Hperm Hout_states].
  assert (Hstate_eq : state = VASTransitionSource transition).
  { assert (Hin : List.In state [VASTransitionSource transition]).
    { eapply Permutation_in; [exact Hperm|now left]. }
    cbn in Hin. destruct Hin as [Hin|Hin]; [now symmetry|contradiction]. }
  assert (Hout_gates : out_gates =
      one_hot_nat (List.length system) index).
  { apply nvec_to_zvec_inj. rewrite one_hot_z_of_nat.
    rewrite nvec_to_zvec_zero, zvec_zero_add in Hgate. exact Hgate. }
  split; [exact Hstate_eq|]. exists out_counters. split.
  - rewrite Htarget, Hout_states, Hout_gates. reflexivity.
  - apply step_equation_action. exact Hcounter.
Qed.

Lemma vas_start_not_from_gate : forall d q (system : VAS d q)
    gate_index transition_index transition counters target,
    ~ PlainVASStep (erase_vas_states system)
        (encode_vas_gate system gate_index counters)
        (vas_start_action system transition_index transition) target.
Proof.
  intros d q system gate_index transition_index transition counters target
    [_ Haction].
  pose proof (step_action_equation _
    (encode_vas_gate system gate_index counters) target) as Heq.
  rewrite <- Haction in Heq.
  destruct (vector_three_parts nat d q (List.length system) target)
    as [out_counters [out_states [out_gates Htarget]]].
  unfold encode_vas_gate, vas_start_action,
    stateful_encoded_dimension in Heq.
  rewrite Htarget in Heq. repeat rewrite nvec_to_zvec_append in Heq.
  repeat rewrite zvec_add_append in Heq.
  apply Vector.append_inj in Heq as [Hprefix _].
  apply Vector.append_inj in Hprefix as [_ Hstate].
  pose proof (f_equal (fun vector =>
    Vector.nth vector (VASTransitionSource transition)) Hstate) as Hcoord.
  unfold nvec_to_zvec, nvec_zero, state_debit, zvec_add in Hcoord.
  rewrite (nth_map Z.of_nat out_states _ _ eq_refl),
    (nth_map2 Z.add _ _ _ _ _ eq_refl eq_refl) in Hcoord.
  repeat rewrite nth_vector_of_function in Hcoord.
  rewrite (nth_map Z.of_nat _ _ _ eq_refl),
    (const_nth nat 0%nat q (VASTransitionSource transition)) in Hcoord.
  cbn in Hcoord. destruct (Fin.eq_dec (VASTransitionSource transition)
    (VASTransitionSource transition)); [|contradiction]. lia.
Qed.

Lemma vas_finish_from_gate_inverse : forall d q (system : VAS d q)
    gate_index transition_index transition counters target,
    (gate_index < List.length system)%nat ->
    nth_error system transition_index = Some transition ->
    PlainVASStep (erase_vas_states system)
      (encode_vas_gate system gate_index counters)
      (vas_finish_action system transition_index transition) target ->
    gate_index = transition_index /\
    target = encode_vas_config system
      (VASTransitionTarget transition) counters.
Proof.
  intros d q system gate_index transition_index transition counters target
    Hgate_index Hnth [_ Haction].
  pose proof (step_action_equation _
    (encode_vas_gate system gate_index counters) target) as Heq.
  rewrite <- Haction in Heq.
  destruct (vector_three_parts nat d q (List.length system) target)
    as [out_counters [out_states [out_gates Htarget]]].
  unfold encode_vas_gate, vas_finish_action,
    stateful_encoded_dimension in Heq.
  rewrite Htarget in Heq. repeat rewrite nvec_to_zvec_append in Heq.
  repeat rewrite zvec_add_append in Heq.
  apply Vector.append_inj in Heq as [Hprefix Hgate].
  apply Vector.append_inj in Hprefix as [Hcounter Hstate].
  assert (Htransition_index : (transition_index < List.length system)%nat).
  { apply nth_error_Some. rewrite Hnth. discriminate. }
  assert (Hindices : gate_index = transition_index).
  { destruct (Nat.eq_dec gate_index transition_index) as [Heq_index|Hneq];
      [exact Heq_index|].
    pose (position := Fin.of_nat_lt Htransition_index).
    pose proof (f_equal (fun vector => Vector.nth vector position) Hgate)
      as Hcoord.
    unfold nvec_to_zvec, gate_debit, zvec_add in Hcoord.
    rewrite (nth_map2 Z.add _ _ position position position eq_refl eq_refl),
      (nth_map Z.opp _ position position eq_refl) in Hcoord.
    repeat rewrite (nth_map Z.of_nat _ position position eq_refl) in Hcoord.
    unfold one_hot_nat, one_hot_z, position in Hcoord.
    repeat rewrite nth_vector_of_function in Hcoord.
    rewrite !Fin.to_nat_of_nat, Nat.eqb_refl in Hcoord.
    destruct (Nat.eqb gate_index transition_index) eqn:Heqb.
    - apply Nat.eqb_eq in Heqb. contradiction.
    - change (Z.of_nat (Vector.nth out_gates (Fin.of_nat_lt Htransition_index)) =
        Z.of_nat (if Nat.eqb transition_index gate_index then 1%nat else 0%nat)
          + -1)%Z in Hcoord.
      rewrite (Nat.eqb_sym transition_index gate_index), Heqb in Hcoord. lia. }
  subst transition_index.
  assert (Hout_counters : out_counters = counters).
  { apply nvec_to_zvec_inj. rewrite zvec_add_zero in Hcounter.
    exact Hcounter. }
  assert (Hout_states : out_states =
      one_hot_state (VASTransitionTarget transition)).
  { apply nvec_to_zvec_inj. rewrite state_credit_of_nat.
    rewrite nvec_to_zvec_zero, zvec_zero_add in Hstate. exact Hstate. }
  assert (Hout_gates : out_gates = nvec_zero (List.length system)).
  { apply nvec_to_zvec_inj.
    rewrite nvec_to_zvec_zero.
    rewrite (zvec_add_comm _
      (nvec_to_zvec (one_hot_nat (List.length system) gate_index))
      (gate_debit (List.length system) gate_index)), gate_debit_cancels in Hgate.
    exact Hgate. }
  split; [reflexivity|]. rewrite Htarget, Hout_counters, Hout_states,
    Hout_gates. reflexivity.
Qed.

Theorem direct_vas_reach_encoded : forall d q (system : VAS d q)
    source_state source target_state target,
    DirectVASReach system source_state source target_state target ->
    VASReach system source_state source target_state target.
Proof.
  intros d q system source_state source target_state target Hreach.
  induction Hreach.
  - constructor.
  - apply In_nth_error in H as [index Hindex].
    eapply plain_vas_reach_step with (target := encode_vas_gate system index target).
    + destruct (vas_start_step_nth d q system index transition source target
        Hindex H0) as [Hin Heq]. rewrite <- Heq. exact Hin.
    + eapply plain_vas_reach_step with
        (target := encode_vas_config system
          (VASTransitionTarget transition) target).
      * destruct (vas_finish_step_nth d q system index transition target Hindex)
          as [Hin Heq]. rewrite <- Heq. exact Hin.
      * exact IHHreach.
Qed.

Lemma encoded_vas_reach_direct_aux : forall d q (system : VAS d q)
    target_state target value,
    PlainVASReach (erase_vas_states system) value
      (encode_vas_config system target_state target) ->
    (forall state counters,
      value = encode_vas_config system state counters ->
      DirectVASReach system state counters target_state target) /\
    (forall index transition counters,
      nth_error system index = Some transition ->
      value = encode_vas_gate system index counters ->
      DirectVASReach system (VASTransitionTarget transition) counters
        target_state target).
Proof.
  intros d q system target_state target value Hreach.
  remember (encode_vas_config system target_state target) as final eqn:Hfinal.
  change (PlainVASReach (erase_vas_states system) value final) in Hreach.
  revert target_state target Hfinal.
  induction Hreach as [value|value next final Hstep Htail IH];
    intros target_state target Hfinal.
  - split.
    + intros state counters Heq.
      destruct (encode_vas_config_inj d q system target_state target
        state counters (eq_trans (eq_sym Hfinal) Heq))
        as [Hstate Hcounters]. subst. constructor.
    + intros index transition counters Hnth Heq.
      exfalso. eapply (encode_vas_gate_state_distinct d q system index
        counters target_state target).
      exact (eq_trans (eq_sym Heq) Hfinal).
  - destruct (erase_vas_states_in d q system (StepAction value next) Hstep)
      as [position [selected [Hnth [Hstart|Hfinish]]]].
    + split.
      * intros state counters Hvalue. subst value.
        assert (Hplain : PlainVASStep (erase_vas_states system)
            (encode_vas_config system state counters)
            (vas_start_action system position selected) next).
        { split; [now rewrite <- Hstart|now symmetry]. }
        destruct (vas_start_from_normal_inverse d q system position selected
          state counters next Hplain) as [Hstate [next_counters [Hnext Haction]]].
        subst state next.
        eapply direct_vas_reach_step with (transition := selected)
          (target := next_counters).
        -- apply nth_error_In in Hnth. exact Hnth.
        -- exact Haction.
        -- apply (proj2 (IH target_state target Hfinal)
             position selected next_counters Hnth). reflexivity.
      * intros index transition counters Hindex Hvalue. subst value.
        exfalso. eapply (vas_start_not_from_gate d q system index position
          selected counters next).
        split; [now rewrite <- Hstart|now symmetry].
    + split.
      * intros state counters Hvalue. subst value.
        exfalso. eapply (vas_finish_not_from_normal d q system position
          selected state counters next Hnth).
        split; [now rewrite <- Hfinish|now symmetry].
      * intros index transition counters Hindex Hvalue. subst value.
        assert (Hplain : PlainVASStep (erase_vas_states system)
            (encode_vas_gate system index counters)
            (vas_finish_action system position selected) next).
        { split; [now rewrite <- Hfinish|now symmetry]. }
        assert (Hindex_bound : (index < List.length system)%nat).
        { apply nth_error_Some. rewrite Hindex. discriminate. }
        destruct (vas_finish_from_gate_inverse d q system index position
          selected counters next Hindex_bound Hnth Hplain)
          as [Hposition Hnext].
        subst position next.
        rewrite Hindex in Hnth. inversion Hnth; subst selected.
        apply (proj1 (IH target_state target Hfinal)
          (VASTransitionTarget transition) counters).
        reflexivity.
Qed.

Theorem encoded_vas_reach_direct : forall d q (system : VAS d q)
    source_state source target_state target,
    VASReach system source_state source target_state target ->
    DirectVASReach system source_state source target_state target.
Proof.
  intros d q system source_state source target_state target Hreach.
  exact (proj1 (encoded_vas_reach_direct_aux d q system target_state target
    (encode_vas_config system source_state source) Hreach)
    source_state source eq_refl).
Qed.

Theorem vas_reach_direct_iff : forall d q (system : VAS d q)
    source_state source target_state target,
    VASReach system source_state source target_state target <->
    DirectVASReach system source_state source target_state target.
Proof.
  intros. split; [apply encoded_vas_reach_direct|apply direct_vas_reach_encoded].
Qed.
