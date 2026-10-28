From Coq Require Import List Vector ZArith Lia Sorting.Permutation.
From Mell.Core Require Import Vector.

Import ListNotations.

Definition SConfig (d q : nat) := (Fin.t q * NVec d)%type.

Record SRule (d q : nat) : Type := {
  input_states : list (Fin.t q);
  input_nonempty : input_states <> [];
  output_state : Fin.t q;
  rule_delta : ZVec d
}.

Arguments input_states {d q} _.
Arguments input_nonempty {d q} _.
Arguments output_state {d q} _.
Arguments rule_delta {d q} _.

Record SBVAS (d q : nat) : Type := {
  initial_configs : list (SConfig d q);
  stateful_rules : list (SRule d q)
}.

Arguments initial_configs {d q} _.
Arguments stateful_rules {d q} _.

Inductive SReach {d q} (S : SBVAS d q) : Fin.t q -> NVec d -> Prop :=
| sreach_initial : forall state counters,
    List.In (state, counters) (initial_configs S) ->
    SReach S state counters
| sreach_rule : forall rule child_configs result,
    List.In rule (stateful_rules S) ->
    SReachChildren S child_configs ->
    Permutation (List.map fst child_configs) (input_states rule) ->
    add_displacement (rule_delta rule) (List.map snd child_configs) = Some result ->
    SReach S (output_state rule) result
with SReachChildren {d q} (S : SBVAS d q) : list (SConfig d q) -> Prop :=
| sreach_children_nil : SReachChildren S []
| sreach_children_cons : forall state counters children,
    SReach S state counters -> SReachChildren S children ->
    SReachChildren S ((state, counters) :: children).

Scheme SReach_ind' := Induction for SReach Sort Prop
with SReachChildren_ind' := Induction for SReachChildren Sort Prop.
Combined Scheme SReach_mutind from SReach_ind', SReachChildren_ind'.

Inductive SRun (d q : nat) : Type :=
| srun_leaf : SConfig d q -> SRun d q
| srun_node : SRule d q -> SRuns d q -> SConfig d q -> SRun d q
with SRuns (d q : nat) : Type :=
| sruns_nil : SRuns d q
| sruns_cons : SRun d q -> SRuns d q -> SRuns d q.

Arguments srun_leaf {d q} _.
Arguments srun_node {d q} _ _ _.
Arguments sruns_nil {d q}.
Arguments sruns_cons {d q} _ _.

Scheme SRun_ind' := Induction for SRun Sort Prop
with SRuns_ind' := Induction for SRuns Sort Prop.
Combined Scheme SRun_SRuns_ind from SRun_ind', SRuns_ind'.

Definition root_config {d q} (run : SRun d q) : SConfig d q :=
  match run with
  | srun_leaf config => config
  | srun_node _ _ config => config
  end.

Fixpoint sruns_configs {d q} (runs : SRuns d q) : list (SConfig d q) :=
  match runs with
  | sruns_nil => []
  | sruns_cons run tail => root_config run :: sruns_configs tail
  end.

Inductive ValidSRun {d q} (S : SBVAS d q) : SRun d q -> Prop :=
| valid_srun_leaf : forall config,
    List.In config (initial_configs S) -> ValidSRun S (srun_leaf config)
| valid_srun_node : forall rule children result,
    List.In rule (stateful_rules S) ->
    ValidSRuns S children ->
    Permutation (List.map fst (sruns_configs children)) (input_states rule) ->
    add_displacement (rule_delta rule) (List.map snd (sruns_configs children)) =
      Some (snd result) ->
    fst result = output_state rule ->
    ValidSRun S (srun_node rule children result)
with ValidSRuns {d q} (S : SBVAS d q) : SRuns d q -> Prop :=
| valid_sruns_nil : ValidSRuns S sruns_nil
| valid_sruns_cons : forall run runs,
    ValidSRun S run -> ValidSRuns S runs ->
    ValidSRuns S (sruns_cons run runs).

Scheme ValidSRun_ind' := Induction for ValidSRun Sort Prop
with ValidSRuns_ind' := Induction for ValidSRuns Sort Prop.
Combined Scheme ValidSRun_mutind from ValidSRun_ind', ValidSRuns_ind'.

Lemma valid_srun_reach_mut : forall d q (S : SBVAS d q),
  (forall run, ValidSRun S run ->
    SReach S (fst (root_config run)) (snd (root_config run))) /\
  (forall runs, ValidSRuns S runs -> SReachChildren S (sruns_configs runs)).
Proof.
  intros d q S. apply ValidSRun_mutind; cbn.
  - intros [state counters] Hinitial. apply sreach_initial; exact Hinitial.
  - intros rule children result Hrule Hchildren IHchildren Hstates Happly Houtput.
    destruct result as [state counters]; cbn in *. subst state.
    eapply sreach_rule with (rule := rule)
      (child_configs := sruns_configs children).
    + exact Hrule.
    + exact IHchildren.
    + exact Hstates.
    + exact Happly.
  - constructor.
  - intros run runs Hrun IHrun Hruns IHruns.
    destruct (root_config run) as [state counters] eqn:Hroot.
    cbn in IHrun |- *. constructor; assumption.
Qed.

Lemma sreach_valid_srun_mut : forall d q (S : SBVAS d q),
  (forall state counters, SReach S state counters ->
    exists run, ValidSRun S run /\ root_config run = (state, counters)) /\
  (forall configs, SReachChildren S configs ->
    exists runs, ValidSRuns S runs /\ sruns_configs runs = configs).
Proof.
  intros d q S. apply SReach_mutind.
  - intros state counters Hinitial.
    exists (srun_leaf (state, counters)); split; [constructor|reflexivity].
    exact Hinitial.
  - intros rule child_configs result Hrule Hchildren IHchildren Hstates Happly.
    destruct IHchildren as [runs [Hruns Hconfigs]].
    exists (srun_node rule runs (output_state rule, result)). split.
    + econstructor; cbn; eauto. all: now rewrite Hconfigs.
    + reflexivity.
  - exists sruns_nil. split; [constructor|reflexivity].
  - intros state counters children Hreach [run [Hrun Hroot]]
      Hchildren [runs [Hruns Hconfigs]].
    exists (sruns_cons run runs). split; [constructor; assumption|].
    cbn. now rewrite Hroot, Hconfigs.
Qed.

Theorem stateful_run_reach_iff : forall d q (S : SBVAS d q) state counters,
    SReach S state counters <->
    exists run, ValidSRun S run /\ root_config run = (state, counters).
Proof.
  intros d q S state counters. split.
  - apply (proj1 (sreach_valid_srun_mut d q S)).
  - intros [run [Hvalid Hroot]].
    pose proof (proj1 (valid_srun_reach_mut d q S) run Hvalid) as Hreach.
    rewrite Hroot in Hreach. exact Hreach.
Qed.

Lemma sreach_children_forall : forall d q (S : SBVAS d q) configs,
    SReachChildren S configs <->
    List.Forall (fun config => SReach S (fst config) (snd config)) configs.
Proof.
  intros d q S configs. split.
  - intro H. induction H; constructor; assumption.
  - intro H. induction H as [|[state counters] configs Hhead Htail IH];
      constructor; assumption.
Qed.

Theorem sreach_children_permutation : forall d q (S : SBVAS d q)
    left right,
    Permutation left right ->
    SReachChildren S left -> SReachChildren S right.
Proof.
  intros d q S left right Hperm Hreach.
  apply sreach_children_forall.
  eapply Permutation_Forall; [exact Hperm|].
  apply sreach_children_forall; exact Hreach.
Qed.

Lemma nvec_add_comm_stateful : forall d (left right : NVec d),
    nvec_add left right = nvec_add right left.
Proof.
  intros d left right. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  apply Nat.add_comm.
Qed.

Lemma nvec_add_assoc_stateful : forall d (x y z : NVec d),
    nvec_add (nvec_add x y) z = nvec_add x (nvec_add y z).
Proof.
  intros d x y z. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  symmetry. apply Nat.add_assoc.
Qed.

Lemma nvec_add_zero_left_stateful : forall d (value : NVec d),
    nvec_add (nvec_zero d) value = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add, nvec_zero.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (const_nth nat 0 d index). apply Nat.add_0_l.
Qed.

Fixpoint nvec_rsum_stateful {d} (values : list (NVec d)) : NVec d :=
  match values with
  | [] => nvec_zero d
  | value :: values' => nvec_add value (nvec_rsum_stateful values')
  end.

Lemma fold_left_nvec_add_stateful : forall d (values : list (NVec d)) acc,
    List.fold_left nvec_add values acc =
      nvec_add acc (nvec_rsum_stateful values).
Proof.
  intros d values; induction values as [|value values IH]; intro acc; cbn.
  - rewrite nvec_add_comm_stateful. symmetry. apply nvec_add_zero_left_stateful.
  - rewrite IH, nvec_add_assoc_stateful. reflexivity.
Qed.

Lemma nvec_sum_rsum_stateful : forall d (values : list (NVec d)),
    nvec_sum values = nvec_rsum_stateful values.
Proof.
  intros d values. unfold nvec_sum. rewrite fold_left_nvec_add_stateful.
  apply nvec_add_zero_left_stateful.
Qed.

Lemma nvec_rsum_permutation_stateful : forall d (left right : list (NVec d)),
    Permutation left right ->
    nvec_rsum_stateful left = nvec_rsum_stateful right.
Proof.
  intros d left right Hperm. induction Hperm; cbn.
  - reflexivity.
  - now rewrite IHHperm.
  - apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros index index' Heq; subst index'.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
    lia.
  - now rewrite IHHperm1, IHHperm2.
Qed.

Lemma add_displacement_permutation : forall d (delta : ZVec d)
    (left right : list (NVec d)),
    Permutation left right ->
    add_displacement delta left = add_displacement delta right.
Proof.
  intros d delta left right Hperm. unfold add_displacement.
  repeat rewrite nvec_sum_rsum_stateful.
  now rewrite (nvec_rsum_permutation_stateful d left right Hperm).
Qed.

Theorem sreach_rule_reorder : forall d q (S : SBVAS d q)
    rule left right result,
    List.In rule (stateful_rules S) ->
    Permutation left right ->
    SReachChildren S left ->
    Permutation (List.map fst left) (input_states rule) ->
    add_displacement (rule_delta rule) (List.map snd left) = Some result ->
    SReach S (output_state rule) result.
Proof.
  intros d q S rule left right result Hrule Hperm Hreach Hstates Happly.
  eapply sreach_rule with (rule := rule) (child_configs := right).
  - exact Hrule.
  - exact (sreach_children_permutation d q S left right Hperm Hreach).
  - eapply Permutation_trans with (l' := List.map fst left).
    + apply Permutation_map. now apply Permutation_sym.
    + exact Hstates.
  - rewrite <- Happly.
    apply add_displacement_permutation.
    apply Permutation_map. now apply Permutation_sym.
Qed.

Lemma sreach_rule_inputs_nonempty : forall d q (S : SBVAS d q) rule configs result,
    List.In rule (stateful_rules S) ->
    SReachChildren S configs ->
    Permutation (List.map fst configs) (input_states rule) ->
    add_displacement (rule_delta rule) (List.map snd configs) = Some result ->
    configs <> [].
Proof.
  intros d q S rule configs result Hrule Hchildren Hperm Happly ->.
  apply (input_nonempty rule).
  apply Permutation_length in Hperm. cbn in Hperm.
  destruct (input_states rule); [reflexivity|cbn in Hperm; discriminate].
Qed.
