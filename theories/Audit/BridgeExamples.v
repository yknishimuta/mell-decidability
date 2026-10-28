From Mell.BVASS Require Import Stateful ContextInsertion OrderedBridge.
From Mell.Reduction Require Import StateErasure.
From Mell.Order Require Import AlmostFullBridge FiniteBasis.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import Runs.
From Coq Require Import List Vector ZArith Lia Program.Equality Sorting.Permutation.

Import ListNotations.

Definition bridge_nv1 (n : nat) : NVec 1 := Vector.of_list [n].
Definition bridge_zv1 (z : Z) : ZVec 1 := Vector.of_list [z].

Definition bridge_q : Fin.t 2 := Fin.F1.
Definition bridge_r : Fin.t 2 := Fin.FS Fin.F1.

Definition q_plus_one : SRule 1 2 :=
  {| input_states := [bridge_q];
     input_nonempty := ltac:(discriminate);
     output_state := bridge_q;
     rule_delta := bridge_zv1 1%Z |}.

Definition state_sensitive_system : SBVAS 1 2 :=
  {| initial_configs := [(bridge_r, bridge_nv1 0)];
     stateful_rules := [q_plus_one] |}.

Example state_sensitive_initial :
    SReach state_sensitive_system bridge_r (bridge_nv1 0).
Proof. constructor. cbn. auto. Qed.

Example state_sensitive_false_increment :
    ~ SReach state_sensitive_system bridge_r (bridge_nv1 1).
Proof.
  assert (Hcases : forall state counters,
      SReach state_sensitive_system state counters ->
      (state = bridge_r /\ counters = bridge_nv1 0) \/ state = bridge_q).
  { intros state counters Hreach. induction Hreach as
      [state counters Hin
      |rule children result Hrule Hchildren IHchildren Hstates _].
    - cbn in Hin. destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
      left; auto.
    - cbn in Hrule. destruct Hrule as [Heq|Hfalse]; [|contradiction].
      inversion Heq; subst. right; reflexivity. }
  intro Hreach. destruct (Hcases _ _ Hreach) as [[_ Heq]|Heq].
  - inversion Heq.
  - discriminate.
Qed.

Example fresh_gate_rejects_state_erasure_false_positive :
    ~ Reach (erase_states state_sensitive_system)
      (encode_state_config state_sensitive_system bridge_r (bridge_nv1 1)).
Proof.
  intro Hreach. apply state_sensitive_false_increment.
  apply (proj2 (erase_states_correct 1 2 state_sensitive_system
    bridge_r (bridge_nv1 1))). exact Hreach.
Qed.

Definition duplicate_rule : SRule 1 2 :=
  {| input_states := [bridge_q; bridge_q];
     input_nonempty := ltac:(discriminate);
     output_state := bridge_r;
     rule_delta := bridge_zv1 (-1)%Z |}.

Definition duplicate_system : SBVAS 1 2 :=
  {| initial_configs := [(bridge_q, bridge_nv1 1); (bridge_q, bridge_nv1 2)];
     stateful_rules := [duplicate_rule] |}.

Example duplicate_input_and_negative_update :
    SReach duplicate_system bridge_r (bridge_nv1 2).
Proof.
  eapply sreach_rule with (rule := duplicate_rule)
    (child_configs := [(bridge_q, bridge_nv1 2); (bridge_q, bridge_nv1 1)]).
  - cbn. auto.
  - constructor.
    + apply sreach_initial. cbn. auto.
    + constructor.
      * apply sreach_initial. cbn. auto.
      * constructor.
  - apply Permutation_refl.
  - reflexivity.
Qed.

Example duplicate_children_can_be_reordered :
    SReach duplicate_system bridge_r (bridge_nv1 2).
Proof.
  eapply sreach_rule_reorder with (rule := duplicate_rule)
    (left := [(bridge_q, bridge_nv1 1); (bridge_q, bridge_nv1 2)])
    (right := [(bridge_q, bridge_nv1 2); (bridge_q, bridge_nv1 1)]).
  - cbn. auto.
  - apply perm_swap.
  - repeat constructor; apply sreach_initial; cbn; auto.
  - apply Permutation_refl.
  - reflexivity.
Qed.

Example negative_update_is_inapplicable_below_zero :
    add_displacement (bridge_zv1 (-3)%Z)
      [bridge_nv1 1; bridge_nv1 1] = None.
Proof. reflexivity. Qed.

Definition q_plus_one_to_r : SRule 1 2 :=
  {| input_states := [bridge_q];
     input_nonempty := ltac:(discriminate);
     output_state := bridge_r;
     rule_delta := bridge_zv1 1%Z |}.

Definition equal_displacement_system : SBVAS 1 2 :=
  {| initial_configs := [(bridge_q, bridge_nv1 0)];
     stateful_rules := [q_plus_one; q_plus_one_to_r] |}.

Example equal_displacement_distinct_gates_reach_both_outputs :
    Reach (erase_states equal_displacement_system)
      (encode_state_config equal_displacement_system bridge_q (bridge_nv1 1)) /\
    Reach (erase_states equal_displacement_system)
      (encode_state_config equal_displacement_system bridge_r (bridge_nv1 1)).
Proof.
  split.
  - apply (proj1 (erase_states_correct 1 2 equal_displacement_system
      bridge_q (bridge_nv1 1))).
    eapply sreach_rule with (rule := q_plus_one)
      (child_configs := [(bridge_q, bridge_nv1 0)]).
    + cbn. auto.
    + repeat constructor; cbn; auto.
    + apply Permutation_refl.
    + reflexivity.
  - apply (proj1 (erase_states_correct 1 2 equal_displacement_system
      bridge_r (bridge_nv1 1))).
    eapply sreach_rule with (rule := q_plus_one_to_r)
      (child_configs := [(bridge_q, bridge_nv1 0)]).
    + cbn. auto.
    + repeat constructor; cbn; auto.
    + apply Permutation_refl.
    + reflexivity.
Qed.

(* A nonnegative nullary transition is represented as an initial configuration;
   [SRule] itself deliberately enforces positive arity. *)
Definition translated_nullary_system : SBVAS 1 2 :=
  {| initial_configs := [(bridge_q, bridge_nv1 3)]; stateful_rules := [] |}.

Example translated_nullary_transition_is_initial :
    SReach translated_nullary_system bridge_q (bridge_nv1 3).
Proof. constructor. cbn. auto. Qed.

Example stateful_rules_are_never_nullary : forall d q (rule : SRule d q),
    input_states rule <> [].
Proof. intros; apply input_nonempty. Qed.

Definition zero_dim_system : SBVAS 0 1 :=
  {| initial_configs := [(Fin.F1, @Vector.nil nat)]; stateful_rules := [] |}.

Example zero_dimension_stateful_initial :
    SReach zero_dim_system Fin.F1 (@Vector.nil nat).
Proof. constructor. cbn. auto. Qed.

Example empty_state_space_has_no_configuration : forall d,
    SConfig d 0 -> False.
Proof. intros d [state counters]. inversion state. Qed.

Definition empty_stateful_system : SBVAS 1 1 :=
  {| initial_configs := []; stateful_rules := [] |}.

Example empty_stateful_erasure_unreachable : forall value,
    ~ Reach (erase_states empty_stateful_system) value.
Proof. intro value. apply empty_initials_unreachable. Qed.

(* RED contract for the R05 multiset/context-family order. *)
Definition qr_binary_rule : SRule 1 2 :=
  {| input_states := [bridge_q; bridge_r];
     input_nonempty := ltac:(discriminate);
     output_state := bridge_q;
     rule_delta := bridge_zv1 0%Z |}.

Definition qr_binary_system : SBVAS 1 2 :=
  {| initial_configs := [(bridge_q, bridge_nv1 0);
                          (bridge_r, bridge_nv1 0)];
     stateful_rules := [qr_binary_rule] |}.

Definition qr_run : SRun 1 2 :=
  srun_node qr_binary_rule
    (sruns_cons (srun_leaf (bridge_q, bridge_nv1 0))
      (sruns_cons (srun_leaf (bridge_r, bridge_nv1 0)) sruns_nil))
    (bridge_q, bridge_nv1 0).

Definition rq_run : SRun 1 2 :=
  srun_node qr_binary_rule
    (sruns_cons (srun_leaf (bridge_r, bridge_nv1 0))
      (sruns_cons (srun_leaf (bridge_q, bridge_nv1 0)) sruns_nil))
    (bridge_q, bridge_nv1 0).

Example qr_run_valid : ValidSRun qr_binary_system qr_run.
Proof.
  unfold qr_run. econstructor.
  - cbn. auto.
  - constructor.
    + constructor. cbn. auto.
    + constructor.
      * constructor. cbn. auto.
      * constructor.
  - apply Permutation_refl.
  - reflexivity.
  - reflexivity.
Qed.

Example rq_run_valid : ValidSRun qr_binary_system rq_run.
Proof.
  unfold rq_run. econstructor.
  - cbn. auto.
  - constructor.
    + constructor. cbn. auto.
    + constructor.
      * constructor. cbn. auto.
      * constructor.
  - apply perm_swap.
  - reflexivity.
  - reflexivity.
Qed.

Lemma qr_rq_isomorphic : SRunIsomorphic qr_run rq_run.
Proof.
  unfold qr_run, rq_run. constructor.
  eapply sruns_iso_cons with
    (right := srun_leaf (bridge_q, bridge_nv1 0))
    (remainder := sruns_cons (srun_leaf (bridge_r, bridge_nv1 0)) sruns_nil).
  - constructor 2. constructor.
  - constructor.
  - eapply sruns_iso_cons with
      (right := srun_leaf (bridge_r, bridge_nv1 0))
      (remainder := sruns_nil).
    + constructor.
    + constructor.
    + constructor.
Qed.

Lemma rq_qr_isomorphic : SRunIsomorphic rq_run qr_run.
Proof.
  unfold qr_run, rq_run. constructor.
  eapply sruns_iso_cons with
    (right := srun_leaf (bridge_r, bridge_nv1 0))
    (remainder := sruns_cons (srun_leaf (bridge_q, bridge_nv1 0)) sruns_nil).
  - constructor 2. constructor.
  - constructor.
  - eapply sruns_iso_cons with
      (right := srun_leaf (bridge_q, bridge_nv1 0))
      (remainder := sruns_nil).
    + constructor.
    + constructor.
    + constructor.
Qed.

Example child_permutation_context_order_both_directions :
    ContextOrder qr_binary_system qr_run rq_run /\
    ContextOrder qr_binary_system rq_run qr_run.
Proof.
  split.
  - apply context_order_of_isomorphism;
      [apply qr_run_valid|apply rq_run_valid|apply qr_rq_isomorphic].
  - apply context_order_of_isomorphism;
      [apply rq_run_valid|apply qr_run_valid|apply rq_qr_isomorphic].
Qed.

Lemma ordered_node_not_embed_leaf : forall d q rule children result config,
    ~ @OrderedDecorEmbed d q (srun_node rule children result)
      (srun_leaf config).
Proof. intros d q rule children result config H; inversion H. Qed.

Lemma sruns_in_two_inv : forall d q (selected first second : SRun d q),
    SRunsIn selected (sruns_cons first (sruns_cons second sruns_nil)) ->
    selected = first \/ selected = second.
Proof.
  intros d q selected first second Hin. inversion Hin; subst; auto.
  match goal with
  | Htail : SRunsIn selected (sruns_cons second sruns_nil) |- _ =>
      inversion Htail; subst; auto;
      match goal with Hnil : SRunsIn _ sruns_nil |- _ => inversion Hnil end
  end.
Qed.

(* The list-based strong embedding remembers positions; the paper's context
   order remembers child occurrences only up to permutation. *)
Example positional_decoration_rejects_permuted_children :
    ~ OrderedDecorEmbed qr_run rq_run.
Proof.
  intro Hembed. unfold qr_run, rq_run in Hembed.
  inversion Hembed; subst.
  - match goal with
    | Hchildren : OrderedDecorEmbeds _ _ |- _ => inversion Hchildren; subst
    end.
    match goal with
    | Hleaf : OrderedDecorEmbed
        (srun_leaf (bridge_q, bridge_nv1 0))
        (srun_leaf (bridge_r, bridge_nv1 0)) |- _ => inversion Hleaf
    end.
  - match goal with
    | Hin : SRunsIn ?child
        (sruns_cons (srun_leaf (bridge_r, bridge_nv1 0))
          (sruns_cons (srun_leaf (bridge_q, bridge_nv1 0)) sruns_nil)),
      Hbelow : OrderedDecorEmbed (srun_node _ _ _) ?child |- _ =>
        destruct (sruns_in_two_inv 1 2 child _ _ Hin) as [Heq|Heq];
        subst child;
        now apply ordered_node_not_embed_leaf in Hbelow
    end.
Qed.

Definition duplicate_run_12 : SRun 1 2 :=
  srun_node duplicate_rule
    (sruns_cons (srun_leaf (bridge_q, bridge_nv1 1))
      (sruns_cons (srun_leaf (bridge_q, bridge_nv1 2)) sruns_nil))
    (bridge_r, bridge_nv1 2).

Definition duplicate_run_21 : SRun 1 2 :=
  srun_node duplicate_rule
    (sruns_cons (srun_leaf (bridge_q, bridge_nv1 2))
      (sruns_cons (srun_leaf (bridge_q, bridge_nv1 1)) sruns_nil))
    (bridge_r, bridge_nv1 2).

Lemma duplicate_run_12_valid : ValidSRun duplicate_system duplicate_run_12.
Proof.
  unfold duplicate_run_12. econstructor.
  - cbn. auto.
  - constructor.
    + constructor. cbn. auto.
    + constructor.
      * constructor. cbn. auto.
      * constructor.
  - apply Permutation_refl.
  - reflexivity.
  - reflexivity.
Qed.

Lemma duplicate_run_21_valid : ValidSRun duplicate_system duplicate_run_21.
Proof.
  unfold duplicate_run_21. econstructor.
  - cbn. auto.
  - constructor.
    + constructor. cbn. auto.
    + constructor.
      * constructor. cbn. auto.
      * constructor.
  - apply Permutation_refl.
  - reflexivity.
  - reflexivity.
Qed.

Lemma duplicate_runs_isomorphic :
    SRunIsomorphic duplicate_run_12 duplicate_run_21.
Proof.
  unfold duplicate_run_12, duplicate_run_21. constructor.
  eapply sruns_iso_cons with
    (right := srun_leaf (bridge_q, bridge_nv1 1))
    (remainder := sruns_cons
      (srun_leaf (bridge_q, bridge_nv1 2)) sruns_nil).
  - constructor 2. constructor.
  - constructor.
  - eapply sruns_iso_cons with
      (right := srun_leaf (bridge_q, bridge_nv1 2))
      (remainder := sruns_nil); constructor.
Qed.

Example duplicate_state_occurrences_are_matched_separately :
    ContextOrder duplicate_system duplicate_run_12 duplicate_run_21.
Proof.
  apply context_order_of_isomorphism.
  - apply duplicate_run_12_valid.
  - apply duplicate_run_21_valid.
  - apply duplicate_runs_isomorphic.
Qed.

Definition qr_q_leaf : SRun 1 2 :=
  srun_leaf (bridge_q, bridge_nv1 0).
Definition qr_r_leaf : SRun 1 2 :=
  srun_leaf (bridge_r, bridge_nv1 0).

Example context_order_rejects_root_state_mismatch :
    ~ ContextOrder qr_binary_system qr_q_leaf qr_r_leaf.
Proof.
  intro Horder.
  pose proof (context_order_root_state 1 2 qr_binary_system
    qr_q_leaf qr_r_leaf Horder) as Hstate.
  discriminate.
Qed.

Definition q_minus_one : SRule 1 2 :=
  {| input_states := [bridge_q];
     input_nonempty := ltac:(discriminate);
     output_state := bridge_q;
     rule_delta := bridge_zv1 (-1)%Z |}.

Definition subtree_balance_run : SRun 1 2 :=
  srun_node duplicate_rule
    (sruns_cons (srun_leaf (bridge_q, bridge_nv1 1))
      (sruns_cons (srun_leaf (bridge_q, bridge_nv1 0)) sruns_nil))
    (bridge_r, bridge_nv1 0).

Definition lower_first_context : SContext 1 2 :=
  scontext_node q_minus_one sruns_nil scontext_hole sruns_nil
    (bridge_q, bridge_nv1 0).

Definition raise_second_context : SContext 1 2 :=
  scontext_node q_plus_one sruns_nil scontext_hole sruns_nil
    (bridge_q, bridge_nv1 1).

Definition subtree_balance_family : SContextFamily subtree_balance_run :=
  family_node scontext_hole
    (families_cons (family_leaf lower_first_context)
      (families_cons (family_leaf raise_second_context) families_nil))
    (bridge_r, bridge_nv1 0).

Example root_nonnegative_does_not_hide_negative_proper_subtree :
    RootConfigLe (root_config subtree_balance_run)
      (root_config (insert_context_family subtree_balance_family)) /\
    ~ HereditarilyPositive subtree_balance_run subtree_balance_family.
Proof.
  split.
  - split; [reflexivity|intro index].
    dependent destruction index; cbn; [lia|dependent destruction index].
  - intro Hpositive.
    pose proof (positive_family_children_general Hpositive) as Hchildren.
    pose proof (positive_families_head_general Hchildren) as Hfirst.
    pose proof (positive_context_family_root_general Hfirst) as Hroot.
    cbn [lower_first_context] in Hroot.
    destruct Hroot as [_ Hle]. specialize (Hle Fin.F1). cbn in Hle. lia.
Qed.

Check stateful_run_reach_iff.
Check erase_states_correct.
Check ordered_embed_implies_context_insert.
Check context_family_effect_exact.
Check hereditary_positive_effect_nonnegative.
Check context_order_refl.
Check context_order_trans.
Check context_order_wqo.
Check context_order_finite_cover.
Check irun_le_wqo.
Check irun_le_finite_cover.

Print Assumptions stateful_run_reach_iff.
Print Assumptions erase_states_correct.
Print Assumptions ordered_embed_implies_context_insert.
Print Assumptions context_family_effect_exact.
Print Assumptions hereditary_positive_effect_nonnegative.
Print Assumptions context_order_refl.
Print Assumptions context_order_trans.
Print Assumptions context_order_wqo.
Print Assumptions context_order_finite_cover.
Print Assumptions irun_le_wqo.
Print Assumptions irun_le_finite_cover.
