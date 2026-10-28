From Mell.Geometry Require Import MathCompBridge Periodic Cone.
From Mell.BVAS Require Import Contexts RunOrder Amalgamation.

From Coq Require Import List Vector ZArith QArith Lia Program.Equality.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Check periodic_cone_union_strict.
Check IRunLe.
Check irun_le_refl.
Check irun_le_trans.
Check root_same_action_mono.
Check context_lift.
Check run_amalgamation.

Definition zv1 (value : Z) : ZVec 1 := Vector.of_list [value].
Definition nv1 (value : nat) : NVec 1 := Vector.of_list [value].

Lemma nv1_le : forall left right, (left <= right)%nat ->
    nvec_le (nv1 left) (nv1 right).
Proof.
  intros left right Hle index. dependent destruction index; cbn.
  - exact Hle.
  - dependent destruction index.
Qed.

Definition false_cone_source (value : ZVec 1) : Prop :=
  Vector.hd value = 0%Z \/ (2 <= Vector.hd value)%Z.

Definition old_minkowski_rhs (value : ZVec 1) : Prop :=
  exists even_part remainder : nat,
    Vector.hd value = (2 * Z.of_nat even_part + Z.of_nat remainder)%Z.

Example old_cone_equality_counterexample_rhs : old_minkowski_rhs (zv1 1).
Proof. exists 0%nat, 1%nat; reflexivity. Qed.

Example old_cone_equality_counterexample_lhs :
    ~ false_cone_source (zv1 1).
Proof. unfold false_cone_source, zv1; cbn; lia. Qed.

Definition strict_boundary (x y : Q) : Prop :=
  (x == 0 /\ y == 0) \/ (0 <= x /\ 0 < y).

Definition relaxed_boundary (x y : Q) : Prop :=
  exists lambda horizontal vertical : Q,
    0 <= lambda /\ 0 <= horizontal /\ 0 <= vertical /\
    x == horizontal /\ y == lambda + vertical.

Example non_strict_coefficient_adds_horizontal_axis : relaxed_boundary 1 0.
Proof.
  exists 0, 1, 0. split; [apply Qle_refl |].
  split; [change (0 <= 1)%Z; lia |].
  split; [apply Qle_refl |]. split; reflexivity.
Qed.

Example strict_coefficient_excludes_horizontal_axis : ~ strict_boundary 1 0.
Proof.
  intros [[Hx _] | [_ Hy]].
  - vm_compute in Hx; discriminate.
  - vm_compute in Hy; discriminate.
Qed.

Definition unary_action (offset : Z) : Action 1 :=
  {| action_arity := 1%nat;
     action_arity_positive := Nat.lt_0_succ 0;
     action_offset := zv1 offset |}.

Definition leaf0 : IRun 1 := irun_leaf (nv1 0).
Definition unary1 : IRun 1 :=
  irun_node (unary_action 1) (iruns_cons leaf0 iruns_nil) (nv1 1).
Definition old_eta : IRun 1 :=
  irun_node (unary_action 2) (iruns_cons leaf0 iruns_nil) (nv1 2).
Definition old_theta : IRun 1 :=
  irun_node (unary_action 1) (iruns_cons unary1 iruns_nil) (nv1 2).

(** R05 regression: the total inserted context has effect [+1], although
    its first prefix temporarily lowers the counter from [1] to [0]. *)
Definition ordered_skip_dip : IRun 1 :=
  irun_node (unary_action (-1)) (iruns_cons unary1 iruns_nil) (nv1 0).
Definition ordered_skip_whole : IRun 1 :=
  irun_node (unary_action 2) (iruns_cons ordered_skip_dip iruns_nil) (nv1 2).

Definition ordered_skip_system : IBVAS 1 :=
  {| initial_vectors := [nv1 0];
     system_actions := [unary_action 1; unary_action (-1); unary_action 2] |}.

Lemma ordered_skip_leaf_valid : ValidIRun ordered_skip_system leaf0.
Proof. constructor; cbn; auto. Qed.

Lemma ordered_skip_small_valid : ValidIRun ordered_skip_system unary1.
Proof.
  econstructor; cbn; [auto|constructor; [apply ordered_skip_leaf_valid|constructor]|].
  reflexivity.
Qed.

Lemma ordered_skip_dip_valid : ValidIRun ordered_skip_system ordered_skip_dip.
Proof.
  econstructor; cbn; [auto|constructor; [apply ordered_skip_small_valid|constructor]|].
  reflexivity.
Qed.

Lemma ordered_skip_whole_valid : ValidIRun ordered_skip_system ordered_skip_whole.
Proof.
  econstructor; cbn; [auto|constructor; [apply ordered_skip_dip_valid|constructor]|].
  reflexivity.
Qed.

Example ordered_skip_compares_endpoint_not_intermediate :
    IRunLe unary1 ordered_skip_whole.
Proof.
  split; [apply nv1_le; lia|].
  eapply embed_below with (child := ordered_skip_dip); [constructor|].
  eapply embed_below with (child := unary1); [constructor|].
  apply irun_embed_refl.
Qed.

Definition repair_system : IBVAS 1 :=
  {| initial_vectors := [nv1 0];
     system_actions := [unary_action 1; unary_action 2] |}.

Lemma leaf0_valid : ValidIRun repair_system leaf0.
Proof. constructor; cbn; auto. Qed.

Lemma unary1_valid : ValidIRun repair_system unary1.
Proof.
  econstructor; cbn; [auto | constructor; [apply leaf0_valid | constructor] |].
  reflexivity.
Qed.

Lemma old_eta_valid : ValidIRun repair_system old_eta.
Proof.
  econstructor; cbn; [auto | constructor; [apply leaf0_valid | constructor] |].
  reflexivity.
Qed.

Lemma old_theta_valid : ValidIRun repair_system old_theta.
Proof.
  econstructor; cbn; [auto | constructor; [apply unary1_valid | constructor] |].
  reflexivity.
Qed.

Definition NaiveTargetLe {d} (left right : IRun d) : Prop :=
  nvec_le (irun_target left) (irun_target right).

Example old_fact_b3_premises_hold :
    IRunLe leaf0 unary1 /\
    irun_target old_eta = irun_target old_theta.
Proof.
  split; [|reflexivity]. split; [apply nv1_le; lia |].
  eapply embed_below with (child := leaf0).
  - constructor.
  - apply irun_embed_refl.
Qed.

Inductive HasOffset {d} (offset : ZVec d) : IRun d -> Prop :=
| has_offset_root : forall action children target,
    action_offset action = offset ->
    HasOffset offset (irun_node action children target)
| has_offset_child : forall action children target,
    RunsHaveOffset offset children ->
    HasOffset offset (irun_node action children target)
with RunsHaveOffset {d} (offset : ZVec d) : IRuns d -> Prop :=
| runs_have_offset_here : forall run runs,
    HasOffset offset run -> RunsHaveOffset offset (iruns_cons run runs)
| runs_have_offset_later : forall run runs,
    RunsHaveOffset offset runs -> RunsHaveOffset offset (iruns_cons run runs).

Lemma runs_in_have_offset : forall d offset (run : IRun d) runs,
    IRunsIn run runs -> HasOffset offset run -> RunsHaveOffset offset runs.
Proof.
  intros d offset run runs Hin Hoffset. induction Hin.
  - constructor; exact Hoffset.
  - constructor 2; exact IHHin.
Qed.

Lemma embedded_node_offset_occurs : forall d (action : Action d) children target whole,
    IRunEmbed (irun_node action children target) whole ->
    HasOffset (action_offset action) whole.
Proof.
  intros d action children target whole Hembed.
  remember (irun_node action children target) as small eqn:Hsmall.
  induction Hembed; inversion Hsmall; subst.
  - constructor 1; reflexivity.
  - constructor 2. eapply runs_in_have_offset; eauto.
Qed.

Lemma old_theta_has_no_plus2 : ~ HasOffset (zv1 2) old_theta.
Proof.
  intros Hoccurs.
  inversion Hoccurs as
    [action children target Hoff
    |action children target Hchildren]; subst.
  - apply (f_equal (@Vector.hd Z 0)) in Hoff; cbn in Hoff; lia.
  - inversion Hchildren as
      [run runs Hrun
      |run runs Htail]; subst.
    + inversion Hrun as
        [action' children' target' Hoff
        |action' children' target' Hchildren']; subst.
      * apply (f_equal (@Vector.hd Z 0)) in Hoff; cbn in Hoff; lia.
      * inversion Hchildren' as
          [run' runs' Hleaf
          |run' runs' Hnil]; subst.
        -- inversion Hleaf.
        -- inversion Hnil.
    + inversion Htail.
Qed.

Example old_fact_b3_missing_same_action : ~ IRunLe old_eta old_theta.
Proof.
  intros [_ Hembed]. apply old_theta_has_no_plus2.
  exact (embedded_node_offset_occurs _ _ _ _ _ Hembed).
Qed.

Example same_action_root_example :
    IRunLe
      (irun_node (unary_action 1) (iruns_cons leaf0 iruns_nil) (nv1 1))
      (irun_node (unary_action 1) (iruns_cons unary1 iruns_nil) (nv1 2)).
Proof.
  apply root_same_action_mono; cbn.
  - split; [apply (proj1 old_fact_b3_premises_hold) | exact I].
  - reflexivity.
  - reflexivity.
Qed.

Example leaf_amalgamation_exact : exists merged : IRun 1,
    ValidIRun repair_system merged /\
    IRunLe unary1 merged /\
    IRunLe old_eta merged /\
    nvec_add (nv1 0) (irun_target merged) =
      nvec_add (nv1 1) (nv1 2).
Proof.
  eapply run_amalgamation with (S := repair_system) (root := leaf0).
  - apply leaf0_valid.
  - apply unary1_valid.
  - apply old_eta_valid.
  - apply (proj1 old_fact_b3_premises_hold).
  - split; [apply nv1_le; lia |].
    eapply embed_below with (child := leaf0).
    + constructor.
    + apply irun_embed_refl.
Qed.

Print Assumptions periodic_cone_union_strict.
Print Assumptions periodic_standard_cone_denominator_clearing.
Print Assumptions irun_le_trans.
Print Assumptions context_lift.
Print Assumptions run_amalgamation.
