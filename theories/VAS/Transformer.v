From Coq Require Import List Vector Arith.PeanoNat Lia.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.VAS Require Import Runs.

Import ListNotations.

Definition NRelation (d : nat) := NVec d -> NVec d -> Prop.

Definition NRelSubset {d} (left right : NRelation d) : Prop :=
  forall input output, left input output -> right input output.

Definition NRelSame {d} (left right : NRelation d) : Prop :=
  forall input output, left input output <-> right input output.

Definition NRelIdentity {d} : NRelation d := fun input output => input = output.

(** [NRelCompose R S] executes [R] first and [S] second. *)
Definition NRelCompose {d} (R S : NRelation d) : NRelation d :=
  fun input output => exists middle, R input middle /\ S middle output.

Lemma nrel_same_refl : forall d (R : NRelation d), NRelSame R R.
Proof. firstorder. Qed.

Lemma nrel_same_sym : forall d (R S : NRelation d),
    NRelSame R S -> NRelSame S R.
Proof. firstorder. Qed.

Lemma nrel_same_trans : forall d (R S T : NRelation d),
    NRelSame R S -> NRelSame S T -> NRelSame R T.
Proof.
  intros d R S T HRS HST input output. split.
  - intros HR. apply HST, HRS, HR.
  - intros HT. apply HRS, HST, HT.
Qed.

Lemma nrel_compose_assoc : forall d (R S T : NRelation d),
    NRelSame (NRelCompose (NRelCompose R S) T)
      (NRelCompose R (NRelCompose S T)).
Proof.
  intros d R S T input output. unfold NRelCompose. split.
  - intros [right [[left [HR HS]] HT]]. exists left. split; [exact HR|].
    now exists right.
  - intros [left [HR [right [HS HT]]]]. exists right. split; [|exact HT].
    now exists left.
Qed.

Lemma nrel_compose_identity_left : forall d (R : NRelation d),
    NRelSame (NRelCompose NRelIdentity R) R.
Proof.
  intros d R input output. unfold NRelCompose, NRelIdentity. split.
  - intros [middle [-> HR]]. exact HR.
  - intros HR. exists input. auto.
Qed.

Lemma nrel_compose_identity_right : forall d (R : NRelation d),
    NRelSame (NRelCompose R NRelIdentity) R.
Proof.
  intros d R input output. unfold NRelCompose, NRelIdentity. split.
  - intros [middle [HR ->]]. exact HR.
  - intros HR. exists output. auto.
Qed.

Lemma nrel_compose_monotone : forall d (R R' S S' : NRelation d),
    NRelSubset R R' -> NRelSubset S S' ->
    NRelSubset (NRelCompose R S) (NRelCompose R' S').
Proof.
  intros d R R' S S' HR HS input output [middle [Hleft Hright]].
  exists middle. split; eauto.
Qed.

Lemma nrel_compose_compat : forall d (R R' S S' : NRelation d),
    NRelSame R R' -> NRelSame S S' ->
    NRelSame (NRelCompose R S) (NRelCompose R' S').
Proof.
  intros d R R' S S' HR HS input output. unfold NRelCompose. split;
    intros [middle [Hleft Hright]]; exists middle; split;
    [apply HR|apply HS|apply HR|apply HS]; assumption.
Qed.

Definition CapacityTransformer {d} (system : PlainVAS d)
    (capacity : NVec d) : NRelation d :=
  fun input output =>
    PlainVASReach system
      (nvec_add capacity input) (nvec_add capacity output).

Theorem capacity_transformer_run_iff : forall d (system : PlainVAS d)
    capacity input output,
    CapacityTransformer system capacity input output <->
    exists run : VASRun d,
      ValidVASRun system run /\
      RunSource run = nvec_add capacity input /\
      RunTarget run = nvec_add capacity output.
Proof. intros; apply vas_reach_run_iff. Qed.

Lemma capacity_transformer_refl : forall d (system : PlainVAS d) capacity input,
    CapacityTransformer system capacity input input.
Proof. intros; unfold CapacityTransformer; constructor. Qed.

Lemma nvec_add_comm_transformer : forall d (left right : NVec d),
    nvec_add left right = nvec_add right left.
Proof.
  intros d left right. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Hindex; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl). lia.
Qed.

Lemma capacity_transformer_capacity_monotone : forall d
    (system : PlainVAS d) capacity extra input output,
    CapacityTransformer system capacity input output ->
    CapacityTransformer system (nvec_add capacity extra) input output.
Proof.
  intros d system capacity extra input output H.
  unfold CapacityTransformer in *. apply (vas_reach_monotone _ _ _ _ extra) in H.
  rewrite !nvec_add_assoc in H.
  rewrite (nvec_add_comm_transformer d input extra) in H.
  rewrite (nvec_add_comm_transformer d output extra) in H.
  rewrite !nvec_add_assoc. exact H.
Qed.

Lemma capacity_transformer_compose_closed : forall d
    (system : PlainVAS d) capacity,
    NRelSubset
      (NRelCompose (CapacityTransformer system capacity)
        (CapacityTransformer system capacity))
      (CapacityTransformer system capacity).
Proof.
  intros d system capacity input output [middle [Hleft Hright]].
  unfold CapacityTransformer in *. eapply PlainVASReach_trans; eauto.
Qed.

Definition PeriodicNRelation {d} (relation : NRelation d) : Prop :=
  relation (nvec_zero d) (nvec_zero d) /\
  forall x1 y1 x2 y2,
    relation x1 y1 -> relation x2 y2 ->
    relation (nvec_add x1 x2) (nvec_add y1 y2).

Theorem capacity_transformer_periodic : forall d
    (system : PlainVAS d) (capacity : NVec d),
    PeriodicNRelation (CapacityTransformer system capacity).
Proof.
  intros d system capacity. split.
  - unfold CapacityTransformer. constructor.
  - intros x1 y1 x2 y2 H1 H2. unfold CapacityTransformer in *.
    pose proof (vas_reach_monotone d system _ _ x2 H1) as H1'.
    pose proof (vas_reach_monotone d system _ _ y1 H2) as H2'.
    eapply PlainVASReach_trans.
    + rewrite !nvec_add_assoc in H1'. exact H1'.
    + rewrite !nvec_add_assoc in H2'.
      rewrite (nvec_add_comm_transformer d y1 x2).
      rewrite (nvec_add_comm_transformer d y1 y2).
      exact H2'.
Qed.

Theorem periodic_nrelation_compose : forall d (R S : NRelation d),
    PeriodicNRelation R -> PeriodicNRelation S ->
    PeriodicNRelation (NRelCompose R S).
Proof.
  intros d R S [HRzero HRadd] [HSzero HSadd]. split.
  - exists (nvec_zero d). auto.
  - intros x1 z1 x2 z2 [y1 [HR1 HS1]] [y2 [HR2 HS2]].
    exists (nvec_add y1 y2). split; [eapply HRadd|eapply HSadd]; eauto.
Qed.

Fixpoint NRelComposeList {d} (relations : list (NRelation d)) : NRelation d :=
  match relations with
  | [] => NRelIdentity
  | relation :: tail => NRelCompose relation (NRelComposeList tail)
  end.

Lemma periodic_nrelation_compose_list : forall d relations,
    List.Forall (@PeriodicNRelation d) relations ->
    PeriodicNRelation (NRelComposeList relations).
Proof.
  intros d relations H. induction H; cbn.
  - split; [reflexivity|]. intros x1 y1 x2 y2 -> ->.
    reflexivity.
  - now apply periodic_nrelation_compose.
Qed.

Fixpoint TransformerAlongTargets {d} (system : PlainVAS d)
    (current : NVec d) (targets : list (NVec d)) : NRelation d :=
  match targets with
  | [] => CapacityTransformer system current
  | target :: tail =>
      NRelCompose (CapacityTransformer system current)
        (TransformerAlongTargets system target tail)
  end.

Definition TransformerAlongRun {d} (system : PlainVAS d)
    (run : VASRun d) : NRelation d :=
  TransformerAlongTargets system (RunSource run) (RunTargets run).

Lemma transformer_along_empty_run : forall d (system : PlainVAS d) source,
    NRelSame (TransformerAlongRun system (EmptyVASRun source))
      (CapacityTransformer system source).
Proof. intros; apply nrel_same_refl. Qed.

Theorem transformer_along_run_periodic : forall d
    (system : PlainVAS d) (run : VASRun d),
    PeriodicNRelation (TransformerAlongRun system run).
Proof.
  intros d system [source targets]. cbn. revert source.
  induction targets as [|target tail IH]; intros source; cbn.
  - apply capacity_transformer_periodic.
  - apply periodic_nrelation_compose.
    + apply capacity_transformer_periodic.
    + apply IH.
Qed.
