From Coq Require Import List Vector VectorSpec ZArith Lia.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.

Import ListNotations.
Open Scope Z_scope.

Definition PlainVAS (d : nat) := list (ZVec d).

Definition zvec_sub_run {d} (left right : ZVec d) : ZVec d :=
  Vector.map2 Z.sub left right.

Definition StepAction {d} (source target : NVec d) : ZVec d :=
  zvec_sub_run (nvec_to_zvec target) (nvec_to_zvec source).

Definition PlainVASStep {d} (system : PlainVAS d)
    (source : NVec d) (action : ZVec d) (target : NVec d) : Prop :=
  List.In action system /\ action = StepAction source target.

(** Every run is a connected configuration word. *)
Record VASRun (d : nat) := {
  RunSource : NVec d;
  RunTargets : list (NVec d)
}.
Arguments RunSource {d} _.
Arguments RunTargets {d} _.

Fixpoint steps_of_targets {d} (source : NVec d) (targets : list (NVec d))
    : list (ZVec d * NVec d) :=
  match targets with
  | [] => []
  | target :: tail =>
      (StepAction source target, target) :: steps_of_targets target tail
  end.

Definition RunSteps {d} (run : VASRun d) :=
  steps_of_targets (RunSource run) (RunTargets run).

Fixpoint targets_target {d} (source : NVec d) (targets : list (NVec d)) : NVec d :=
  match targets with [] => source | target :: tail => targets_target target tail end.

Definition RunTarget {d} (run : VASRun d) :=
  targets_target (RunSource run) (RunTargets run).

Definition RunActionWord {d} (run : VASRun d) : list (ZVec d) :=
  List.map fst (RunSteps run).

Fixpoint ValidVASTargets {d} (system : PlainVAS d) (source : NVec d)
    (targets : list (NVec d)) : Prop :=
  match targets with
  | [] => True
  | target :: tail =>
      List.In (StepAction source target) system /\
      ValidVASTargets system target tail
  end.

Definition ValidVASRun {d} (system : PlainVAS d) (run : VASRun d) : Prop :=
  ValidVASTargets system (RunSource run) (RunTargets run).

Inductive PlainVASReach {d} (system : PlainVAS d) : NVec d -> NVec d -> Prop :=
| plain_vas_reach_refl : forall source, PlainVASReach system source source
| plain_vas_reach_step : forall source target final,
    List.In (StepAction source target) system ->
    PlainVASReach system target final -> PlainVASReach system source final.

Lemma valid_targets_reach : forall d (system : PlainVAS d) source targets,
    ValidVASTargets system source targets ->
    PlainVASReach system source (targets_target source targets).
Proof.
  intros d system source targets. revert source.
  induction targets as [|target tail IH]; intros source H; cbn in *.
  - constructor.
  - destruct H as [Hs Ht]. econstructor; eauto.
Qed.

Lemma reach_has_targets : forall d (system : PlainVAS d) source target,
    PlainVASReach system source target ->
    exists targets, ValidVASTargets system source targets /\
      targets_target source targets = target.
Proof.
  intros d system source target H. induction H.
  - exists []; split; reflexivity.
  - destruct IHPlainVASReach as [targets [Hv Ht]].
    exists (target :: targets). cbn. split; [auto|exact Ht].
Qed.

Theorem vas_reach_run_iff : forall d (system : PlainVAS d)
    (source target : NVec d),
    PlainVASReach system source target <->
    exists run : VASRun d,
      ValidVASRun system run /\ RunSource run = source /\ RunTarget run = target.
Proof.
  intros d system source target. split.
  - intros H. destruct (reach_has_targets _ _ _ _ H) as [targets [Hv Ht]].
    exists {| RunSource := source; RunTargets := targets |}. cbn. auto.
  - intros [[run_source targets] [Hv [Hs Ht]]]. cbn in *. subst.
    now apply valid_targets_reach.
Qed.

Definition EmptyVASRun {d} (source : NVec d) : VASRun d :=
  {| RunSource := source; RunTargets := [] |}.

Lemma empty_vas_run_valid : forall d (system : PlainVAS d) source,
    ValidVASRun system (EmptyVASRun source).
Proof. reflexivity. Qed.

Lemma empty_vas_run_endpoints : forall d (source : NVec d),
    RunSource (EmptyVASRun source) = source /\ RunTarget (EmptyVASRun source) = source.
Proof. intros; split; reflexivity. Qed.

Lemma PlainVASReach_trans : forall d (system : PlainVAS d) x y z,
    PlainVASReach system x y -> PlainVASReach system y z -> PlainVASReach system x z.
Proof. intros d system x y z H; induction H; eauto using PlainVASReach. Qed.

Lemma targets_target_app : forall d source left right,
    @targets_target d source (left ++ right) =
    targets_target (targets_target source left) right.
Proof. intros d source left; revert source; induction left; intros; cbn; auto. Qed.

Lemma valid_targets_app : forall d (system : PlainVAS d) source left right,
    ValidVASTargets system source (left ++ right) <->
    ValidVASTargets system source left /\
    ValidVASTargets system (targets_target source left) right.
Proof.
  intros d system source left. revert source.
  induction left; intros; cbn; [tauto|rewrite IHleft; tauto].
Qed.

Definition VASRunConcat {d} (left right : VASRun d) : VASRun d :=
  {| RunSource := RunSource left; RunTargets := RunTargets left ++ RunTargets right |}.

Lemma vas_run_concat_valid : forall d (system : PlainVAS d) left right,
    ValidVASRun system left -> ValidVASRun system right ->
    RunTarget left = RunSource right -> ValidVASRun system (VASRunConcat left right).
Proof.
  intros d system [ls lt] [rs rt] Hl Hr Hc; cbn in *.
  apply valid_targets_app; split; [exact Hl|now rewrite Hc].
Qed.

Fixpoint ActionDisplacement {d} (word : list (ZVec d)) : ZVec d :=
  match word with [] => zvec_zero d | action :: tail =>
    zvec_add action (ActionDisplacement tail) end.

Lemma zvec_add_zero_right_run : forall d (value : ZVec d),
    zvec_add value (zvec_zero d) = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros i j Hij; subst j. unfold zvec_add, zvec_zero.
  rewrite (nth_map2 Z.add _ _ i i i eq_refl eq_refl), (const_nth Z 0 d i). lia.
Qed.

Lemma step_action_equation : forall d (source target : NVec d),
    nvec_to_zvec target = zvec_add (nvec_to_zvec source) (StepAction source target).
Proof.
  intros d source target. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros i j Hij; subst j. unfold StepAction, zvec_sub_run, zvec_add, nvec_to_zvec.
  rewrite (nth_map Z.of_nat target i i eq_refl),
    (nth_map2 Z.add _ _ i i i eq_refl eq_refl),
    (nth_map Z.of_nat source i i eq_refl),
    (nth_map2 Z.sub _ _ i i i eq_refl eq_refl),
    (nth_map Z.of_nat target i i eq_refl),
    (nth_map Z.of_nat source i i eq_refl). lia.
Qed.

Lemma step_equation_action : forall d (source target : NVec d) action,
    nvec_to_zvec target = zvec_add (nvec_to_zvec source) action ->
    action = StepAction source target.
Proof.
  intros d source target action Hequation.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Hindex; subst index'.
  pose proof (f_equal
    (fun value : ZVec d => Vector.nth value index) Hequation) as Hnth.
  unfold StepAction, zvec_sub_run, zvec_add, nvec_to_zvec in Hnth |- *.
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl) in Hnth |- *.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl) in Hnth.
  rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl). lia.
Qed.

Lemma plain_vas_step_iff : forall d (system : PlainVAS d) source action target,
    PlainVASStep system source action target <->
    List.In action system /\
    nvec_to_zvec target = zvec_add (nvec_to_zvec source) action.
Proof.
  intros d system source action target. unfold PlainVASStep. split.
  - intros [Hin ->]. split; [exact Hin|apply step_action_equation].
  - intros [Hin Hequation]. split; [exact Hin|].
    now apply step_equation_action.
Qed.

Lemma valid_targets_displacement : forall d (system : PlainVAS d) source targets,
    ValidVASTargets system source targets ->
    nvec_to_zvec (targets_target source targets) =
    zvec_add (nvec_to_zvec source)
      (ActionDisplacement (List.map fst (steps_of_targets source targets))).
Proof.
  intros d system source targets. revert source.
  induction targets as [|target tail IH]; intros source H; cbn in *.
  - symmetry; apply zvec_add_zero_right_run.
  - destruct H as [_ Htail].
    transitivity (zvec_add (nvec_to_zvec target)
      (ActionDisplacement (List.map fst (steps_of_targets target tail)))).
    + now apply IH.
    + rewrite (step_action_equation d source target).
      symmetry. apply zvec_add_assoc.
Qed.

Theorem valid_run_target_displacement : forall d (system : PlainVAS d) run,
    ValidVASRun system run ->
    nvec_to_zvec (RunTarget run) = zvec_add (nvec_to_zvec (RunSource run))
      (ActionDisplacement (RunActionWord run)).
Proof. intros d system [source targets]; apply valid_targets_displacement. Qed.

Lemma nvec_to_zvec_injective : forall d (left right : NVec d),
    nvec_to_zvec left = nvec_to_zvec right -> left = right.
Proof.
  intros d left right H.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros i j Hij; subst j.
  pose proof (f_equal (fun value : ZVec d => Vector.nth value i) H) as Hnth.
  unfold nvec_to_zvec in Hnth.
  repeat rewrite (nth_map Z.of_nat _ i i eq_refl) in Hnth. lia.
Qed.

Lemma step_action_deterministic : forall d source left right,
    @StepAction d source left = StepAction source right -> left = right.
Proof.
  intros d source left right H. apply nvec_to_zvec_injective.
  rewrite (step_action_equation d source left),
    (step_action_equation d source right), H. reflexivity.
Qed.

Lemma valid_targets_word_unique : forall d (system : PlainVAS d) source left right,
    ValidVASTargets system source left -> ValidVASTargets system source right ->
    List.map fst (steps_of_targets source left) =
      List.map fst (steps_of_targets source right) ->
    left = right.
Proof.
  intros d system source left. revert source.
  induction left as [|lh lt IH]; intros source right Hl Hr Hw;
    destruct right as [|rh rt]; cbn in *; try discriminate; auto.
  destruct Hl as [_ Hl], Hr as [_ Hr]. inversion Hw.
  assert (lh = rh) by (eapply step_action_deterministic; eauto).
  subst. f_equal. eapply IH; eauto.
Qed.

Theorem valid_run_source_word_unique : forall d (system : PlainVAS d)
    (left right : VASRun d),
    ValidVASRun system left -> ValidVASRun system right ->
    RunSource left = RunSource right -> RunActionWord left = RunActionWord right ->
    left = right.
Proof.
  intros d system [ls lt] [rs rt]; cbn. intros Hl Hr Hs Hw. subst.
  f_equal. eapply valid_targets_word_unique; eauto.
Qed.

Definition ShiftVASRun {d} (offset : NVec d) (run : VASRun d) : VASRun d :=
  {| RunSource := nvec_add (RunSource run) offset;
     RunTargets := List.map (fun target => nvec_add target offset) (RunTargets run) |}.

Lemma step_action_shift : forall d source target offset,
    @StepAction d (nvec_add source offset) (nvec_add target offset) = StepAction source target.
Proof.
  intros d source target offset.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros i j Hij; subst j.
  unfold StepAction, zvec_sub_run, nvec_to_zvec, nvec_add.
  repeat rewrite (nth_map2 Z.sub _ _ i i i eq_refl eq_refl).
  repeat rewrite (nth_map Z.of_nat _ i i eq_refl).
  repeat rewrite (nth_map2 Nat.add _ _ i i i eq_refl eq_refl). lia.
Qed.

Lemma shift_targets_valid : forall d (system : PlainVAS d) source targets offset,
    ValidVASTargets system source targets ->
    ValidVASTargets system (nvec_add source offset)
      (List.map (fun target => nvec_add target offset) targets).
Proof.
  intros d system source targets. revert source.
  induction targets as [|target tail IH]; intros source offset H.
  - reflexivity.
  - change (List.In (StepAction source target) system /\
      ValidVASTargets system target tail) in H.
    change (List.In (StepAction (nvec_add source offset)
        (nvec_add target offset)) system /\
      ValidVASTargets system (nvec_add target offset)
        (List.map (fun value => nvec_add value offset) tail)).
    destruct H as [Hin Htail]. rewrite step_action_shift. split; auto.
Qed.

Lemma shift_targets_target : forall (d : nat) (source : NVec d)
    (targets : list (NVec d)) (offset : NVec d),
    targets_target (nvec_add source offset)
      (List.map (fun target => nvec_add target offset) targets) =
    nvec_add (targets_target source targets) offset.
Proof. intros d source targets; revert source; induction targets; cbn; auto. Qed.

Lemma steps_of_targets_shift_actions : forall (d : nat) (source : NVec d)
    (targets : list (NVec d)) (offset : NVec d),
    List.map fst
      (steps_of_targets (nvec_add source offset)
        (List.map (fun target => nvec_add target offset) targets)) =
    List.map fst (steps_of_targets source targets).
Proof.
  intros d source targets. revert source.
  induction targets as [|target tail IH]; intros source offset.
  - reflexivity.
  - change (StepAction (nvec_add source offset) (nvec_add target offset) ::
      List.map fst
        (steps_of_targets (nvec_add target offset)
          (List.map (fun value => nvec_add value offset) tail)) =
      StepAction source target :: List.map fst (steps_of_targets target tail)).
    rewrite step_action_shift, IH. reflexivity.
Qed.

Lemma shift_run_action_word : forall d offset (run : VASRun d),
    RunActionWord (ShiftVASRun offset run) = RunActionWord run.
Proof.
  intros d offset [source targets]. apply steps_of_targets_shift_actions.
Qed.

Lemma shift_run_endpoints : forall d offset (run : VASRun d),
    RunSource (ShiftVASRun offset run) = nvec_add (RunSource run) offset /\
    RunTarget (ShiftVASRun offset run) = nvec_add (RunTarget run) offset.
Proof.
  intros d offset [source targets]; split; [reflexivity|cbn; apply shift_targets_target].
Qed.

Theorem vas_run_shift_valid : forall d (system : PlainVAS d) run offset,
    ValidVASRun system run -> ValidVASRun system (ShiftVASRun offset run).
Proof. intros d system [source targets]; apply shift_targets_valid. Qed.

Theorem vas_reach_monotone : forall d (system : PlainVAS d) source target offset,
    PlainVASReach system source target ->
    PlainVASReach system (nvec_add source offset) (nvec_add target offset).
Proof.
  intros d system source target offset H.
  apply vas_reach_run_iff in H. destruct H as [run [Hv [Hs Ht]]].
  apply vas_reach_run_iff. exists (ShiftVASRun offset run). split.
  - now apply vas_run_shift_valid.
  - destruct (shift_run_endpoints d offset run) as [Hs' Ht'].
    split; [now rewrite Hs', Hs|now rewrite Ht', Ht].
Qed.
