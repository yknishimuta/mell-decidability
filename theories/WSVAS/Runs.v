From Coq Require Import List Vector Lia.
From Mell.Core Require Import Vector.
From Mell.VAS Require Import Runs.
From Mell.WSVAS Require Import System.

Import ListNotations.

Record WSRun {d} (system : WSVAS d) : Type := {
  WSRunSource : NVec d;
  WSRunTargets : list (ws_transition system * NVec d)
}.

Arguments WSRunSource {d system} _.
Arguments WSRunTargets {d system} _.

Fixpoint ws_targets_target {d} {system : WSVAS d}
    (source : NVec d) (steps : list (ws_transition system * NVec d)) : NVec d :=
  match steps with
  | [] => source
  | (_, target) :: tail => ws_targets_target target tail
  end.

Definition ws_source {d} {system : WSVAS d} (run : WSRun system) : NVec d :=
  WSRunSource run.

Definition ws_target {d} {system : WSVAS d} (run : WSRun system) : NVec d :=
  ws_targets_target (WSRunSource run) (WSRunTargets run).

Definition ws_direction {d} {system : WSVAS d} (run : WSRun system) :=
  (ws_source run, ws_target run).

Definition ws_run_length {d} {system : WSVAS d} (run : WSRun system) : nat :=
  length (WSRunTargets run).

Fixpoint ValidWSTargets {d} {system : WSVAS d} (source : NVec d)
    (steps : list (ws_transition system * NVec d)) : Prop :=
  match steps with
  | [] => True
  | (transition, target) :: tail =>
      ws_transition_action system transition = StepAction source target /\
      ValidWSTargets target tail
  end.

Definition ValidWSRun {d} {system : WSVAS d} (run : WSRun system) : Prop :=
  ValidWSTargets (WSRunSource run) (WSRunTargets run).

Definition empty_ws_run {d} {system : WSVAS d} (source : NVec d) : WSRun system :=
  {| WSRunSource := source; WSRunTargets := [] |}.

Lemma valid_ws_run_empty : forall d (system : WSVAS d) source,
    ValidWSRun (empty_ws_run (system := system) source).
Proof. reflexivity. Qed.

Definition WSVASStep {d} (system : WSVAS d) (source target : NVec d) : Prop :=
  exists transition,
    ws_transition_action system transition = StepAction source target.

Inductive WSVASStepStar {d} (system : WSVAS d) : NVec d -> NVec d -> Prop :=
| ws_step_star_refl : forall source, WSVASStepStar system source source
| ws_step_star_step : forall source middle target,
    WSVASStep system source middle ->
    WSVASStepStar system middle target ->
    WSVASStepStar system source target.

Lemma ws_targets_target_app : forall d (system : WSVAS d) source left right,
    ws_targets_target source (left ++ right) =
    ws_targets_target (system := system) (ws_targets_target source left) right.
Proof. intros d system source left; revert source; induction left as [|[]]; intros; cbn; auto. Qed.

Lemma valid_ws_targets_app : forall d (system : WSVAS d) source left right,
    ValidWSTargets source (left ++ right) <->
    ValidWSTargets (system := system) source left /\
    ValidWSTargets (ws_targets_target source left) right.
Proof.
  intros d system source left; revert source.
  induction left as [|[transition target] tail IH]; intros source right; cbn.
  - tauto.
  - rewrite IH. tauto.
Qed.

Definition ws_run_concat {d} {system : WSVAS d}
    (left right : WSRun system) : WSRun system :=
  {| WSRunSource := WSRunSource left;
     WSRunTargets := WSRunTargets left ++ WSRunTargets right |}.

Lemma ws_run_concat_source : forall d (system : WSVAS d)
    (left right : WSRun system),
    ws_source (ws_run_concat left right) = ws_source left.
Proof. reflexivity. Qed.

Lemma ws_run_concat_target : forall d (system : WSVAS d)
    (left right : WSRun system),
    ws_target left = ws_source right ->
    ws_target (ws_run_concat left right) = ws_target right.
Proof.
  intros d system [ls lt] [rs rt] H; cbn in *.
  rewrite ws_targets_target_app, H. reflexivity.
Qed.

Lemma valid_ws_run_concat : forall d (system : WSVAS d)
    (left right : WSRun system),
    ValidWSRun left -> ValidWSRun right ->
    ws_target left = ws_source right ->
    ValidWSRun (ws_run_concat left right).
Proof.
  intros d system [ls lt] [rs rt] Hl Hr Hboundary; cbn in *.
  apply valid_ws_targets_app. split; [exact Hl|].
  now rewrite Hboundary.
Qed.

Definition shift_ws_steps {d} {system : WSVAS d} (offset : NVec d)
    (steps : list (ws_transition system * NVec d)) :=
  List.map (fun '(transition, target) =>
    (transition, nvec_add target offset)) steps.

Definition ws_run_shift {d} {system : WSVAS d} (offset : NVec d)
    (run : WSRun system) : WSRun system :=
  {| WSRunSource := nvec_add (WSRunSource run) offset;
     WSRunTargets := shift_ws_steps offset (WSRunTargets run) |}.

Lemma ws_targets_target_shift : forall d (system : WSVAS d)
    (offset source : NVec d)
    (steps : list (ws_transition system * NVec d)),
    ws_targets_target (nvec_add source offset) (shift_ws_steps offset steps) =
    nvec_add (ws_targets_target (system := system) source steps) offset.
Proof.
  intros d system offset source steps. revert source.
  induction steps as [|[transition target] tail IH]; intros source; cbn; auto.
Qed.

Lemma valid_ws_targets_shift : forall d (system : WSVAS d)
    (offset source : NVec d)
    (steps : list (ws_transition system * NVec d)),
    ValidWSTargets source steps ->
    ValidWSTargets (nvec_add source offset) (shift_ws_steps offset steps).
Proof.
  intros d system offset source steps. revert source.
  induction steps as [|[transition target] tail IH]; intros source Hvalid; cbn in *.
  - exact I.
  - destruct Hvalid as [Haction Htail]. split.
    + rewrite Haction. symmetry. apply step_action_shift.
    + now apply IH.
Qed.

Lemma valid_ws_run_shift : forall d (system : WSVAS d) offset
    (run : WSRun system),
    ValidWSRun run -> ValidWSRun (ws_run_shift offset run).
Proof. intros d system offset [source steps]; apply valid_ws_targets_shift. Qed.

Lemma ws_run_shift_source : forall d (system : WSVAS d) offset
    (run : WSRun system),
    ws_source (ws_run_shift offset run) = nvec_add (ws_source run) offset.
Proof. reflexivity. Qed.

Lemma ws_run_shift_target : forall d (system : WSVAS d) offset
    (run : WSRun system),
    ws_target (ws_run_shift offset run) = nvec_add (ws_target run) offset.
Proof. intros d system offset [source steps]; apply ws_targets_target_shift. Qed.

Lemma ws_run_shift_length : forall d (system : WSVAS d) offset
    (run : WSRun system),
    ws_run_length (ws_run_shift offset run) = ws_run_length run.
Proof. intros d system offset [source steps]; unfold ws_run_length, ws_run_shift, shift_ws_steps; cbn; now rewrite map_length. Qed.

Lemma valid_ws_run_step_star : forall d (system : WSVAS d)
    (run : WSRun system),
    ValidWSRun run -> WSVASStepStar system (ws_source run) (ws_target run).
Proof.
  intros d system [source steps]. cbn. revert source.
  induction steps as [|[transition target] tail IH]; intros source Hvalid; cbn in *.
  - constructor.
  - destruct Hvalid as [Haction Htail]. econstructor.
    + exists transition. exact Haction.
    + now apply IH.
Qed.
