From Coq Require Import List Vector.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Contexts OneSourceReduction.
From Mell.Semilinear Require Import Presentation Closure LinearEquations.
From Mell.VAS Require Import Intraproductions AlmostSemilinearProjection.
From Mell.WSVAS Require Import System Runs WitnessAlphabet BVASSimulation
  SafeLinearization.

Import ListNotations.

Definition IBVASInductiveInvariant {d} (S : IBVAS d)
    (set : NVec d -> Prop) : Prop :=
  (forall value, List.In value (initial_vectors S) -> set value) /\
  forall action children target,
    List.In action (system_actions S) ->
    List.Forall set children ->
    apply_action action children = Some target ->
    set target.

Section InductiveClosure.
Context {d : nat} (S : IBVAS d) (set : NVec d -> Prop).

Lemma inductive_invariant_free_runs :
  IBVASInductiveInvariant S set ->
  (forall run, ValidFreeIRun S run ->
      List.Forall set (free_irun_sources run) -> set (irun_target run)) /\
  (forall runs, ValidFreeIRuns S runs ->
      List.Forall set (free_iruns_sources runs) ->
      List.Forall set (iruns_targets runs)).
Proof.
  intros [_ Haction]. apply ValidFreeIRun_IRuns_ind; intros.
  - inversion H; subst. assumption.
  - apply Haction with (action := action) (children := iruns_targets children).
    + exact i.
    + apply H. exact H0.
    + exact e.
  - constructor.
  - cbn in H1. apply List.Forall_app in H1 as [Hrun Htail].
    constructor; [now apply H|now apply H0].
Qed.
Lemma inductive_invariant_closed_free_runs :
  IBVASInductiveInvariant S set -> ClosedUnderFreeRuns S set.
Proof.
  intro Hinvariant. intros run Hvalid Hall.
  exact ((proj1 (inductive_invariant_free_runs Hinvariant)) run Hvalid Hall).
Qed.

End InductiveClosure.

Lemma ws_step_star_has_run : forall d (system : WSVAS d) source target,
  WSVASStepStar system source target ->
  exists run : WSRun system,
    ValidWSRun run /\ ws_source run = source /\ ws_target run = target.
Proof.
  intros d system source target Hstar. induction Hstar.
  - exists (empty_ws_run source). repeat split; reflexivity.
  - destruct H as [transition Htransition].
    destruct IHHstar as [[tail_source tail_steps] [Hvalid [Hsource Htarget]]].
    cbn in Hsource. subst tail_source.
    exists {| WSRunSource := source;
      WSRunTargets := (transition, middle) :: tail_steps |}.
    cbn. repeat split; auto.
Qed.

Lemma reach_wsvas_from_set_iff_star : forall d (system : WSVAS d)
    (sources targets : NVec d -> Prop),
  ReachWSVASFromSet system sources targets <->
  forall target, (exists source,
      sources source /\ WSVASStepStar system source target) -> targets target.
Proof.
  intros d system sources targets. split.
  - intros Hreach target [source [Hsource Hstar]].
    destruct (ws_step_star_has_run d system source target Hstar)
      as [run [Hvalid [Hrun_source Hrun_target]]].
    rewrite <- Hrun_target. apply Hreach with (run := run); auto.
    now rewrite Hrun_source.
  - intros Hstar run Hvalid Hsource. apply Hstar.
    exists (ws_source run). split; [exact Hsource|].
    now apply valid_ws_run_step_star.
Qed.

Lemma simulation_invariant_extensional : forall d (S : IBVAS d)
    (A : NVec d -> Prop) code,
  (forall value, A value <-> denote code value) ->
  forall value,
    (A value \/ Reach S value) <-> SimulationInvariant S code value.
Proof.
  intros d S A code Hcode value. unfold SimulationInvariant.
  rewrite <- Hcode. tauto.
Qed.

Lemma closed_under_free_runs_extensional : forall d (S : IBVAS d)
    (left right : NVec d -> Prop),
  (forall value, left value <-> right value) ->
  ClosedUnderFreeRuns S left -> ClosedUnderFreeRuns S right.
Proof.
  intros d S left right Heq Hclosed run Hvalid Hall.
  apply (proj1 (Heq _)), Hclosed with (run := run); [exact Hvalid|].
  eapply List.Forall_impl; [|exact Hall]. intros value Hvalue.
  exact (proj2 (Heq _) Hvalue).
Qed.

Lemma source_shuffle_extensional : forall d
    (X left right : NVec d -> Prop) word,
  (forall value, left value <-> right value) ->
  SourceShuffle X left word -> SourceShuffle X right word.
Proof.
  intros d X left right word Heq
    [prefix [special [suffix [Hword [HX [Hprefix Hsuffix]]]]]].
  exists prefix, special, suffix. repeat split; auto.
  - eapply List.Forall_impl; [|exact Hprefix].
    intros value Hvalue. exact (proj1 (Heq _) Hvalue).
  - eapply List.Forall_impl; [|exact Hsuffix].
    intros value Hvalue. exact (proj1 (Heq _) Hvalue).
Qed.

Lemma reach_from_shuffle_extensional : forall d (S : IBVAS d)
    (X left right : NVec d -> Prop) target,
  (forall value, left value <-> right value) ->
  ReachFromShuffle S X left target -> ReachFromShuffle S X right target.
Proof.
  intros d S X left right target Heq
    [run [Hvalid [Htarget Hshuffle]]].
  exists run. repeat split; auto.
  now apply source_shuffle_extensional with (left := left).
Qed.

Lemma translated_closed_linearization_stable : forall d
    (base : NVec d) (period : NVec d -> Prop),
  PeriodicNSet period ->
  NSetStable (NSetTranslate base (ClosedLinearizationN period))
    (ClosedLinearizationN period).
Proof.
  intros d base period Hperiod value offset [first [Hfirst ->]] Hoffset.
  exists (nvec_add first offset). split.
  - now apply (proj2 (closed_linearization_n_periodic d period Hperiod)).
  - rewrite nvec_add_assoc_local. reflexivity.
Qed.

Theorem lemma_5_1_bvas_safe_linearization : forall d (S : IBVAS d)
    (A target period : NVec d -> Prop) (base : NVec d),
  IBVASInductiveInvariant S (fun value => A value \/ Reach S value) ->
  Semilinear A ->
  Semilinear target ->
  PeriodicNSet period ->
  AsymptoticallyDefinableNSet period ->
  (forall value,
    ReachFromShuffle S (NSetTranslate base period)
      (fun x => A x \/ Reach S x) value -> target value) ->
  (forall value, target value ->
    NSetMinkowskiN (fun x => A x \/ Reach S x)
      (ClosedLinearizationN period) value) ->
  exists offset,
    period offset /\
    forall value,
      ReachFromNonemptyShuffle S
        (NSetTranslate (nvec_add base offset)
          (ClosedLinearizationN period))
        (fun x => A x \/ Reach S x) value ->
      target value.
Proof.
  intros d S A target period base Hinvariant HA Htarget Hperiod Hasymptotic
    Hsafe Htarget_bound.
  destruct HA as [code Hcode].
  set (I := fun value => A value \/ Reach S value).
  set (J := SimulationInvariant S code).
  assert (HIJ : forall value, I value <-> J value).
  { intro value. unfold I, J. now apply simulation_invariant_extensional. }
  assert (HIclosed : ClosedUnderFreeRuns S I).
  { unfold I. now apply inductive_invariant_closed_free_runs. }
  assert (HJclosed : ClosedUnderFreeRuns S J).
  { now apply closed_under_free_runs_extensional with (left := I). }
  assert (Hws_safe : ReachWSVASFromSet (concrete_wsvas S code)
      (NSetTranslate base period) target).
  { apply (proj2 (reach_wsvas_from_set_iff_star d
      (concrete_wsvas S code) (NSetTranslate base period) target)).
    intros value [source [Hsource Hstar]]. apply Hsafe.
    apply reach_from_shuffle_extensional with (left := J).
    - intro x. symmetry. apply HIJ.
    apply (proj2 (lemma_5_5_bvas_wsvas_reach_iff S code
      (NSetTranslate base period) value HJclosed)).
    exists source. split; assumption. }
  destruct (lemma_5_4_wsvas_safe_linearization (concrete_wsvas S code)
    base period target Hperiod Hasymptotic Htarget Hws_safe)
    as [offset [Hoffset Hws_linear]].
  exists offset. split; [exact Hoffset|].
  set (linear_source := NSetTranslate (nvec_add base offset)
    (ClosedLinearizationN period)).
  assert (Hlinear_safe : forall value,
      ReachFromShuffle S linear_source I value -> target value).
  { intros value Hreach.
    assert (HreachJ : ReachFromShuffle S linear_source J value).
    { apply reach_from_shuffle_extensional with (left := I); assumption. }
    destruct (proj1 (lemma_5_5_bvas_wsvas_reach_iff S code
      linear_source value HJclosed) HreachJ) as [source [Hsource Hstar]].
    destruct (ws_step_star_has_run d (concrete_wsvas S code)
      source value Hstar) as [run [Hvalid [Hrun_source Hrun_target]]].
    rewrite <- Hrun_target. apply Hws_linear with (run := run); [exact Hvalid|].
    now rewrite Hrun_source. }
  intros value Hnonempty. apply Hlinear_safe.
  apply (proj2 (lemma_5_7_one_source_reduction d S I
    (ClosedLinearizationN period) linear_source HIclosed
    (closed_linearization_n_periodic d period Hperiod)
    (translated_closed_linearization_stable d
      (nvec_add base offset) period Hperiod)
    (fun reached Hreached => Htarget_bound reached (Hlinear_safe reached Hreached))
    value)).
  exact Hnonempty.
Qed.
