From Coq Require Import Classical_Prop List Sorting.Permutation.
From KruskalTrees Require Import idx.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Contexts RunOrder RunOrderAntisymmetry
  RunLeafOperations LanguageFlattening OneSourceReduction.
From Mell.Geometry Require Import ClosedLinearization ClosedLinearizationL2
  FaceStrippingLemma610 QratHomogeneousAdapter RationalClosure.
From Mell.Geometry Require Export ClosedLinearizationFinite.
From Mell.Order Require Import PeriodicOrder.
From Mell.Order Require Import FiniteBasis.
From Mell.Semilinear Require Import Closure.
From Mell.Separator Require Import Attractor DirectedRuns SafetyWitness RankDecrease
  WitnessUpdate.
From Mell.WSVAS Require Import System Runs WitnessAlphabet.

Import ListNotations.
Import idx_notations.

(** Paper Lemma 5.6 is a one-step statement.  In particular it has no
    closure hypothesis on [A \/ Reach system]. *)
Definition BVASSideStepWithSet {d} (system : IBVAS d)
    (side : NSet d) (source target : NVec d) : Prop :=
  exists (rule_index : idx (length (system_actions system)))
    (side_values : list (NVec d)),
    length side_values =
      Nat.pred (action_arity (nth_idx (system_actions system) rule_index)) /\
    List.Forall side side_values /\
    apply_action (nth_idx (system_actions system) rule_index)
      (source :: side_values) = Some target.

Theorem lemma_5_6_paper_wsvas_exists : forall d (system : IBVAS d)
    (A : NSet d),
  Semilinear A ->
  exists machine : WSVAS d,
    forall source target,
      WSVASStep machine source target <->
      BVASSideStepWithSet system
        (fun value => A value \/ Reach system value) source target.
Proof.
  intros d system A [code Hcode].
  exists (concrete_wsvas system code). intros source target.
  rewrite <- (lemma_5_6_bvas_wsvas_step_iff system code source target).
  unfold BVASSideStep, BVASSideStepWithSet, action_at. split.
  - intros [index [values [Hlength [Hall Happly]]]].
    exists index, values. repeat split; try assumption.
    eapply List.Forall_impl; [|exact Hall].
    intros value [Hreach|Hdenote]; [now right|left].
    exact (proj2 (Hcode value) Hdenote).
  - intros [index [values [Hlength [Hall Happly]]]].
    exists index, values. repeat split; try assumption.
    eapply List.Forall_impl; [|exact Hall].
    intros value [HA|Hreach]; [right|now left].
    exact (proj1 (Hcode value) HA).
Qed.

Definition paper_lemma_5_6_bvas_wsvas_exists :=
  lemma_5_6_paper_wsvas_exists.

(** The paper's initial-side formulation of attractors. *)
Definition PaperAttractor {d} (system : IBVAS d) (set : NSet d) : Prop :=
  forall target,
    ReachFromNonemptyShuffle system set (InitialNSet system) target ->
    set target.

Theorem paper_attractor_iff_reachable_side : forall d
    (system : IBVAS d) (set : NSet d),
  PaperAttractor system set <-> Attractor system set.
Proof.
  intros d system set. split.
  - intros Hpaper target
      [run [Hvalid [Htarget Hsources]]].
    destruct (flatten_reachable_side_sources system set run Hvalid Hsources)
      as [flattened [Hflattened [Hflattened_target Hflattened_sources]]].
    apply Hpaper. exists flattened. split; [exact Hflattened|]. split.
    + now rewrite Hflattened_target, Htarget.
    + exact Hflattened_sources.
  - intros Hinternal target Hreach.
    eapply attractor_initial_form; eauto.
Qed.

Definition paper_attractor_iff_attractor :=
  paper_attractor_iff_reachable_side.

Record PaperSafetyWitness {d} (system : IBVAS d) (safe : NSet d) : Type := {
  paper_witness_safe_semilinear : Semilinear safe;
  paper_witness_reach_safe : forall value, Reach system value -> safe value;
  paper_witness_attractor : NSet d;
  paper_witness_attractor_semilinear : Semilinear paper_witness_attractor;
  paper_witness_attractor_closed :
    PaperAttractor system paper_witness_attractor;
  paper_witness_attractor_safe : forall value,
    paper_witness_attractor value -> safe value;
  paper_witness_nodes : list (DirectedIRun system);
  paper_witness_nodes_homogeneous :
    HomogeneousWitnessNodes paper_witness_nodes;
  paper_witness_run_coverage : forall run,
    ValidIRun system run ->
    paper_witness_attractor (irun_target run) \/
    exists node,
      List.In node paper_witness_nodes /\ DirectedRunMember node run
}.

Arguments paper_witness_attractor {d system safe} _ _.
Arguments paper_witness_nodes {d system safe} _.

Definition paper_safety_witness_to_internal {d} {system : IBVAS d} {safe}
    (witness : PaperSafetyWitness system safe) : SafetyWitness system safe.
Proof.
  destruct witness as [Hsafe_semilinear Hreach attractor
    Hattractor_semilinear Hattractor Hattractor_safe nodes
    Hhomogeneous Hcoverage].
  refine {| witness_safe_semilinear := Hsafe_semilinear;
    witness_reach_safe := Hreach;
    witness_attractor := attractor;
    witness_attractor_semilinear := Hattractor_semilinear;
    witness_attractor_safe := Hattractor_safe;
    witness_nodes := nodes;
    witness_nodes_homogeneous := Hhomogeneous;
    witness_run_coverage := Hcoverage |}.
  apply (proj1 (paper_attractor_iff_reachable_side d system
    attractor)). exact Hattractor.
Defined.

Lemma paper_to_internal_nodes : forall d (system : IBVAS d) safe
    (witness : PaperSafetyWitness system safe),
  witness_nodes (paper_safety_witness_to_internal witness) =
    paper_witness_nodes witness.
Proof. intros d system safe []; reflexivity. Qed.

Definition internal_safety_witness_to_paper {d} {system : IBVAS d} {safe}
    (witness : SafetyWitness system safe) : PaperSafetyWitness system safe.
Proof.
  destruct witness as [Hsafe_semilinear Hreach attractor
    Hattractor_semilinear Hattractor Hattractor_safe nodes
    Hhomogeneous Hcoverage].
  refine {| paper_witness_safe_semilinear := Hsafe_semilinear;
    paper_witness_reach_safe := Hreach;
    paper_witness_attractor := attractor;
    paper_witness_attractor_semilinear := Hattractor_semilinear;
    paper_witness_attractor_safe := Hattractor_safe;
    paper_witness_nodes := nodes;
    paper_witness_nodes_homogeneous := Hhomogeneous;
    paper_witness_run_coverage := Hcoverage |}.
  apply (proj2 (paper_attractor_iff_reachable_side d system
    attractor)). exact Hattractor.
Defined.

Lemma internal_to_paper_nodes : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe),
  paper_witness_nodes (internal_safety_witness_to_paper witness) =
    witness_nodes witness.
Proof. intros d system safe []; reflexivity. Qed.

Theorem lemma_7_1_paper_safety_witness_rank_descent : forall d
    (system : IBVAS d) (safe : NSet d)
    (witness : PaperSafetyWitness system safe),
  paper_witness_nodes witness <> [] ->
  exists next : PaperSafetyWitness system safe,
    WitnessRankLess (paper_witness_nodes next) (paper_witness_nodes witness).
Proof.
  intros d system safe witness Hnonempty.
  assert (Hinternal_nonempty :
      witness_nodes (paper_safety_witness_to_internal witness) <> []).
  { now rewrite paper_to_internal_nodes. }
  destruct (lemma_7_1_safety_witness_rank_descent d system safe
    (paper_safety_witness_to_internal witness) Hinternal_nonempty)
    as [next Hnext].
  exists (internal_safety_witness_to_paper next).
  rewrite internal_to_paper_nodes, <- paper_to_internal_nodes. exact Hnext.
Qed.

Definition paper_lemma_7_1_safety_witness_rank_descent :=
  lemma_7_1_paper_safety_witness_rank_descent.
