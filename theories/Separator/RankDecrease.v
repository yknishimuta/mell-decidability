From Coq Require Import Arith Lia List Relation_Operators Wellfounded.
From mathcomp Require Import all_ssreflect all_algebra.
From Mell.BVAS Require Import System.
From Mell.Geometry Require Import FaceDimension QcLinearAlgebra.
From Mell.Separator Require Import DirectedRuns SafetyWitness.

Import ListNotations QcMathComp.

Definition directed_irun_rank {d} {system : IBVAS d}
    (node : DirectedIRun system) : nat :=
  \dim <<qrow_generators (directed_generators node)>>%VS.

Lemma directed_irun_rank_span : forall d (system : IBVAS d)
    (node : DirectedIRun system),
  SpanDimension (DirectedCone node) (directed_irun_rank node).
Proof.
  intros d system node. exists (directed_generators node). split.
  - apply qcone_span_presentation.
  - reflexivity.
Qed.

Lemma directed_irun_rank_le_dimension : forall d (system : IBVAS d)
    (node : DirectedIRun system),
  Nat.le (directed_irun_rank node) d.
Proof.
  intros d system node. unfold directed_irun_rank.
  pose proof (dimvS (subvf
    <<qrow_generators (directed_generators node)>>%VS)) as Hdimension.
  rewrite dimvf in Hdimension. cbn in Hdimension.
  pose proof (elimT leP Hdimension) as Hle. lia.
Qed.

Fixpoint RankTuple (dimension : nat) : Type :=
  match dimension with
  | 0 => nat
  | S smaller => (nat * RankTuple smaller)%type
  end.

Fixpoint high_rank_less (dimension : nat) :
    RankTuple dimension -> RankTuple dimension -> Prop :=
  match dimension return RankTuple dimension -> RankTuple dimension -> Prop with
  | 0 => Nat.lt
  | S smaller => slexprod nat (RankTuple smaller) Nat.lt
      (high_rank_less smaller)
  end.

Theorem high_rank_less_well_founded : forall dimension,
  well_founded (high_rank_less dimension).
Proof.
  induction dimension as [|dimension IH]; cbn.
  - apply lt_wf.
  - apply wf_slexprod; [apply lt_wf|exact IH].
Qed.

Definition nodes_at_rank {d} {system : IBVAS d}
    (rank : nat) (nodes : list (DirectedIRun system)) : nat :=
  count_occ Nat.eq_dec (List.map directed_irun_rank nodes) rank.

Fixpoint witness_rank_tuple {d} {system : IBVAS d}
    (dimension : nat) (nodes : list (DirectedIRun system)) :
    RankTuple dimension :=
  match dimension return RankTuple dimension with
  | 0 => nodes_at_rank 0 nodes
  | S smaller => (nodes_at_rank (S smaller) nodes,
      witness_rank_tuple smaller nodes)
  end.

Definition WitnessRankLess {d} {system : IBVAS d}
    (next previous : list (DirectedIRun system)) : Prop :=
  high_rank_less d (witness_rank_tuple d next)
    (witness_rank_tuple d previous).

Theorem witness_rank_less_well_founded : forall d (system : IBVAS d),
  well_founded (@WitnessRankLess d system).
Proof.
  intros d system. unfold WitnessRankLess.
  apply (wf_inverse_image (list (DirectedIRun system)) (RankTuple d)
    (high_rank_less d) (witness_rank_tuple d)).
  apply high_rank_less_well_founded.
Qed.

Lemma nodes_at_rank_app : forall d (system : IBVAS d) rank
    (left right : list (DirectedIRun system)),
  nodes_at_rank rank (left ++ right) =
    nodes_at_rank rank left + nodes_at_rank rank right.
Proof.
  intros d system rank left right. unfold nodes_at_rank.
  rewrite List.map_app. apply count_occ_app.
Qed.

Lemma nodes_at_rank_cons_same : forall d (system : IBVAS d)
    (node : DirectedIRun system) (tail : list (DirectedIRun system)),
  nodes_at_rank (directed_irun_rank node) (node :: tail) =
    S (nodes_at_rank (directed_irun_rank node) tail).
Proof.
  intros. unfold nodes_at_rank. cbn.
  destruct (Nat.eq_dec (directed_irun_rank node) (directed_irun_rank node));
    [lia|contradiction].
Qed.
