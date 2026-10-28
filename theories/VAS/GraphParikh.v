From Coq Require Import Arith Fin Lia List Vector ZArith Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import Code.
From Mell.VAS Require Import Runs Intraproductions ProductionGraph
  ProductionGraphPaths.

Import ListNotations.

Definition production_graph_edge_eq_dec {d} :
    forall left right : ProductionGraphEdge d, {left = right} + {left <> right}.
Proof.
  intros [ls la lt] [rs ra rt].
  destruct (nvec_eq_dec ls rs) as [->|H]; [|right; congruence].
  destruct (zvec_eq_dec la ra) as [->|H]; [|right; congruence].
  destruct (nvec_eq_dec lt rt) as [->|H]; [left; reflexivity|right; congruence].
Defined.

Inductive GraphEdgeTrace {d} :
    NVec d -> NVec d -> list (ProductionGraphEdge d) -> Prop :=
| graph_edge_trace_nil : forall state,
    GraphEdgeTrace state state []
| graph_edge_trace_cons : forall edge target tail,
    GraphEdgeTrace (RunEdgeTarget edge) target tail ->
    GraphEdgeTrace (RunEdgeSource edge) target (edge :: tail).

Definition ProductionGraphEdgeTrace {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness : NVec d)
    (source target : NVec d) (trace : list (ProductionGraphEdge d)) : Prop :=
  GraphEdgeTrace source target trace /\
  List.Forall (fun edge => ProductionGraphTransition system gamma witness
    (RunEdgeSource edge) (RunEdgeAction edge) (RunEdgeTarget edge)) trace.

Definition GraphEdgeParikh {d} (trace : list (ProductionGraphEdge d))
    (edge : ProductionGraphEdge d) : nat :=
  count_occ production_graph_edge_eq_dec trace edge.

Definition GraphCycle {d} (trace : list (ProductionGraphEdge d))
    (root : NVec d) : Prop := GraphEdgeTrace root root trace.

Definition TotalGraphCycle {d} (graph trace : list (ProductionGraphEdge d)) : Prop :=
  forall edge, List.In edge graph -> (0 < GraphEdgeParikh trace edge)%nat.

Definition GraphTraceActionWord {d} (trace : list (ProductionGraphEdge d)) :=
  List.map RunEdgeAction trace.

Lemma graph_edge_trace_singleton : forall d (edge : ProductionGraphEdge d),
    GraphEdgeTrace (RunEdgeSource edge) (RunEdgeTarget edge) [edge].
Proof. intros; constructor; constructor. Qed.

Lemma graph_edge_trace_append : forall d source middle target left right,
    @GraphEdgeTrace d source middle left ->
    GraphEdgeTrace middle target right ->
    GraphEdgeTrace source target (left ++ right).
Proof.
  intros d source middle target left right Hleft.
  induction Hleft; intro Hright; cbn; [exact Hright|constructor; auto].
Qed.

Lemma graph_edge_trace_split : forall d source target left right,
    @GraphEdgeTrace d source target (left ++ right) ->
    exists middle, GraphEdgeTrace source middle left /\
      GraphEdgeTrace middle target right.
Proof.
  intros d source target left. revert source.
  induction left as [|edge tail IH]; intros source right Htrace.
  - cbn in Htrace. exists source; split; [constructor|assumption].
  - cbn in Htrace. inversion Htrace; subst.
    destruct (IH _ _ H2) as [middle [Hleft Hright]].
    exists middle; split; [constructor; exact Hleft|exact Hright].
Qed.

Lemma production_graph_edge_trace_append : forall d system gamma witness
    source middle target left right,
    @ProductionGraphEdgeTrace d system gamma witness source middle left ->
    ProductionGraphEdgeTrace system gamma witness middle target right ->
    ProductionGraphEdgeTrace system gamma witness source target (left ++ right).
Proof.
  intros d system gamma witness source middle target left right
    [Hleft HFleft] [Hright HFright]. split.
  - eapply graph_edge_trace_append; eauto.
  - apply List.Forall_app; split; assumption.
Qed.

Lemma production_graph_edge_trace_to_path : forall d system gamma witness
    source target trace,
    @ProductionGraphEdgeTrace d system gamma witness source target trace ->
    ProductionGraphPath system gamma witness source target
      (GraphTraceActionWord trace).
Proof.
  intros d system gamma witness source target trace [Htrace Hall].
  induction Htrace; cbn in *; [constructor|].
  inversion Hall; subst. econstructor; eauto.
Qed.

Lemma production_graph_path_has_edge_trace : forall d system gamma witness
    source target word,
    @ProductionGraphPath d system gamma witness source target word ->
    exists trace,
      ProductionGraphEdgeTrace system gamma witness source target trace /\
      GraphTraceActionWord trace = word.
Proof.
  intros d system gamma witness source target word Hpath.
  induction Hpath.
  - exists []; repeat split; constructor.
  - destruct IHHpath as [trace [[Htrace Hall] Hword]].
    set (edge := {| RunEdgeSource := source; RunEdgeAction := action;
                    RunEdgeTarget := middle |}).
    exists (edge :: trace). split; [split|].
    + exact (graph_edge_trace_cons edge target trace Htrace).
    + constructor; [exact H|exact Hall].
    + change (action :: GraphTraceActionWord trace = action :: word).
      now rewrite Hword.
Qed.

Lemma graph_edge_parikh_nil : forall d (edge : ProductionGraphEdge d),
    GraphEdgeParikh [] edge = 0%nat.
Proof. reflexivity. Qed.

Lemma graph_edge_parikh_cons : forall d head tail (edge : ProductionGraphEdge d),
    GraphEdgeParikh (head :: tail) edge =
      ((if production_graph_edge_eq_dec head edge then 1 else 0) +
      GraphEdgeParikh tail edge)%nat.
Proof.
  intros. unfold GraphEdgeParikh. cbn.
  destruct (production_graph_edge_eq_dec head edge); reflexivity.
Qed.

Lemma graph_edge_parikh_app : forall d left right (edge : ProductionGraphEdge d),
    GraphEdgeParikh (left ++ right) edge =
      (GraphEdgeParikh left edge + GraphEdgeParikh right edge)%nat.
Proof. intros; unfold GraphEdgeParikh; apply count_occ_app. Qed.

Lemma graph_edge_parikh_positive_iff : forall d trace (edge : ProductionGraphEdge d),
    (0 < GraphEdgeParikh trace edge)%nat <-> List.In edge trace.
Proof.
  intros. unfold GraphEdgeParikh. symmetry.
  apply count_occ_In.
Qed.

Lemma total_graph_cycle_iff : forall d graph trace,
    @TotalGraphCycle d graph trace <->
    forall edge, List.In edge graph -> List.In edge trace.
Proof.
  intros; unfold TotalGraphCycle; split; intros H edge Hin;
    specialize (H edge Hin); now apply graph_edge_parikh_positive_iff in H ||
      apply graph_edge_parikh_positive_iff.
Qed.

Lemma graph_edge_parikh_permutation : forall d left right,
    Permutation left right -> forall edge : ProductionGraphEdge d,
      GraphEdgeParikh left edge = GraphEdgeParikh right edge.
Proof. intros d left right H edge; unfold GraphEdgeParikh; now apply Permutation_count_occ. Qed.
