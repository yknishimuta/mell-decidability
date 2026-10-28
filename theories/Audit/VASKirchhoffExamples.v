From Mell.VAS Require Import ProductionGraph GraphParikh Kirchhoff EulerCycles.
From Mell.Core Require Import Vector.

From Coq Require Import Lia List.
Import ListNotations.

Check GraphEdgeTrace.
Check ProductionGraphEdgeTrace.
Check GraphEdgeParikh.
Check GraphCycle.
Check TotalGraphCycle.
Check graph_cycle_parikh_kirchhoff.
Check positive_kirchhoff_euler_total_cycle.
Check production_graph_positive_kirchhoff_realized.

Section BoundaryRegressions.

Variable d : nat.
Variable root : NVec d.
Variable action : ZVec d.

Definition audit_loop : ProductionGraphEdge d :=
  {| RunEdgeSource := root;
     RunEdgeAction := action;
     RunEdgeTarget := root |}.

Example empty_trace_is_cycle : GraphCycle [] root.
Proof. constructor. Qed.

Example empty_trace_parikh_zero :
    GraphEdgeParikh [] audit_loop = 0%nat.
Proof. apply graph_edge_parikh_nil. Qed.

Example singleton_loop_trace : GraphCycle [audit_loop] root.
Proof. unfold GraphCycle; exact (graph_edge_trace_singleton d audit_loop). Qed.

Example singleton_loop_parikh :
    GraphEdgeParikh [audit_loop] audit_loop = 1%nat.
Proof.
  rewrite graph_edge_parikh_cons, graph_edge_parikh_nil.
  destruct (production_graph_edge_eq_dec audit_loop audit_loop);
    [reflexivity|contradiction].
Qed.

Example loop_weight_three_exact_euler :
    exists trace,
      GraphCycle trace root /\
      TotalGraphCycle [audit_loop] trace /\
      GraphEdgeParikh trace audit_loop = 3%nat.
Proof.
  destruct (positive_kirchhoff_euler_total_cycle d [root] [audit_loop] root
    (fun _ => 3%nat)) as [trace [Hcycle [_ [Htotal Hexact]]]].
  - constructor; [intro H; inversion H|constructor].
  - now left.
  - intros edge [<-|[]]. cbn; auto.
  - intros source target Hsource Htarget.
    cbn in Hsource, Htarget. destruct Hsource as [->|[]].
    destruct Htarget as [->|[]]. exists []; split; constructor.
  - intro state. unfold GraphWeightSumNat, EdgeLeaves, EdgeEnters, audit_loop.
    cbn. reflexivity.
  - intros edge [<-|[]]. lia.
  - exists trace. repeat split; auto. apply Hexact. now left.
Qed.

Variable other : NVec d.
Hypothesis root_other : root <> other.

Definition audit_same_action_other_loop : ProductionGraphEdge d :=
  {| RunEdgeSource := other;
     RunEdgeAction := action;
     RunEdgeTarget := other |}.

Example same_action_different_edges_are_distinct :
    audit_loop <> audit_same_action_other_loop.
Proof. intro H; inversion H; contradiction. Qed.

Definition audit_unbalanced_edge : ProductionGraphEdge d :=
  {| RunEdgeSource := root;
     RunEdgeAction := action;
     RunEdgeTarget := other |}.

Example unbalanced_single_edge_is_not_kirchhoff :
    ~ KirchhoffBalanceNat [audit_unbalanced_edge] (fun _ => 1%nat).
Proof.
  intro Hbalance. specialize (Hbalance root).
  unfold GraphWeightSumNat, EdgeLeaves, EdgeEnters, audit_unbalanced_edge in Hbalance.
  cbn in Hbalance.
  destruct (nvec_eq_dec root root) as [_|Hbad]; [|contradiction].
  destruct (nvec_eq_dec other root) as [Hbad|_]; [symmetry in Hbad; contradiction|].
  discriminate.
Qed.

Example empty_graph_euler :
    exists trace,
      GraphCycle trace root /\
      (forall edge, List.In edge trace -> List.In edge []) /\
      TotalGraphCycle [] trace /\
      forall edge, List.In edge [] -> GraphEdgeParikh trace edge = 0%nat.
Proof.
  eapply (positive_kirchhoff_euler_total_cycle d [root] [] root
    (fun _ => 0%nat)).
  - constructor.
  - now left.
  - intros edge H; contradiction.
  - intros source target Hsource Htarget.
    cbn in Hsource, Htarget. destruct Hsource as [->|[]].
    destruct Htarget as [->|[]]. exists []; split; constructor.
  - intro state; reflexivity.
  - intros edge H; contradiction.
Qed.

End BoundaryRegressions.

Print Assumptions graph_cycle_parikh_kirchhoff.
Print Assumptions graph_edge_parikh_displacement.
Print Assumptions positive_kirchhoff_euler_total_cycle.
Print Assumptions production_graph_exact_nodup_edges.
Print Assumptions production_graph_positive_kirchhoff_realized.
