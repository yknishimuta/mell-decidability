From Coq Require Import Arith Fin Lia List Vector ZArith QArith Qring.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge RationalHToV.
From Mell.VAS Require Import Runs ProductionGraph GraphParikh.

Import ListNotations.

Fixpoint GraphWeightSumNat {d} (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> nat)
    (select : ProductionGraphEdge d -> bool) : nat :=
  match edges with
  | [] => 0
  | edge :: tail =>
      (if select edge then weight edge else 0) +
      GraphWeightSumNat tail weight select
  end.

Fixpoint GraphWeightSumQ {d} (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> Q)
    (select : ProductionGraphEdge d -> bool) : Q :=
  match edges with
  | [] => 0
  | edge :: tail =>
      (if select edge then weight edge else 0) +
      GraphWeightSumQ tail weight select
  end.

Definition EdgeLeaves {d} (state : NVec d) (edge : ProductionGraphEdge d) : bool :=
  if nvec_eq_dec (RunEdgeSource edge) state then true else false.

Definition EdgeEnters {d} (state : NVec d) (edge : ProductionGraphEdge d) : bool :=
  if nvec_eq_dec (RunEdgeTarget edge) state then true else false.

Definition KirchhoffBalanceNat {d} (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> nat) : Prop :=
  forall state,
    GraphWeightSumNat edges weight (EdgeLeaves state) =
    GraphWeightSumNat edges weight (EdgeEnters state).

Definition KirchhoffBalanceQ {d} (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> Q) : Prop :=
  forall state,
    GraphWeightSumQ edges weight (EdgeLeaves state) ==
    GraphWeightSumQ edges weight (EdgeEnters state).

Definition WeightedGraphActionWord {d} (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> nat) : list (ZVec d) :=
  List.flat_map
    (fun edge => List.repeat (RunEdgeAction edge) (weight edge)) edges.

Definition KirchhoffDisplacementNat {d} (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> nat) : ZVec d :=
  ActionDisplacement (WeightedGraphActionWord edges weight).

Definition KirchhoffDisplacementQ {d} (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> Q) : QVec d :=
  qvec_rsum (List.map
    (fun edge => qvec_scale (weight edge)
      (zvec_to_qvec (RunEdgeAction edge))) edges).

Lemma graph_weight_sum_nat_ext : forall d edges left right select,
    (forall edge, List.In edge edges -> left edge = right edge) ->
    @GraphWeightSumNat d edges left select = GraphWeightSumNat edges right select.
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros left right select H; cbn.
  - reflexivity.
  - rewrite (H edge (or_introl eq_refl)), (IH left right select).
    + reflexivity.
    + intros; apply H; now right.
Qed.

Lemma graph_weight_sum_nat_add : forall d edges left right select,
    @GraphWeightSumNat d edges (fun edge => left edge + right edge)%nat select =
    (GraphWeightSumNat edges left select +
     GraphWeightSumNat edges right select)%nat.
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros; cbn; [lia|].
  destruct (select edge); cbn; rewrite IH; lia.
Qed.

Lemma graph_weight_sum_nat_nsmul : forall d edges coefficient weight select,
    @GraphWeightSumNat d edges
      (fun edge => coefficient * weight edge)%nat select =
    (coefficient * GraphWeightSumNat edges weight select)%nat.
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros; cbn; [lia|].
  destruct (select edge); cbn; rewrite IH; lia.
Qed.

Lemma kirchhoff_balance_nat_add : forall d edges left right,
    @KirchhoffBalanceNat d edges left -> KirchhoffBalanceNat edges right ->
    KirchhoffBalanceNat edges (fun edge => left edge + right edge)%nat.
Proof.
  intros d edges left right Hleft Hright state.
  repeat rewrite graph_weight_sum_nat_add. now rewrite Hleft, Hright.
Qed.

Lemma kirchhoff_balance_nat_nsmul : forall d edges coefficient weight,
    @KirchhoffBalanceNat d edges weight ->
    KirchhoffBalanceNat edges (fun edge => coefficient * weight edge)%nat.
Proof.
  intros d edges coefficient weight H state.
  repeat rewrite graph_weight_sum_nat_nsmul. now rewrite H.
Qed.

Lemma graph_weight_sum_q_add : forall d edges
    (left right : ProductionGraphEdge d -> Q) select,
    @GraphWeightSumQ d edges (fun edge => Qplus (left edge) (right edge)) select ==
    Qplus (GraphWeightSumQ edges left select) (GraphWeightSumQ edges right select).
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros; cbn.
  - ring.
  - destruct (select edge); cbn; setoid_rewrite IH; ring.
Qed.

Lemma graph_weight_sum_q_scale : forall d edges (coefficient : Q)
    (weight : ProductionGraphEdge d -> Q) select,
    @GraphWeightSumQ d edges (fun edge => Qmult coefficient (weight edge)) select ==
    Qmult coefficient (GraphWeightSumQ edges weight select).
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros; cbn.
  - ring.
  - destruct (select edge); cbn; setoid_rewrite IH; ring.
Qed.

Lemma kirchhoff_balance_q_add : forall d edges left right,
    @KirchhoffBalanceQ d edges left -> KirchhoffBalanceQ edges right ->
    KirchhoffBalanceQ edges (fun edge => Qplus (left edge) (right edge)).
Proof.
  intros d edges left right Hleft Hright state.
  eapply Qeq_trans; [apply graph_weight_sum_q_add|].
  eapply Qeq_trans; [apply Qplus_comp; [apply Hleft|apply Hright]|].
  symmetry; apply graph_weight_sum_q_add.
Qed.

Lemma kirchhoff_balance_q_scale : forall d edges coefficient weight,
    @KirchhoffBalanceQ d edges weight ->
    KirchhoffBalanceQ edges (fun edge => Qmult coefficient (weight edge)).
Proof.
  intros d edges coefficient weight H state.
  eapply Qeq_trans; [apply graph_weight_sum_q_scale|].
  eapply Qeq_trans; [apply Qmult_comp; [reflexivity|apply H]|].
  symmetry; apply graph_weight_sum_q_scale.
Qed.

Definition TraceLeaves {d} (state : NVec d)
    (trace : list (ProductionGraphEdge d)) : nat :=
  count_occ nvec_eq_dec (List.map RunEdgeSource trace) state.

Definition TraceEnters {d} (state : NVec d)
    (trace : list (ProductionGraphEdge d)) : nat :=
  count_occ nvec_eq_dec (List.map RunEdgeTarget trace) state.

Lemma graph_edge_trace_vertices : forall d source target trace,
    @GraphEdgeTrace d source target trace ->
    List.map RunEdgeSource trace ++ [target] =
      source :: List.map RunEdgeTarget trace.
Proof.
  intros d source target trace H; induction H; cbn; [reflexivity|].
  now rewrite IHGraphEdgeTrace.
Qed.

Lemma graph_cycle_trace_balance : forall d root trace state,
    @GraphCycle d trace root -> TraceLeaves state trace = TraceEnters state trace.
Proof.
  intros d root trace state Hcycle.
  unfold TraceLeaves, TraceEnters.
  pose proof (graph_edge_trace_vertices d root root trace Hcycle) as Hvertices.
  apply (f_equal (fun values => count_occ nvec_eq_dec values state)) in Hvertices.
  repeat rewrite count_occ_app in Hvertices. cbn in Hvertices.
  destruct (nvec_eq_dec root state); cbn in Hvertices; lia.
Qed.

Lemma graph_weight_sum_onehot_absent : forall d graph head select,
    ~ List.In head graph ->
    @GraphWeightSumNat d graph
      (fun edge => if production_graph_edge_eq_dec edge head then 1%nat else 0%nat)
      select = 0%nat.
Proof.
  intros d graph; induction graph as [|edge graph IH]; intros head select Hnotin;
    cbn; [reflexivity|].
  destruct (production_graph_edge_eq_dec edge head) as [->|Hne].
  - exfalso; apply Hnotin; now left.
  - assert (Htail : ~ List.In head graph).
    { intro Hin; apply Hnotin; now right. }
    destruct (select edge); cbn; now apply IH.
Qed.

Lemma graph_weight_sum_onehot : forall d graph head select,
    NoDup graph -> List.In head graph ->
    @GraphWeightSumNat d graph
      (fun edge => if production_graph_edge_eq_dec edge head then 1%nat else 0%nat)
      select = if select head then 1%nat else 0%nat.
Proof.
  intros d graph; induction graph as [|edge graph IH]; intros head select Hnodup Hin;
    [contradiction|].
  inversion Hnodup as [|? ? Hnotin Hnodup']; subst. cbn.
  destruct Hin as [->|Hin].
  - destruct (production_graph_edge_eq_dec head head) as [_|Hbad];
      [|contradiction]. destruct (select head); cbn.
    + now rewrite graph_weight_sum_onehot_absent.
    + now rewrite graph_weight_sum_onehot_absent.
  - destruct (production_graph_edge_eq_dec edge head) as [->|Hne];
      [exfalso; apply Hnotin; exact Hin|].
    destruct (select edge); cbn; apply IH; assumption.
Qed.

Lemma graph_weight_sum_parikh : forall d graph trace state,
    NoDup graph ->
    (forall edge, List.In edge trace -> List.In edge graph) ->
    @GraphWeightSumNat d graph (GraphEdgeParikh trace) (EdgeLeaves state) =
      TraceLeaves state trace.
Proof.
  intros d graph trace. induction trace as [|head tail IH]; intros state Hnodup Hsub.
  - clear Hnodup Hsub. unfold TraceLeaves. cbn.
    induction graph as [|edge graph IHgraph]; cbn; [reflexivity|].
    destruct (EdgeLeaves state edge); cbn; exact IHgraph.
  - assert (Hhead : List.In head graph) by (apply Hsub; now left).
    assert (Htail : forall edge, List.In edge tail -> List.In edge graph).
    { intros edge Hin; apply Hsub; now right. }
    eapply eq_trans.
    + apply graph_weight_sum_nat_ext with
        (right := fun edge =>
          ((if production_graph_edge_eq_dec edge head then 1 else 0) +
           GraphEdgeParikh tail edge)%nat).
      intros edge Hedge.
      rewrite graph_edge_parikh_cons.
      destruct (production_graph_edge_eq_dec head edge) as [->|Hne].
      * destruct (production_graph_edge_eq_dec edge edge); [lia|contradiction].
      * destruct (production_graph_edge_eq_dec edge head); [congruence|reflexivity].
    + rewrite graph_weight_sum_nat_add,
        (graph_weight_sum_onehot d graph head (EdgeLeaves state) Hnodup Hhead),
        (IH state Hnodup Htail).
      unfold TraceLeaves. cbn. unfold EdgeLeaves.
      destruct (nvec_eq_dec (RunEdgeSource head) state); reflexivity.
Qed.

Lemma graph_weight_sum_parikh_enters : forall d graph trace state,
    NoDup graph ->
    (forall edge, List.In edge trace -> List.In edge graph) ->
    @GraphWeightSumNat d graph (GraphEdgeParikh trace) (EdgeEnters state) =
      TraceEnters state trace.
Proof.
  intros d graph trace. induction trace as [|head tail IH]; intros state Hnodup Hsub.
  - clear Hnodup Hsub. unfold TraceEnters. cbn.
    induction graph as [|edge graph IHgraph]; cbn; [reflexivity|].
    destruct (EdgeEnters state edge); cbn; exact IHgraph.
  - assert (Hhead : List.In head graph) by (apply Hsub; now left).
    assert (Htail : forall edge, List.In edge tail -> List.In edge graph).
    { intros edge Hin; apply Hsub; now right. }
    eapply eq_trans.
    + apply graph_weight_sum_nat_ext with
        (right := fun edge =>
          ((if production_graph_edge_eq_dec edge head then 1 else 0) +
           GraphEdgeParikh tail edge)%nat).
      intros edge Hedge.
      rewrite graph_edge_parikh_cons.
      destruct (production_graph_edge_eq_dec head edge) as [->|Hne].
      * destruct (production_graph_edge_eq_dec edge edge); [lia|contradiction].
      * destruct (production_graph_edge_eq_dec edge head); [congruence|reflexivity].
    + rewrite graph_weight_sum_nat_add,
        (graph_weight_sum_onehot d graph head (EdgeEnters state) Hnodup Hhead),
        (IH state Hnodup Htail).
      unfold TraceEnters. cbn. unfold EdgeEnters.
      destruct (nvec_eq_dec (RunEdgeTarget head) state); reflexivity.
Qed.

Theorem graph_cycle_parikh_kirchhoff : forall d graph trace root,
    NoDup graph ->
    (forall edge, List.In edge trace -> List.In edge graph) ->
    @GraphCycle d trace root ->
    KirchhoffBalanceNat graph (GraphEdgeParikh trace).
Proof.
  intros d graph trace root Hnodup Hsub Hcycle state.
  rewrite (graph_weight_sum_parikh d graph trace state Hnodup Hsub),
    (graph_weight_sum_parikh_enters d graph trace state Hnodup Hsub).
  now apply graph_cycle_trace_balance with (root := root).
Qed.
