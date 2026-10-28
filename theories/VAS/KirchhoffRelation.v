From Coq Require Import Arith Fin Lia List Vector ZArith QArith Qring
  Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore.
From Mell.VAS Require Import Runs Intraproductions ProductionGraph
  ProductionGraphPaths GraphParikh Kirchhoff EulerCycles.

Import ListNotations.
Open Scope Q_scope.

Definition ExactProductionGraphEdges {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness : NVec d)
    (edges : list (ProductionGraphEdge d)) : Prop :=
  NoDup edges /\
  forall source action target,
    ProductionGraphTransition system gamma witness source action target <->
    List.In {| RunEdgeSource := source;
               RunEdgeAction := action;
               RunEdgeTarget := target |} edges.

Lemma exact_production_graph_edges_exists : forall d system gamma witness,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    exists edges, ExactProductionGraphEdges system gamma witness edges.
Proof. intros. now apply production_graph_exact_nodup_edges. Qed.

Definition NonnegativeQVec {d} (value : QVec d) : Prop :=
  forall index, 0 <= value index.

Definition SamePositiveSupport {d} (value : QVec d) (support : NVec d) : Prop :=
  forall index,
    (0 < value index <-> 0 < nvec_to_qvec support index).

Definition QVecDifference {d} (left right : QVec d) : QVec d :=
  fun index => left index - right index.

Definition KirchhoffRelationForEdges {d} (gamma : ProductionTriple d)
    (edges : list (ProductionGraphEdge d)) (input output : QVec d) : Prop :=
  NonnegativeQVec input /\
  NonnegativeQVec output /\
  SamePositiveSupport input (GammaInput gamma) /\
  SamePositiveSupport output (GammaOutput gamma) /\
  exists weight : ProductionGraphEdge d -> Q,
    KirchhoffBalanceQ edges weight /\
    (forall edge, List.In edge edges -> 0 < weight edge) /\
    QVecEq (QVecDifference output input)
      (KirchhoffDisplacementQ edges weight).

Lemma nonnegative_qvec_ext : forall d (left right : QVec d),
    QVecEq left right ->
    (NonnegativeQVec left <-> NonnegativeQVec right).
Proof.
  intros d left right Heq. split; intros H index.
  - setoid_rewrite <- (Heq index). apply H.
  - setoid_rewrite (Heq index). apply H.
Qed.

Lemma same_positive_support_ext : forall d (left right : QVec d) support,
    QVecEq left right ->
    (SamePositiveSupport left support <-> SamePositiveSupport right support).
Proof.
  intros d left right support Heq. split; intros H index;
    specialize (H index); setoid_rewrite <- (Heq index) ||
      setoid_rewrite (Heq index); exact H.
Qed.

Lemma same_positive_support_zero : forall d (value : QVec d),
    NonnegativeQVec value ->
    SamePositiveSupport value (Vector.const 0%nat d) ->
    QVecEq value (qvec_zero d).
Proof.
  intros d value Hnonnegative Hsupport index.
  specialize (Hsupport index). unfold nvec_to_qvec, qvec_zero in *.
  rewrite const_nth in Hsupport. unfold q_of_nat in Hsupport. cbn in Hsupport.
  destruct (Qlt_le_dec 0 (value index)) as [Hpositive|Hnotpositive].
  - apply Hsupport in Hpositive. exfalso. exact (Qlt_irrefl 0 Hpositive).
  - apply Qle_antisym; [exact Hnotpositive|apply Hnonnegative].
Qed.

Lemma same_positive_support_positive_scale : forall d coefficient
    (value : QVec d) support,
    0 < coefficient ->
    (SamePositiveSupport (qvec_scale coefficient value) support <->
     SamePositiveSupport value support).
Proof.
  intros d coefficient value support Hcoefficient. split; intros H index;
    specialize (H index); unfold qvec_scale in H.
  - assert (Hproduct : 0 < coefficient * value index <-> 0 < value index).
    { pose proof (Qmult_lt_l 0 (value index) coefficient Hcoefficient) as Hmul.
      setoid_replace (coefficient * 0) with 0 in Hmul by ring. exact Hmul. }
    rewrite Hproduct in H. exact H.
  - assert (Hproduct : 0 < coefficient * value index <-> 0 < value index).
    { pose proof (Qmult_lt_l 0 (value index) coefficient Hcoefficient) as Hmul.
      setoid_replace (coefficient * 0) with 0 in Hmul by ring. exact Hmul. }
    rewrite Hproduct. exact H.
Qed.

Fixpoint EdgeWeightLookup {d} (edges : list (ProductionGraphEdge d)) :
    QVec (length edges) -> ProductionGraphEdge d -> Q :=
  match edges as listed return QVec (length listed) -> ProductionGraphEdge d -> Q with
  | [] => fun _ _ => 0
  | head :: tail => fun weights edge =>
      if production_graph_edge_eq_dec edge head
      then weights Fin.F1
      else EdgeWeightLookup tail (fun index => weights (Fin.FS index)) edge
  end.

Definition EdgeWeightVectorOfFunction {d}
    (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> Q) : QVec (length edges) :=
  fun index => weight (Vector.nth (Vector.of_list edges) index).

Lemma edge_weight_lookup_of_function : forall d edges weight edge,
    NoDup edges -> List.In edge edges ->
    @EdgeWeightLookup d edges (EdgeWeightVectorOfFunction edges weight) edge ==
      weight edge.
Proof.
  intros d edges; induction edges as [|head tail IH]; intros weight edge Hnodup Hin;
    [contradiction|].
  inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
  cbn [EdgeWeightLookup EdgeWeightVectorOfFunction].
  destruct (production_graph_edge_eq_dec edge head) as [->|Hneq].
  - reflexivity.
  - apply IH; [exact Hnodup'|]. destruct Hin as [Heq|Hin].
    + exfalso; apply Hneq; symmetry; exact Heq.
    + exact Hin.
Qed.

Definition FiniteKirchhoffWitness {d} (gamma : ProductionTriple d)
    (edges : list (ProductionGraphEdge d)) (input output : QVec d)
    (weights : QVec (length edges)) : Prop :=
  KirchhoffBalanceQ edges (EdgeWeightLookup edges weights) /\
  (forall edge, List.In edge edges -> 0 < EdgeWeightLookup edges weights edge) /\
  QVecEq (QVecDifference output input)
    (KirchhoffDisplacementQ edges (EdgeWeightLookup edges weights)).

Lemma graph_weight_sum_q_ext : forall d edges left right select,
    (forall edge, List.In edge edges -> left edge == right edge) ->
    @GraphWeightSumQ d edges left select == GraphWeightSumQ edges right select.
Proof.
  intros d edges; induction edges as [|edge tail IH];
    intros left right select H; cbn; [reflexivity|].
  destruct (select edge).
  - apply Qplus_comp; [apply H; now left|]. apply IH.
    intros; apply H; now right.
  - apply Qplus_comp; [reflexivity|]. apply IH.
    intros; apply H; now right.
Qed.

Lemma qvec_rsum_ext : forall d (values : list (QVec d))
    (transform : QVec d -> QVec d),
    (forall value, List.In value values -> QVecEq value (transform value)) ->
    QVecEq (qvec_rsum values) (qvec_rsum (List.map transform values)).
Proof.
  intros d values; induction values as [|head tail IH]; intros transform H index;
    cbn [qvec_rsum]; [reflexivity|].
  unfold qvec_add. apply Qplus_comp.
  - apply H. now left.
  - apply IH. intros; apply H; now right.
Qed.

Lemma kirchhoff_displacement_q_ext : forall d edges left right,
    (forall edge, List.In edge edges -> left edge == right edge) ->
    QVecEq (@KirchhoffDisplacementQ d edges left)
      (KirchhoffDisplacementQ edges right).
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros left right H index;
    cbn [KirchhoffDisplacementQ qvec_rsum]; [reflexivity|].
  unfold qvec_add, qvec_scale. apply Qplus_comp.
  - apply Qmult_comp; [apply H; now left|reflexivity].
  - apply IH. intros; apply H; now right.
Qed.

Lemma finite_edge_weights_equiv : forall (d : nat) (gamma : ProductionTriple d)
    (edges : list (ProductionGraphEdge d)) (input output : QVec d),
    NoDup edges ->
    KirchhoffRelationForEdges gamma edges input output <->
    NonnegativeQVec input /\
    NonnegativeQVec output /\
    SamePositiveSupport input (GammaInput gamma) /\
    SamePositiveSupport output (GammaOutput gamma) /\
    exists weights : QVec (length edges),
      FiniteKirchhoffWitness gamma edges input output weights.
Proof.
  intros d gamma edges input output Hnodup. unfold KirchhoffRelationForEdges.
  repeat apply and_iff_compat_l. split.
  - intros [weight [Hbalance [Hpositive Hdisplacement]]].
    exists (EdgeWeightVectorOfFunction edges weight).
    unfold FiniteKirchhoffWitness. repeat split.
    + intro state. unfold KirchhoffBalanceQ in Hbalance.
      specialize (Hbalance state).
      eapply Qeq_trans.
      * apply graph_weight_sum_q_ext. intros edge Hin.
        apply edge_weight_lookup_of_function; assumption.
      * eapply Qeq_trans; [exact Hbalance|]. symmetry.
        apply graph_weight_sum_q_ext. intros edge Hin.
        apply edge_weight_lookup_of_function; assumption.
    + intros edge Hin. setoid_rewrite edge_weight_lookup_of_function;
        [apply Hpositive; exact Hin|exact Hnodup|exact Hin].
    + eapply qvec_eq_trans; [exact Hdisplacement|].
      apply kirchhoff_displacement_q_ext. intros edge Hin.
      symmetry. apply edge_weight_lookup_of_function; assumption.
  - intros [weights [Hbalance [Hpositive Hdisplacement]]].
    exists (EdgeWeightLookup edges weights). auto.
Qed.

Lemma graph_weight_sum_q_permutation : forall d left right weight select,
    Permutation left right ->
    @GraphWeightSumQ d left weight select == GraphWeightSumQ right weight select.
Proof.
  intros d left right weight select Hperm. induction Hperm; cbn.
  - reflexivity.
  - setoid_rewrite IHHperm. reflexivity.
  - destruct (select x), (select y); ring.
  - etransitivity; eauto.
Qed.

Lemma qvec_rsum_permutation : forall d (left right : list (QVec d)),
    Permutation left right -> QVecEq (qvec_rsum left) (qvec_rsum right).
Proof.
  intros d left right Hperm. induction Hperm; intro index; cbn [qvec_rsum].
  - reflexivity.
  - unfold qvec_add. setoid_rewrite (IHHperm index). reflexivity.
  - unfold qvec_add. ring.
  - etransitivity; eauto.
Qed.

Lemma kirchhoff_balance_q_permutation : forall d left right weight,
    Permutation left right ->
    (@KirchhoffBalanceQ d left weight <-> KirchhoffBalanceQ right weight).
Proof.
  intros d left right weight Hperm. split; intros H state.
  - eapply Qeq_trans.
    + symmetry. apply graph_weight_sum_q_permutation. exact Hperm.
    + eapply Qeq_trans; [apply H|]. apply graph_weight_sum_q_permutation. exact Hperm.
  - eapply Qeq_trans.
    + apply graph_weight_sum_q_permutation. exact Hperm.
    + eapply Qeq_trans; [apply H|]. symmetry.
      apply graph_weight_sum_q_permutation. exact Hperm.
Qed.

Lemma kirchhoff_displacement_q_permutation : forall d left right weight,
    Permutation left right ->
    QVecEq (@KirchhoffDisplacementQ d left weight)
      (KirchhoffDisplacementQ right weight).
Proof.
  intros d left right weight Hperm. unfold KirchhoffDisplacementQ.
  apply qvec_rsum_permutation. now apply Permutation_map.
Qed.

Lemma kirchhoff_relation_edges_permutation : forall d gamma left right input output,
    Permutation left right ->
    (@KirchhoffRelationForEdges d gamma left input output <->
     KirchhoffRelationForEdges gamma right input output).
Proof.
  intros d gamma left right input output Hperm. unfold KirchhoffRelationForEdges.
  repeat apply and_iff_compat_l. split; intros [weight [Hbalance [Hpositive Hdisp]]];
    exists weight; repeat split.
  - apply (proj1 (kirchhoff_balance_q_permutation d left right weight Hperm)); exact Hbalance.
  - intros edge Hin. apply Hpositive. eapply Permutation_in; [symmetry; exact Hperm|exact Hin].
  - eapply qvec_eq_trans; [exact Hdisp|]. apply kirchhoff_displacement_q_permutation; exact Hperm.
  - apply (proj2 (kirchhoff_balance_q_permutation d left right weight Hperm)); exact Hbalance.
  - intros edge Hin. apply Hpositive. eapply Permutation_in; [exact Hperm|exact Hin].
  - eapply qvec_eq_trans; [exact Hdisp|]. apply qvec_eq_sym.
    apply kirchhoff_displacement_q_permutation; exact Hperm.
Qed.

Lemma exact_production_graph_edges_permutation : forall d system gamma
    witness1 witness2 edges1 edges2,
    @Lemma57Witness d system gamma witness1 ->
    Lemma57Witness system gamma witness2 ->
    ExactProductionGraphEdges system gamma witness1 edges1 ->
    ExactProductionGraphEdges system gamma witness2 edges2 ->
    Permutation edges1 edges2.
Proof.
  intros d system gamma witness1 witness2 edges1 edges2 Hw1 Hw2
    [Hnodup1 Hexact1] [Hnodup2 Hexact2].
  apply NoDup_Permutation; [exact Hnodup1|exact Hnodup2|].
  intros [source action target]. rewrite <- Hexact1, <- Hexact2.
  apply production_graph_transition_witness_independent; assumption.
Qed.

Theorem kirchhoff_relation_exact_edges_independent : forall d system gamma
    witness1 witness2 edges1 edges2 input output,
    @Lemma57Witness d system gamma witness1 ->
    Lemma57Witness system gamma witness2 ->
    ExactProductionGraphEdges system gamma witness1 edges1 ->
    ExactProductionGraphEdges system gamma witness2 edges2 ->
    (KirchhoffRelationForEdges gamma edges1 input output <->
     KirchhoffRelationForEdges gamma edges2 input output).
Proof.
  intros d system gamma witness1 witness2 edges1 edges2 input output
    Hw1 Hw2 Hedges1 Hedges2.
  apply kirchhoff_relation_edges_permutation.
  exact (exact_production_graph_edges_permutation d system gamma
    witness1 witness2 edges1 edges2 Hw1 Hw2 Hedges1 Hedges2).
Qed.

Definition ProductionKirchhoffRelation {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (input output : QVec d) : Prop :=
  exists witness edges,
    Lemma57Witness system gamma witness /\
    ExactProductionGraphEdges system gamma witness edges /\
    KirchhoffRelationForEdges gamma edges input output.

Lemma production_kirchhoff_relation_fixed_edges : forall d system gamma
    witness edges input output,
    @Lemma57Witness d system gamma witness ->
    ExactProductionGraphEdges system gamma witness edges ->
    (ProductionKirchhoffRelation system gamma input output <->
     KirchhoffRelationForEdges gamma edges input output).
Proof.
  intros d system gamma witness edges input output Hw Hedges. split.
  - intros [other [other_edges [Hother [Hother_edges Hrelation]]]].
    apply (proj2 (kirchhoff_relation_exact_edges_independent d system gamma
      witness other edges other_edges input output Hw Hother Hedges Hother_edges)).
    exact Hrelation.
  - intro Hrelation. exists witness, edges. auto.
Qed.
