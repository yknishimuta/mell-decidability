From Mell.VAS Require Import Kirchhoff KirchhoffRelation KirchhoffDefinability
  KirchhoffLemma514.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge.

From Coq Require Import Lia List QArith Sorting.Permutation.
From Mell.Geometry Require Import RationalDefinability.
From Mell.VAS Require Import Runs Intraproductions RelationCone.

Open Scope Q_scope.
Import ListNotations.

Check ExactProductionGraphEdges.
Check NonnegativeQVec.
Check SamePositiveSupport.
Check KirchhoffRelationForEdges.
Check finite_edge_weights_equiv.
Check kirchhoff_relation_for_edges_qdefinable.
Check kirchhoff_relation_exact_edges_independent.
Check ProductionKirchhoffRelation.
Check production_kirchhoff_relation_qdefinable.
Check production_graph_total_cycle_scaled_gamma_displacement.
Check lemma_5_14_gamma_in_kirchhoff_relation.
Check same_positive_support_zero.
Check same_positive_support_positive_scale.
Check kirchhoff_relation_edges_permutation.
Check normalized_parikh_displacement_gamma.

Lemma regression_embedded_nvec_nonnegative : forall d (value : NVec d),
    NonnegativeQVec (nvec_to_qvec value).
Proof. intros d value index. unfold nvec_to_qvec, q_of_nat, Qle. cbn. lia. Qed.

Lemma regression_embedded_nvec_same_support : forall d (value : NVec d),
    SamePositiveSupport (nvec_to_qvec value) value.
Proof. intros d value index. reflexivity. Qed.

Example regression_dimension_zero_lemma_5_14
    (system : PlainVAS 0) (gamma : ProductionTriple 0) :
    ValidProductionTriple system gamma ->
    ProductionKirchhoffRelation system gamma
      (nvec_to_qvec (GammaInput gamma)) (nvec_to_qvec (GammaOutput gamma)).
Proof. apply lemma_5_14_gamma_in_kirchhoff_relation. Qed.

Example regression_empty_edges_qdefinable : forall d gamma,
    QDefinable
      (fun pair : QVec (d + d) =>
        KirchhoffRelationForEdges gamma []
          (qpair_left pair) (qpair_right pair)).
Proof.
  intros d gamma. apply kirchhoff_relation_for_edges_qdefinable.
  constructor.
Qed.

Example regression_edge_order_irrelevant : forall d gamma left right input output,
    Permutation left right ->
    (@KirchhoffRelationForEdges d gamma left input output <->
     KirchhoffRelationForEdges gamma right input output).
Proof. apply kirchhoff_relation_edges_permutation. Qed.

Lemma regression_zero_weight_rejected_on_present_edge : forall d gamma edges
    (input output : QVec d) edge,
    List.In edge edges ->
    ~ (KirchhoffRelationForEdges gamma edges input output /\
       (forall weight,
         KirchhoffBalanceQ edges weight ->
         weight edge == 0)).
Proof.
  intros d gamma edges input output edge Hin [Hrelation Hall].
  destruct Hrelation as [_ [_ [_ [_ [weight [Hbalance [Hpositive _]]]]]]].
  specialize (Hpositive edge Hin). specialize (Hall weight Hbalance).
  setoid_rewrite Hall in Hpositive. exact (Qlt_irrefl 0 Hpositive).
Qed.

Print Assumptions finite_edge_weights_equiv.
Print Assumptions kirchhoff_relation_for_edges_qdefinable.
Print Assumptions kirchhoff_relation_exact_edges_independent.
Print Assumptions production_kirchhoff_relation_qdefinable.
Print Assumptions production_graph_total_cycle_scaled_gamma_displacement.
Print Assumptions lemma_5_14_gamma_in_kirchhoff_relation.
