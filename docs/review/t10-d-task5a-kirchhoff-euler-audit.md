# T10-D Task 5A: Kirchhoff functions and Euler cycles

## Scope and baseline

- Repository branch: `work/mell-formalization`
- Starting commit: `71ecc3fa7384777f96319b2ab604c526fb2ab771`
- Source: Leroux (2012), Section 5.3, up to the graph-theoretic Euler realization used before Lemmas 5.14 and 5.15.
- This task does not lift a production-graph cycle to a VAS run and does not prove Lemma 5.14, Lemma 5.15, or Corollary 5.16.

## Public representation

`GraphEdgeTrace source target trace` inductively records the complete ordered list of directed `ProductionGraphEdge`s, including source, action, and target. `ProductionGraphEdgeTrace` additionally proves that every recorded edge is an actual transition of the selected production graph.

`GraphEdgeParikh trace edge` is `count_occ` with decidable equality on the full edge record. Consequently equal action labels on distinct source/target pairs remain distinct. `GraphCycle trace root` is a closed edge trace. `TotalGraphCycle graph trace` states strict positive occurrence of every edge listed by the exact graph.

The finite exact graph representation is kept explicit: all Euler theorems take a `NoDup graph` edge list. The production-graph specialization takes the pointwise `iff` connecting this list to `ProductionGraphTransition`; it therefore applies only to an actual represented graph, not to arbitrary over-approximating signatures in the Corollary 5.12 catalog.

`production_graph_exact_nodup_edges` bridges Task 4A's finite transition representation to this interface by deduplicating the finite list while preserving its pointwise membership equivalence.

## Kirchhoff definitions

`KirchhoffBalanceNat graph f` and `KirchhoffBalanceQ graph f` state, at every state, equality (respectively Leibniz equality on naturals and `Qeq` on rationals) of the sum of outgoing and incoming edge weights. A self-loop is selected by both sums.

`KirchhoffDisplacementNat graph f` is the VAS displacement of the action word obtained by repeating every graph edge action exactly `f edge` times. `KirchhoffDisplacementQ` is the finite rational weighted sum of embedded integer actions. Additivity and natural/rational scaling are proved.

Public cycle facts include:

```coq
graph_cycle_parikh_kirchhoff :
  forall d graph trace root,
    NoDup graph ->
    (forall edge, List.In edge trace -> List.In edge graph) ->
    GraphCycle trace root ->
    KirchhoffBalanceNat graph (GraphEdgeParikh trace)
```

and `graph_edge_parikh_displacement`, which identifies the weighted Kirchhoff displacement with the action-word displacement of a trace whose Parikh counts are exact.

## Euler realization

The central theorem is:

```coq
positive_kirchhoff_euler_total_cycle :
  forall d states graph root weight,
    NoDup graph ->
    List.In root states ->
    EdgeEndpointsIn states graph ->
    FiniteDirectedStronglyConnected states graph ->
    KirchhoffBalanceNat graph weight ->
    (forall edge, List.In edge graph -> 0 < weight edge) ->
    exists trace,
      GraphCycle trace root /\
      (forall edge, List.In edge trace -> List.In edge graph) /\
      TotalGraphCycle graph trace /\
      forall edge, List.In edge graph ->
        GraphEdgeParikh trace edge = weight edge
```

The proof expands each edge into a finite bag containing exactly its specified multiplicity. A bounded maximum chooses a maximal trail. Flow balance forces a maximal trail to close. A maximal closed cycle that leaves a residual edge can be enlarged: strong connectivity reaches a residual-edge source from a vertex already on the cycle, residual balance produces a nonempty residual cycle there, and splicing contradicts maximality. Hence the final closed trace is a permutation of the expanded bag, yielding exact per-edge occurrence counts. The termination/maximum measure is the finite bag/trace length, bounded by the expanded bag length. The empty graph is admitted and is realized by the empty trace at the root.

The production-graph specialization is:

```coq
production_graph_positive_kirchhoff_realized :
  forall d system gamma witness graph weight,
    ValidProductionTriple system gamma ->
    Lemma57Witness system gamma witness ->
    NoDup graph ->
    (forall source action target,
      ProductionGraphTransition system gamma witness source action target <->
      List.In {| RunEdgeSource := source;
                 RunEdgeAction := action;
                 RunEdgeTarget := target |} graph) ->
    KirchhoffBalanceNat graph weight ->
    (forall edge, List.In edge graph -> 0 < weight edge) ->
    exists trace,
      ProductionGraphEdgeTrace system gamma witness
        (ProductionGraphSpecialState gamma witness)
        (ProductionGraphSpecialState gamma witness) trace /\
      TotalGraphCycle graph trace /\
      forall edge, List.In edge graph ->
        GraphEdgeParikh trace edge = weight edge
```

It uses Task 4A finite states and strong connectivity. Its conclusion is deliberately a graph cycle only.

## Verification and assumptions

The focused regression covers empty traces/graphs, a self-loop Parikh count, exact Euler realization of loop weight three, distinction of two edges with the same action but different endpoints, and rejection of an unbalanced single-edge weighting. The examples are dimension-polymorphic and therefore include dimension zero whenever their hypotheses are inhabited. The definitions and general theorems additionally cover asymmetric directed graphs and multiple cycles. Strong connectivity is an explicit theorem premise and is used in the residual-cycle construction; no theorem is stated for a non-strongly-connected graph.

`Print Assumptions` results:

- `graph_cycle_parikh_kirchhoff`: closed under the global context.
- `graph_edge_parikh_displacement`: closed under the global context.
- `positive_kirchhoff_euler_total_cycle`: depends only on `Classical_Prop.classic`.
- `production_graph_positive_kirchhoff_realized`: depends only on `Classical_Prop.classic`.

The classical dependency is confined to choosing a maximum from a nonempty bounded Prop predicate; no choice oracle or executable graph generator is introduced. Scans reject `Admitted`, `admit`, `Abort`, new `Axiom`, `ClassicalEpsilon`, constructive/dependent/countable choice, UIP/K, `Eq_rect_eq`, functional extensionality, and oracle hooks.

## Task 5B handoff

The remaining obligations are precisely the semantic realization steps, not graph Euler theory:

1. relate rational/integral Kirchhoff functions to the production-graph cones used in Lemma 5.14;
2. realize a production-graph cycle, with its concrete ordered edge trace, as an actual VAS run after the required intraproduction/capacity pumping (Lemma 5.15);
3. prove the asymptotic definability conclusion culminating in Corollary 5.16;
4. keep graph-cycle existence distinct from VAS-run realizability throughout that lift.
