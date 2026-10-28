# T10-D Task 5B audit: Kirchhoff relation and Lemma 5.14

## Scope and source correspondence

This checkpoint formalizes Leroux (2012), Section 5.3 through Lemma 5.14 only.
It does not prove Lemma 5.15, Corollary 5.16, or a lifting of arbitrary graph
cycles to VAS runs.

For a production triple `gamma = (x,c,y)`, the formal relation keeps every
condition in the paper:

- rational input and output vectors are coordinatewise nonnegative;
- their strictly positive supports are exactly the supports of `x` and `y`;
- every edge of the exact production graph receives a strictly positive
  rational weight;
- the weight satisfies Kirchhoff flow conservation at every graph state; and
- `output - input` is the weighted sum of the original integer VAS actions.

The exact edge representation is a `NoDup` list whose membership is equivalent
to `ProductionGraphTransition`. Edges with the same action but different source
or target remain distinct.

## Public representation

`ExactProductionGraphEdges system gamma witness edges` is the conjunction of
`NoDup edges` and exact pointwise membership in the production graph.

`KirchhoffRelationForEdges gamma edges input output` is defined as

```text
NonnegativeQVec input /\
NonnegativeQVec output /\
SamePositiveSupport input (GammaInput gamma) /\
SamePositiveSupport output (GammaOutput gamma) /\
exists weight : ProductionGraphEdge d -> Q,
  KirchhoffBalanceQ edges weight /\
  (forall edge, In edge edges -> 0 < weight edge) /\
  QVecEq (QVecDifference output input)
    (KirchhoffDisplacementQ edges weight)
```

`ProductionKirchhoffRelation system gamma input output` existentially packages
a `Lemma57Witness`, an exact edge list, and the fixed-edge relation. The
independence theorem proves that every two correct witness/edge choices define
the same relation.

## Finite weights and definability

`finite_edge_weights_equiv` replaces the unrestricted edge function by a
vector of exactly `length edges` rational variables. `NoDup` supplies unique
edge indexing; lookup and reconstruction preserve strict positivity, all
balance sums, and displacement.

`qkirchhoff_relation_formula` has `2*d` free variables and `length edges`
existential weight variables. Its finite conjunction contains nonnegativity,
both exact support conditions, strict weight positivity, one balance equation
per enumerated state endpoint, and one displacement equation per coordinate.
All products are by fixed integer action coefficients; there is no
variable-by-variable multiplication. Formula semantics and closedness are
proved before exposing:

```text
kirchhoff_relation_for_edges_qdefinable :
  forall d gamma edges,
    NoDup edges ->
    QDefinable (fun pair =>
      KirchhoffRelationForEdges gamma edges
        (qpair_left pair) (qpair_right pair))
```

For a valid triple, one exact graph is obtained propositionally and the edge
independence theorem transports its finite formula to the existential public
relation. No executable graph-selection function is introduced.

## Lemma 5.14

For each exact graph edge, its defining Omega run is projected to a special
state graph cycle containing that edge. These cycles are concatenated with the
basic multiplier-one run supplied by validity. The resulting trace is total,
and its multiplier is `1 + sum n_j`, hence positive. Its action displacement is
exactly that multiplier times `GammaOutput - GammaInput`.

The trace Parikh function is balanced and positive on every exact edge. Dividing
it by the positive multiplier yields a positive rational Kirchhoff function
whose displacement is exactly `y-x`. This proves
`lemma_5_14_gamma_in_kirchhoff_relation`. The construction only projects actual
Omega runs to graph cycles; it never assumes the converse lift.

## Verification and assumptions

Focused compilation and `coqchk -silent` cover the three source modules and the
audit module. `Print Assumptions` results are:

- `finite_edge_weights_equiv`: closed;
- `kirchhoff_relation_for_edges_qdefinable`: closed;
- `kirchhoff_relation_exact_edges_independent`: `Classical_Prop.classic`;
- `production_kirchhoff_relation_qdefinable`: `Classical_Prop.classic`;
- `production_graph_total_cycle_scaled_gamma_displacement`: closed;
- `lemma_5_14_gamma_in_kirchhoff_relation`: `Classical_Prop.classic`.

The classical dependency comes from finite exact graph/witness existence and
permutation transport already admitted by the project contract. No choice
operator, functional extensionality, UIP/K, `Eq_rect_eq`, `Admitted`, `Abort`,
or new axiom is used.

The regression audit checks embedded natural-vector nonnegativity and exact
support, rejection of zero weight on a present edge, dimension-zero
specialization of Lemma 5.14, empty-edge definability, edge-list permutation
invariance, all public types, and the above assumptions. The large explicit
Example 5.13 enumeration is not duplicated here.

The final independent review found no Critical or Important issue. It checked
the complete relation contract, finite variable placement and closedness,
edge/witness independence, the positive multiplier normalization, and the
one-way projection from actual Omega runs. Its only Minor observation is that
Example 5.13 and value-level counterexamples for every rejected conjunct are
not separately enumerated; the corresponding general semantic equivalences
and boundary regressions are present.

## Task 5C handoff

Lemma 5.15 still requires:

1. clearing denominators of a rational positive Kirchhoff witness;
2. separating a positive integral residual circulation;
3. realizing that circulation by Task 5A's Euler theorem;
4. pumping with the Lemma 5.7 intraproduction so every finite prefix is
   nonnegative on unbounded coordinates while bounded coordinates are fixed;
5. lifting the specially prepared graph cycle word to an actual VAS run; and
6. connecting the resulting integral transformer witness to the rational cone
   of the capacity transformer.

Corollary 5.16 must additionally classify relations by the finite production
graph signature and both input/output support masks; graph finiteness alone is
not sufficient.
