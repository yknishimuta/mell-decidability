# T10-D Task 4A audit: production graphs

Baseline: `b1da514b1a8d02266589be8e31ecb8dd4a0be608`.

Scope: Leroux (2012), Section 5.2, production graphs and Corollaries
5.9--5.11.  Corollary 5.12, Kirchhoff functions, Lemmas 5.14--5.15 and
Corollary 5.16 are deliberately out of scope.

## Representation

The bounded-coordinate mask is passed explicitly; it is never extracted from
the existential Lemma 5.7 witness into `Set`.

```coq
Definition ProjectBounded {d} (witness configuration : NVec d) : NVec d :=
  Vector.map2 (fun mask value => if Nat.eqb mask 0 then value else 0)
    witness configuration.

Definition Lemma57Witness {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness : NVec d) : Prop :=
  IntraProduction system gamma witness /\
  forall index : Fin.t d,
    (BoundedGammaCoordinate system gamma index <->
     Vector.nth witness index = 0%nat).

Definition ProductionGraphState {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness state : NVec d) : Prop :=
  exists configuration,
    QGamma system gamma configuration /\
    state = ProjectBounded witness configuration.
```

An edge is not merely a step between two arbitrary `QGamma` points.  It must
be an adjacent step of one concrete `OmegaGamma` run:

```coq
Definition ProductionGraphTransition {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness : NVec d)
    (source : NVec d) (action : ZVec d) (target : NVec d) : Prop :=
  exists run configuration next,
    OmegaGamma system gamma run /\
    RunAdjacentStep run configuration action next /\
    PlainVASStep system configuration action next /\
    source = ProjectBounded witness configuration /\
    target = ProjectBounded witness next.
```

`ProductionGraphPath system gamma witness source target word` is inductive:
the empty constructor stays at one state, and the step constructor prefixes
one `ProductionGraphTransition` and its action label.  Append and word-split
lemmas are public.  Only the sound projection from an omega run to a graph
path is proved; no unsupported graph-path-to-VAS-run lifting is asserted.

## Corollaries 5.9--5.11

```coq
corollary_5_9_omega_endpoints_special :
  forall d system gamma witness run,
    ValidProductionTriple system gamma ->
    Lemma57Witness system gamma witness ->
    OmegaGamma system gamma run ->
    ProjectBounded witness (RunSource run) =
      ProductionGraphSpecialState gamma witness /\
    ProjectBounded witness (RunTarget run) =
      ProductionGraphSpecialState gamma witness.

corollary_5_10_production_graph_strongly_connected :
  forall d system gamma witness source target,
    ValidProductionTriple system gamma ->
    Lemma57Witness system gamma witness ->
    ProductionGraphState system gamma witness source ->
    ProductionGraphState system gamma witness target ->
    exists word,
      ProductionGraphPath system gamma witness source target word.

corollary_5_11_projected_states_antichain :
  forall d system gamma witness source target,
    ValidProductionTriple system gamma ->
    Lemma57Witness system gamma witness ->
    ProductionGraphState system gamma witness source ->
    ProductionGraphState system gamma witness target ->
    nvec_le source target ->
    source = target.
```

For Corollary 5.9, the common omega multiplier makes both endpoint offsets
intraproductions, hence zero on every bounded coordinate.  Corollary 5.10
splits an actual omega run at each occurrence and concatenates the path back
to the special state with the path out to the target state.  Corollary 5.11
uses one uniform multiple of the Lemma 5.7 witness to dominate all unbounded
coordinates, applies Lemma 5.5 and Lemma 5.6, and recovers equality on every
bounded coordinate.

## Individual graph finiteness

```coq
production_graph_states_finite :
  forall d system gamma witness,
    ValidProductionTriple system gamma ->
    Lemma57Witness system gamma witness ->
    exists states : list (NVec d),
      forall state,
        ProductionGraphState system gamma witness state <->
        List.In state states.

production_graph_transitions_finite :
  forall d system gamma witness,
    ValidProductionTriple system gamma ->
    Lemma57Witness system gamma witness ->
    exists transitions : list (ProductionGraphEdge d),
      forall source action target,
        ProductionGraphTransition system gamma witness source action target <->
        List.In {| RunEdgeSource := source;
                   RunEdgeAction := action;
                   RunEdgeTarget := target |} transitions.
```

State finiteness is a Prop-level existence proof: Dickson restricted to the
state predicate supplies a finite cover, and Corollary 5.11 turns every cover
comparison into equality.  Transition finiteness selects, with finite
`Classical_Prop.classic` case splits, the actual edges from
`states * system * states`.  No executable graph generator or `QGamma`
decision procedure is claimed.

`finite_production_graph_exists` first obtains a Lemma 5.7 witness in `Prop`
and packages exact finite state and transition lists.  The projection,
special state, state predicate, transition predicate, and path predicate are
all proved independent of which valid Lemma 5.7 witness is supplied.

## Regression coverage

`VASProductionGraphExamples.v` checks all public types and covers dimension
zero, the all-unbounded one-dimensional graph, a mixed bounded/unbounded
projection, a nonempty special-state cycle, strong connectivity, antichain
behavior, finite state/edge representations, and two different Lemma 5.7
witnesses inducing the same projection.  Earlier imported VAS audits retain
coverage of empty/zero/duplicate/signed actions, nonzero capacity, and a run
whose intermediate configuration lies below capacity.

The explicit three-dimensional Example 5.3/5.8 graph was not duplicated: its
mathematical obligations are covered by the general theorems, while the
existing one- and two-dimensional regressions exercise the same projection,
cycle, mixed-coordinate, and witness-independence mechanisms.

## Assumptions

At the focused audit:

- Corollaries 5.9 and 5.10 are closed under the global context.
- Corollary 5.11 depends only on `Classical_Prop.classic` (bounded/unbounded
  finite coordinate case splits).
- state finiteness, transition finiteness, and the packaged finite graph
  depend only on `Classical_Prop.classic`, inherited from the finite-cover
  theorem and finite Prop-level selection.
- no `ClassicalEpsilon`, choice oracle, functional extensionality, UIP/K,
  `Eq_rect_eq`, `Admitted`, `admit`, `Abort`, or new `Axiom` occurs.

## Task 4B handoff (Corollary 5.12)

This task proves finiteness of each graph, not finiteness of the family of
graphs at a fixed system and capacity.  Task 4B still needs:

1. finitely many bounded-coordinate masks;
2. the common special state for a fixed capacity and mask;
3. a uniform bound on states occurring across every valid production triple
   with that capacity, using finite action branching and the antichain result;
4. a verified König/bounded-bad-path argument (or an equivalent WQO theorem);
5. uniform finiteness of all possible labeled transitions;
6. quotienting graph representations extensionally and enumerating the
   resulting finite graph class.

No part of Corollary 5.12 is claimed here.
