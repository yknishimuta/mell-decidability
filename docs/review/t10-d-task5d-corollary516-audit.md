# T10-D Task 5D audit — Leroux Corollary 5.16

## Scope and baseline

- Branch: `work/mell-formalization`
- Baseline: `14eb681cafe0953e2b9c7c80109ed201e99d4639`
- Scope: positive homogeneity of `R_gamma`, the equality
  `Cone(T_c) = union_{gamma in Gamma_c} R_gamma`, finite
  classification of the relations, rational definability, Corollary 5.16,
  and the run-transformer corollary.
- Section 6 and Task 6 are deliberately excluded.

## Construction

`production_kirchhoff_positive_scale` scales endpoints and every exact
graph-edge weight by a strictly positive rational. Nonnegativity, exact
positive support, strict edge positivity, Kirchhoff balance, and displacement
are transported. The theorem intentionally does not accept scale zero.

`capacity_cone_union_kirchhoff` proves both inclusions. Lemma 5.15 gives the
union-to-cone direction. For the converse, denominator clearing for the
periodic capacity relation supplies a positive integer multiple in the
natural relation. That pair forms a valid production triple; Lemma 5.14 puts
the integer pair in its Kirchhoff relation, and positive scaling by the
reciprocal returns the original rational pair.

The finite classification key is the triple

1. a represented production-graph signature,
2. the positive-support mask of `GammaInput`,
3. the positive-support mask of `GammaOutput`.

The bounded-coordinate mask stored by the graph and the two support masks are
kept distinct. Exact NoDup edge lists representing the same signature are
related by `Permutation`; balance, positivity, and displacement are thereby
transported. Equal support masks transport precisely the two support clauses.

The graph catalog can contain unrealized signatures. The representative
theorem therefore performs a finite Prop-level induction over all keys,
selecting one valid production triple only when a key is realized. No
Set-level choice function or executable graph generator is introduced.

The finite representative union is expressed by a finite disjunction of the
already proved `production_kirchhoff_relation_qdefinable` formulas.
`capacity_transformer_cone_qdefinable` transports this formula across the
cone/union equivalence. Combining it with
`capacity_transformer_periodic` proves Corollary 5.16. The existing
finite-composition theorem based on Lemma 5.1 then discharges every capacity
premise of `TransformerAlongRun`.

## Paper correspondence

Leroux Corollary 5.16 states that every capacity transformer is
asymptotically definable. The Coq theorem uses the existing exact definition:

`AsymptoticallyDefinableNRelation R := PeriodicNRelation R /\
QDefinable (RelationConePairs (NRelationAsZ R))`.

Thus its periodic part is Task 2A, its cone equality is Lemmas 5.14 and 5.15
plus positive homogeneity, and its definability part is the finite
graph-and-support classification above. No extra graph catalog, decidability
oracle, or validity premise remains in the public theorem.

## Regression coverage

The audit module checks all public contracts and includes formal regressions
for dimension zero, the empty action system, a dimension-zero run
transformer, strict-positive scaling (including the impossibility of the zero
premise), finite enumeration of both support masks, and a concrete pair of
one-dimensional triples whose input support masks differ.

These regressions supplement the inherited Task 4B/5B/5C coverage for zero
actions, duplicate actions, empty graphs, bounded masks, exact graph
representations, strict Kirchhoff positivity, Lemmas 5.14–5.15, and rational
denominator clearing.

## Verification

- RED/GREEN: the Task 5D audit target was absent before the new modules and
  succeeds after their addition.
- Focused source and regression build: passed via `make audit-t10-d-task5d`.
- Forced full `_CoqProject` rebuild: passed with exit status 0 via
  `opam exec --switch . -- make -B -f Makefile.coq -j2`.
- Kernel validation: focused `coqchk -silent` passed for both Task 5D source
  modules and the Task 5D audit module.
- Forbidden-construction scan: passed for all Task 5D source and audit files.
- Target-only `git diff --check`: passed. Pre-existing audit-log changes and
  untracked vendor files were preserved and excluded from the Task 5D commit.
- Independent review: PASS. It specifically checked the two cone inclusions,
  strict-positive scaling, the graph-plus-two-support-mask classification,
  exclusion of unrealized keys, exact finite disjunction, and the absence of
  residual hypotheses in Corollary 5.16 and the run-transformer theorem.

## Axiom and dependency audit

- No `Admitted`, `admit`, `Abort`, or new `Axiom`.
- No `ClassicalEpsilon`, choice oracle, UIP/K, `Eq_rect_eq`, functional
  extensionality, or external oracle.
- `production_kirchhoff_positive_scale` is closed under the global context.
- The finite representative theorem and its downstream cone-definability
  theorems inherit only `Classical_Prop.classic`. Its use is confined to the
  finite Prop-level realized-key case split and inherited finite graph
  catalog results.

## Task 6 handoff

The public interface available to Section 6 is
`transformer_along_run_asymptotically_definable`, without a run-validity
premise. Task 6 must still formalize Leroux Section 6's minimal-run
decomposition and almost-semilinearity arguments. Corollary 5.16 establishes
asymptotic definability of run transformers; it does not by itself prove the
Section 6 decomposition or a semilinear reachability relation.
