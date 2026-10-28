# T10-D Task 5B Kirchhoff Relation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize Leroux's rational Kirchhoff relation for a production graph, prove FO(Q,+,≤) definability and representation independence, and prove Lemma 5.14.

**Architecture:** Fix an exact NoDup production-edge list, define the semantic relation with strictly positive rational edge weights, and compile it to a finite linear formula whose existential variables are indexed by edge positions. Prove list-permutation invariance, then package the representation-independent relation. Construct Lemma 5.14 from projected Omega runs covering every real edge, normalize the resulting integral Parikh flow by the positive common multiplier, and stop before any graph-cycle-to-VAS-run lift.

**Tech Stack:** Rocq/Coq, existing `QFormula`/`QDefinable`, production graph and Kirchhoff modules.

**Spec:** User-provided T10-D Task 5B contract.

## Global Constraints

- Preserve all public APIs through Task 5A.
- Use at most `Classical_Prop.classic`; no choice oracle or new axiom.
- Strictly positive weights and bidirectional positive-support equality are mandatory.
- Graph cycles are not VAS runs.
- Stop before Lemma 5.15 and Corollary 5.16.

## Review Focus

- Empty edge lists and dimension zero still produce closed formulas.
- Duplicate action labels with different endpoints retain separate weight variables.
- Qeq, not Leibniz equality, governs rational vector equality and sums.
- Edge-list permutation and Lemma57 witness changes do not change the relation.
- Lemma 5.14 uses multiplier `1 + sum n_j`, so normalization never divides by zero.

---

### Task 1: Semantic relation and support API

**Files:** Create `theories/VAS/KirchhoffRelation.v`; test in `theories/Audit/VASKirchhoffRelationExamples.v`.

**Interfaces:** Produce `ExactProductionGraphEdges`, `NonnegativeQVec`, `SamePositiveSupport`, `KirchhoffRelationForEdges`, finite-weight equivalence and permutation invariance.

- [ ] Write RED checks for the required names and strict-support counterexamples.
- [ ] Implement definitions and Qeq/extensionality lemmas.
- [ ] Implement list-indexed weight conversion and exact NoDup edge adapter.
- [ ] Prove permutation invariance of balance, positivity, and displacement.
- [ ] Focused build GREEN.

### Task 2: Finite FO(Q,+,≤) compiler

**Files:** Create `theories/VAS/KirchhoffDefinability.v`; extend audit regression.

**Interfaces:** Produce `kirchhoff_relation_for_edges_qdefinable` and representation-independent definability.

- [ ] Write RED checks for both definability theorems.
- [ ] Compile nonnegativity, exact support, positivity, balance, and displacement into a finite conjunction under `length edges` existentials.
- [ ] Prove closure and semantic correctness, including zero variables/coordinates.
- [ ] Use exact-edge independence to fix one Prop-level representation for `ProductionKirchhoffRelation`.
- [ ] Focused build GREEN.

### Task 3: Omega coverage and Lemma 5.14

**Files:** Create `theories/VAS/KirchhoffLemma514.v`; extend audit regression.

**Interfaces:** Produce `production_graph_total_cycle_scaled_gamma_displacement` and `lemma_5_14_gamma_in_kirchhoff_relation`.

- [ ] Write RED checks for coverage-cycle and Lemma 5.14 names.
- [ ] Project each transition's witnessing Omega run to an edge trace containing that edge.
- [ ] Concatenate the basic multiplier-one cycle and all per-edge cycles.
- [ ] Prove totality and displacement `n*(y-x)` with `n>0`.
- [ ] Divide integral Parikh weights by `n`; prove rational balance, positivity, displacement, and exact supports.
- [ ] Focused build GREEN.

### Task 4: Verification and handoff

**Files:** Modify `_CoqProject`, `Makefile`; create `docs/review/t10-d-task5b-kirchhoff-relation-audit.md`.

- [ ] Run focused regression, full `_CoqProject`, `coqchk`, Check/Print Assumptions, scans, and diff checks.
- [ ] Obtain an independent review focused on relation completeness, finite quantification, independence, and multiplier arithmetic.
- [ ] Commit target files only; do not push.
