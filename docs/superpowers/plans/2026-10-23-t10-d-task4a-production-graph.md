# T10-D Task 4A Production Graph Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Formalize Leroux Corollaries 5.9--5.11 and finite existence of each production graph, without implementing Corollary 5.12 or Kirchhoff functions.

**Architecture:** Keep a Lemma 5.7 witness explicit. Define a zero-mask projection, Ω-run-certified edges, and an inductive action-word path relation. Prove the geometric results first, then derive finite state and transition lists from the existing restricted WQO finite-cover theorem.

**Tech Stack:** Coq 8.20, existing Mell VAS/WQO libraries.

---

## Task 1: Projection and graph state/transition interfaces

**Files:** Create `theories/VAS/ProductionGraph.v`; create RED checks in `theories/Audit/VASProductionGraphExamples.v`.

- Write failing `Check` tests for projection, witness predicate, graph states, adjacency, and transitions.
- Implement `ProjectBounded`, `Lemma57Witness`, `ProductionGraphState`, `RunAdjacentStep`, and `ProductionGraphTransition`.
- Prove projection coordinate laws, state endpoints, transition endpoint/action correctness, and witness independence.
- Focused compile both files.

## Task 2: Graph paths and Corollaries 5.9--5.10

**Files:** Create `theories/VAS/ProductionGraphPaths.v`; extend audit checks.

- Write failing checks for path reflexivity/append/split and Ω projection.
- Implement action-word-indexed `ProductionGraphPath` and run projection.
- Prove Ω endpoints project to the special state and every Ω run gives a special cycle preserving its action word.
- Split projected Ω paths at an occurrence and prove strong connectivity.
- Focused compile.

## Task 3: Corollary 5.11 and individual graph finiteness

**Files:** Extend `ProductionGraph.v`; extend audit checks.

- Write failing checks for antichain, finite state list, finite transition list, and combined existence.
- Prove a uniform multiplier lemma using a finite coordinate maximum.
- Prove projected-state antichain via Lemmas 5.5--5.7.
- Apply restricted WQO finite cover to enumerate states exactly.
- Enumerate the finite state/action/state product and select transitions in Prop using `classic`.
- Prove graph independence from any two valid Lemma 5.7 witnesses.

## Task 4: Regressions, audit, and commit

**Files:** Complete audit examples; create `docs/review/t10-d-task4a-production-graph-audit.md`; minimally update `_CoqProject` and `Makefile`.

- Cover dimension zero, bounded/unbounded/mixed systems, empty/zero/duplicate/mixed-sign actions, capacity dip, empty/nonempty cycles, connectivity, antichain, finite lists, and witness independence. Attempt Examples 5.3/5.8 only if compact.
- Run focused audit, full `_CoqProject`, `coqchk -silent`, assumptions and forbidden scans, and target diff check.
- Obtain independent review focused on Ω-step certification, no reverse lift, finite existence vs executable generation, and witness independence.
- Stage only Task 4A files and commit locally; do not push.

## Review Focus

- Every graph edge is certified by an adjacent step in one Ωγ run.
- Paths are only projected from runs in the proved direction.
- Corollary 5.11 uses Lemmas 5.5--5.7, not finiteness circularly.
- State/transition finiteness is existential and introduces no selector.
- All witness-independence claims use only the common zero-coordinate mask.
