# T10-D Task 5A Kirchhoff and Euler Cycles Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize finite production-graph edge traces, Parikh/Kirchhoff laws, and exact realization of positive integral Kirchhoff weights by an Euler cycle.

**Architecture:** Add three focused VAS modules. `GraphParikh.v` owns connected edge traces and exact edge counts. `Kirchhoff.v` owns natural/rational flow balance and action displacement. `EulerCycles.v` proves a generic finite directed-multigraph Euler theorem by a decreasing unused-multiplicity measure, then specializes it to exact represented production graphs.

**Tech Stack:** Coq 8.20.1, stdlib lists/vectors/QArith, existing `Mell.VAS.ProductionGraph*` APIs.

**Spec:** User task “T10-D Task 5A: Kirchhoff functions and Euler cycles”.

## Global Constraints

- Preserve every T01–Task 4B public contract.
- No new axiom, admitted proof, choice oracle, functional extensionality, or Euler oracle.
- The Euler result is a graph-cycle theorem only; it does not lift the cycle to a VAS run.
- Stop before Lemmas 5.14–5.15 and Corollary 5.16.
- Stage and commit only Task 5A source, regression, audit, and minimal build-list changes.

## Review Focus

- Parikh counts distinguish edges with equal actions but different endpoints.
- Self-loops contribute once to both incoming and outgoing flow.
- Euler realization matches every requested multiplicity exactly, not merely positively.
- Strong connectivity is used and is not inferred from balance.
- Empty-edge graphs admit the empty root cycle.

---

### Task 1: Edge traces and Parikh counts

**Files:**
- Create: `theories/VAS/GraphParikh.v`
- Create: `theories/Audit/VASKirchhoffExamples.v`

**Interfaces:**
- Consumes: `ProductionGraphEdge`, `ProductionGraphTransition`, `ProductionGraphPath`.
- Produces: `GraphEdgeTrace`, `ProductionGraphEdgeTrace`, `GraphEdgeParikh`, `GraphCycle`, `TotalGraphCycle` and append/split/path/action/count laws.

- [ ] Add RED `Check` statements for the public API and confirm the audit file fails.
- [ ] Implement connected edge traces and exact edge equality/counting.
- [ ] Prove empty/cons/append/split, action-word, path-conversion, and positivity/totality laws.
- [ ] Focused compile source and audit.

### Task 2: Kirchhoff balance and displacement

**Files:**
- Create: `theories/VAS/Kirchhoff.v`
- Modify: `theories/Audit/VASKirchhoffExamples.v`

**Interfaces:**
- Consumes: Task 1 Parikh functions and existing `ZVec`/`QVec` arithmetic.
- Produces: `KirchhoffBalanceNat`, `KirchhoffBalanceQ`, `KirchhoffDisplacementNat`, `KirchhoffDisplacementQ`, algebraic closure, `graph_cycle_parikh_kirchhoff`, and displacement equality.

- [ ] Extend RED checks and confirm failure on missing definitions.
- [ ] Define finite outgoing/incoming weighted sums and action displacement.
- [ ] Prove additive/scalar laws with `Qeq` for rational statements.
- [ ] Prove closed-trace balance, Parikh/action displacement, and positivity of total cycles.
- [ ] Focused compile source and audit.

### Task 3: Exact Euler realization

**Files:**
- Create: `theories/VAS/EulerCycles.v`
- Modify: `theories/Audit/VASKirchhoffExamples.v`

**Interfaces:**
- Consumes: exact finite state/edge lists, Task 2 balance, graph strong connectivity.
- Produces: `positive_kirchhoff_euler_total_cycle` and `production_graph_positive_kirchhoff_realized`.

- [ ] Extend RED checks and confirm failure on the two public theorems.
- [ ] Define the remaining-multiplicity operations and prove strict decrease of total unused count.
- [ ] Formalize Hierholzer cycle construction/splicing and exact Parikh realization.
- [ ] Specialize using exact Task 4A finite lists and strong connectivity.
- [ ] Focused compile source and audit.

### Task 4: Verification and handoff

**Files:**
- Modify: `_CoqProject`
- Modify: `Makefile`
- Create: `docs/review/t10-d-task5a-kirchhoff-euler-audit.md`

**Interfaces:**
- Consumes: Tasks 1–3.
- Produces: reproducible audit target and Task 5B handoff.

- [ ] Add dimension-zero, empty graph, self-loop, cycle, equal-action/different-edge, imbalance, non-strongly-connected, and exact-weight regressions.
- [ ] Run focused build, full `_CoqProject`, `coqchk -silent`, `Check`, `Print Assumptions`, forbidden scan, and diff checks.
- [ ] Obtain independent review emphasizing exact multiplicity, connectivity, and graph/run separation.
- [ ] Stage only authorized files and make one local commit.
