# T10-D Leroux VAS Theorem Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the forward post-image half of Leroux 2012 Corollary 6.3 from its Sections 2--6 prerequisites, without importing it as an axiom.

**Architecture:** Define stateful unary VAS runs and Jančar's order, develop capacity transformers and finite production graphs, prove their rational definability through Kirchhoff functions, and derive the finite minimal-run decomposition of a semilinear restriction of the reachability relation.  The source vector-only result is lifted over finitely many source/target control-state pairs; projecting the target configuration then yields the required post-image theorem.

**Tech Stack:** Coq 8.20.1, T10-A closure/definability, T10-C rational geometry interfaces, Kruskal/Dickson adapters.

**Spec:** `docs/review/t10-planning-audit.md`

## Global Constraints

- The direct output is `vas_post_inter_semilinear`; the relation theorem is also public and has the exact audit type.
- Corollary 6.3 is not accepted by citation alone: Sections 2--6 listed in the audit are proof obligations.
- Sections 7--9 of Leroux 2012 are outside T10-D.
- Finite control states are preserved.  The source vector-only Corollary 6.3 is lifted by a finite disjoint union over state pairs, not by silently forgetting states.

## Review Focus

- Runs whose minimal capacity has zero in only some coordinates.
- Composition of transformer relations with an empty intermediate fibre.
- Positive integer realization of a rational Kirchhoff circulation.
- Minimal-run finiteness under the combined Jančar/period order.
- Projection of the relation after, not before, intersection with `X × Y`.

---

### Task 1: VAS semantics and Jančar order

**Files:**
- Create: `theories/VAS/Runs.v`
- Create: `theories/Audit/VASStatements.v`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `NVec`, `ZVec`, `add_displacement`, Kruskal list WQO.
- Produces: `VAS`, `VASRun`, `ValidVASRun`, `VASReach` with explicit source/target states, `vas_run_order`, Lemma 4.1 WQO/well-founded minimality interface.

- [ ] **Step 1: RED.** Add failing exact `Check` commands for both final public theorems and Lemma 4.1.
- [ ] **Step 2: Implement VAS runs.** Preserve finite control state and every intermediate nonnegative configuration.
- [ ] **Step 3: Implement Jančar order.** Include source/target/capacity and action-word embedding conditions exactly as Section 4.
- [ ] **Step 4: Prove Lemma 4.1.** Derive the required WQO/minimal-element finiteness and test unary negative updates.
- [ ] **Step 5: GREEN and commit.** Run focused checks and commit the runs/order unit.

### Task 2: Transformer relations and intraproductions

**Files:**
- Create: `theories/VAS/Transformer.v`
- Modify: `theories/Audit/VASStatements.v`, `_CoqProject`

**Interfaces:**
- Consumes: VAS runs/order, `NPeriodic`, rational cones/definability.
- Produces: capacity transformer, run transformer, asymptotic definability predicates, Leroux Lemmas 5.1, 5.2, 5.5, 5.6, 5.7.

- [ ] **Step 1: RED.** State the five source lemmas; demonstrate that periodicity alone does not imply asymptotic definability.
- [ ] **Step 2: Prove composition and periodicity.** Preserve capacity offsets and nonnegative intermediates.
- [ ] **Step 3: Prove intraproduction closure/realization.** Lemma 5.6 must construct a genuine cycle effect; Lemma 5.7 must be strictly positive exactly outside `I_gamma`.
- [ ] **Step 4: GREEN and commit.** Test zero/unbounded coordinate mixtures and commit.

### Task 3: Finite production graphs and Kirchhoff relations

**Files:**
- Create: `theories/VAS/ProductionGraph.v`
- Modify: `theories/VAS/Transformer.v`, `theories/Audit/VASStatements.v`, `_CoqProject`

**Interfaces:**
- Produces: `ProductionGraph`, projected bounded state set, Corollary 5.12, Kirchhoff function, Lemmas 5.14--5.15, Corollary 5.16.

- [ ] **Step 1: RED.** Exhibit why merely knowing the action alphabet is finite does not make the projected state set finite.
- [ ] **Step 2: Prove bounded projection finiteness and state incomparability.** Track Lemmas 5.5--5.7 at every use.
- [ ] **Step 3: Prove graph-class finiteness.** Include all finite control/action labels.
- [ ] **Step 4: Prove Kirchhoff soundness/completeness.** Clear rational denominators and realize a positive integer cycle instead of assuming a circulation is executable.
- [ ] **Step 5: GREEN and commit.** Run graph/cycle examples and commit.

### Task 4: Almost-semilinear reachability relation and Corollary 6.3

**Files:**
- Create: `theories/VAS/AlmostSemilinear.v`
- Modify: `theories/Audit/VASStatements.v`, `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: T10-A semilinear products/intersections/projections and transformer theorem.
- Produces: Lemma 6.1 decomposition, Lemma 6.2 intersection closure, `vas_reach_relation_inter_semilinear`, `vas_post_inter_semilinear`.

- [ ] **Step 1: RED.** State both public theorems and record the missing minimal-run decomposition.
- [ ] **Step 2: Prove Lemma 6.1.** Decompose by finitely many minimal runs and the intersection of each run transformer with the finitely generated period.
- [ ] **Step 3: Prove Lemma 6.2.** Establish the exact cone equality used for intersection and its definability.
- [ ] **Step 4: Lift finite control and derive Corollary 6.3 forward.** Prove the vector-only result for each source/target state pair, take their finite union, form `R=X×Y`, intersect the reachability relation, then project the target configuration.
- [ ] **Step 5: Verify.** Run `make check-t10-d`, `make audit-t10-d`, `coqchk`, full `Check`, and `Print Assumptions`.
- [ ] **Step 6: Independent review.** Reviewer maps every dependency to Sections 2--6 and confirms no citation-only axiom or hidden module hypothesis.
- [ ] **Step 7: Commit.** Commit only D files as `feat(t10-d): prove Leroux forward VAS theorem`.
