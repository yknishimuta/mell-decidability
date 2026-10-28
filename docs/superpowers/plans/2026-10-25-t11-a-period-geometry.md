# Task 11-A Period Geometry Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the doubled IBVAS relation, transformer and initialized-run periods, and directed-run closed-linearization results corresponding to Lemmas 4.6, 4.10, 4.11, 3.12, and 3.13 of arXiv:2607.09558v1.

**Architecture:** Keep the existing public `IBVAS`, `IRunLe`, periodic/cone, and almost-semilinear APIs unchanged. Add four focused Separator modules: the doubled construction and one-state bridge; transformer and run-period geometry; directed runs; and closed-linearization/inclusion results. Every semantic projection restricts marker and auxiliary coordinates before projection.

**Tech Stack:** Coq/Gallina, repository vector and BVAS APIs, T10 geometry and almost-semilinearity libraries.

**Spec:** User-supplied Task 11-A instruction and arXiv:2607.09558v1 Sections 3–4.

## Global Constraints

- Branch `work/mell-formalization`, baseline `63b241a47081d32a9ad7dc0c7f3495574362e868`.
- Preserve all T06–T10 public contracts and unrelated working-tree files.
- No new axioms, admitted proofs, choice, UIP/K, functional extensionality, or truncating integer-to-natural adapters.
- Do not proceed to Task 11-B.
- Stage only Task 11-A sources, regression, plan, build registration, and audit document; do not push.

## Review Focus

- Marker-total-one is imposed before projection; marker-total-zero/two cannot leak into Lemma 4.6.
- Transformer addition is witnessed by valid run operations, not root-counter monotonicity alone.
- `P_rho` addition uses exact amalgamation and the structural cone equation is proved in both directions.
- Directed-run cone membership retains nonnegative integer offsets and exact subrun occurrences.
- `Q_w` is exactly `ClosedLinearization(P_w)`; neither its difference group nor rational closure is enlarged.

---

### Task 1: Doubled relation and Lemma 4.6

**Files:**
- Create: `theories/Separator/DoubledRelation.v`
- Test: `theories/Audit/SeparatorPeriodGeometryExamples.v`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `IBVAS`, `SReach`, `bvass_reach_inter_semilinear`, coordinate projection closure.
- Produces: `SpecialLeafReach`, `doubled_system`, marker invariants, and the Lemma 4.6 almost-semilinear intersection theorem.

- [ ] Add failing `Check`/examples for the public construction and theorem; compile and confirm missing symbols.
- [ ] Implement vector packing, lifted actions, marker moves, and the one-state SBVAS bridge.
- [ ] Prove the marker-zero and marker-one run characterizations by mutual structural induction.
- [ ] Prove restriction-before-projection and apply Task 6E4 to obtain Lemma 4.6.
- [ ] Focused compile and record theorem assumptions.

### Task 2: Transformer and Lemma 4.10

**Files:**
- Create: `theories/Separator/TransformerPeriod.v`
- Modify: `theories/Audit/SeparatorPeriodGeometryExamples.v`

**Interfaces:**
- Consumes: Lemma 4.6, special-leaf runs, periodic/almost-semilinear relation APIs.
- Produces: `IBVASTransformer`, periodicity, almost semilinearity, and asymptotic definability.

- [ ] Add failing checks for transformer periodicity and asymptotic definability.
- [ ] Prove reflexive/transitive/translation lemmas using explicit valid-run constructions.
- [ ] Prove the lower-bound translation equivalence and almost-semilinearity.
- [ ] Apply the periodic-almost-semilinear bridge and focused compile.

### Task 3: Initialized-run periods and Lemma 4.11

**Files:**
- Extend: `theories/Separator/TransformerPeriod.v`
- Modify: `theories/Audit/SeparatorPeriodGeometryExamples.v`

**Interfaces:**
- Consumes: `IRunLe`, `run_amalgamation`, transformer cone definability, sum/projection cone closure.
- Produces: `IRunPeriod`, periodicity, exact structural decomposition, cone equation, and asymptotic definability.

- [ ] Add failing checks for zero/addition, structural decomposition, and Lemma 4.11.
- [ ] Prove `IRunPeriod` periodic by reflexivity and exact amalgamation.
- [ ] Prove the run/list mutual structural decomposition in both directions.
- [ ] Prove the cone sum/relation/projection equation and structural Q-definability induction.
- [ ] Focused compile and assumptions audit.

### Task 4: Directed runs and Lemma 3.12

**Files:**
- Create: `theories/Separator/DirectedRuns.v`
- Create: `theories/Separator/PeriodGeometry.v`
- Modify: `theories/Audit/SeparatorPeriodGeometryExamples.v`

**Interfaces:**
- Consumes: `IRunPeriod`, finitely-generated rational cones, `periodic_cone_intersection`, and `closed_linearization_finitely_generated`.
- Produces: `DirectedIRun`, its concretization, `DirectedPeriod`, `DirectedClosedPeriod`, target equivalence, and Lemma 3.12.

- [ ] Add failing checks for exact definitions, target equivalence, and finite generation.
- [ ] Prove the rational-cone integer-section periodic/nonnegative properties.
- [ ] Prove `Cone(P_w) = Cone(P_rho) ∩ C_w` and Q-definability.
- [ ] Apply the existing closed-linearization finite-generation theorem and focused compile.

### Task 5: Directed edges and Lemma 3.13

**Files:**
- Extend: `theories/Separator/DirectedRuns.v`
- Extend: `theories/Separator/PeriodGeometry.v`
- Modify: `theories/Audit/SeparatorPeriodGeometryExamples.v`
- Create: `docs/review/t11-a-doubled-period-geometry-audit.md`

**Interfaces:**
- Consumes: exact amalgamation, positional `IRun` context decomposition/lift, and directed periods.
- Produces: directed edge, translated-period inclusion, Lemma 3.13, and mutual-edge/equal-cone equality.

- [ ] Add failing checks for positional subrun lifting and closed-period inclusion.
- [ ] Prove the exact IRun subrun replacement/lift lemma using existing `IContext` decomposition.
- [ ] Prove translated `P_rho` inclusion, then directed-period inclusion.
- [ ] Prove difference and rational-closure inclusions and Lemma 3.13.
- [ ] Run focused regressions, full rebuild, validate/coqchk, prohibited scan, and independent review.
- [ ] Stage only Task 11-A files, verify staged diff, and commit locally.
