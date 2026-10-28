# T10-D Task 6D Corollary 6.3 and Stateful Lift Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove Corollary 6.3 for plain VAS and lift the relation and post results to finite-control VAS without erasing control-state checks.

**Architecture:** Reuse `SemiCode` as the canonical finite linear decomposition of packed source/target relations. Prove projection closure first at the asymptotic-period and almost-semilinear levels, then assemble stateless Corollary 6.3. Define finite-control unary VAS and a two-phase state/gate encoding into a plain VAS of dimension `d + q + |transitions|`; prove exact reach equivalence before transporting semilinear endpoint constraints and reassembling finite state pairs.

**Tech Stack:** Coq 8.20.1, existing `NVec`/`ZVec`, `SemiCode`, rational cone/QDefinable APIs, Task 6C almost-semilinearity, and the state/gate encoding pattern from `Reduction/StateErasure.v`.

**Spec:** User-supplied T10-D Task 6D execution instruction, 2026-10-24.

## Global Constraints

- Preserve branch `work/mell-formalization` and baseline `c3651f6659951e2e4e81daefbefa8ec961d4490a`.
- No new Axiom, `Admitted`, choice oracle, UIP/K, functional extensionality, reset, clean, push, or public-contract weakening.
- Do not stage pre-existing logs, `FaceStrippingBasesExamples.v`, `vendor/presburger/`, or this planning file.
- Use the two-phase state/gate encoding for all transitions, including self-loops.

## Review Focus

- Empty relation/code and dimension/state-count zero remain well typed and vacuous where appropriate.
- Source and target projections preserve the nonnegative `NRelationAsZ` bridge exactly.
- Self-loop transitions cannot bypass their control-state test.
- Encoded reachability has no reachable malformed normal/gate configurations.
- Final stateful union retains both source and target state tags.

---

### Task 1: Packed semilinear relations and finite linear decomposition

**Files:**
- Create: `theories/VAS/SemilinearRelationDecomposition.v`
- Test: `theories/Audit/VASCorollary63StatefulExamples.v`

**Interfaces:**
- Consumes: `SemiCode`, `denote`, `LinearRelationData`, `LinearRelationContains`.
- Produces: `SemilinearNRelation`, pair pack/split correctness, `semilinear_nrelation_finite_linear_decomposition`, stateless reach/intersection almost-semilinearity.

- [ ] Write `Check`/boundary examples first and confirm the source module is missing.
- [ ] Implement exact conversion of each packed `LinearComponent (d+d)` to `LinearRelationData d`.
- [ ] Prove the finite decomposition and assemble Task 6C over the component list.
- [ ] Focused compile and record RED/GREEN.

### Task 2: Projection closure and Corollary 6.3

**Files:**
- Create: `theories/VAS/AlmostSemilinearProjection.v`
- Create: `theories/VAS/Corollary63.v`
- Test: `theories/Audit/VASCorollary63StatefulExamples.v`

**Interfaces:**
- Consumes: `AsymptoticallyDefinableNRelation`, `AlmostSemilinearNRelation`, `qdefinable_projection`.
- Produces: asymptotic source/target projection, almost-semilinear projections, plain post/pre Corollary 6.3.

- [ ] Add failing checks for source/target projection and post/pre contracts.
- [ ] Prove periodicity, cone/projection exchange, and QDefinable transport.
- [ ] Map finite components and prove source/target projection closure.
- [ ] Assemble forward and backward Corollary 6.3 and focused compile.

### Task 3: Finite-control VAS and exact two-phase encoding

**Files:**
- Create: `theories/VAS/StatefulVAS.v`
- Create: `theories/VAS/StatefulEncoding.v`
- Test: `theories/Audit/VASCorollary63StatefulExamples.v`

**Interfaces:**
- Consumes: `PlainVAS`, `PlainVASReach`, one-hot/state-gate arithmetic pattern.
- Produces: `VAS`, `VASReach`, endpoint encodings, forward/backward exact reach equivalence.

- [ ] Add failing examples for self-loop, state change, empty transitions, and unreachable state pairs.
- [ ] Define transitions and operational reach semantics.
- [ ] Define start/finish actions with a dedicated gate per transition.
- [ ] Prove token/classification invariants, matching-finish exclusivity, and exact reach equivalence.
- [ ] Focused compile all boundary examples.

### Task 4: Stateful semilinearity and final public theorems

**Files:**
- Create: `theories/VAS/StatefulAlmostSemilinear.v`
- Test: `theories/Audit/VASCorollary63StatefulExamples.v`

**Interfaces:**
- Consumes: Task 1/2 stateless results and Task 3 exact encoding.
- Produces: `StatefulRelationSemilinear`, `StatefulRelationAlmostSemilinear`, `StatefulSemilinear`, `StatefulAlmostSemilinear`, `vas_reach_relation_inter_semilinear`, `vas_post_inter_semilinear`.

- [ ] Add failing exact public `Check`s.
- [ ] Define finite state-tagged component semantics.
- [ ] Specialize the encoded relation per finite state pair and project counters.
- [ ] Reassemble all state pairs and prove both final contracts.
- [ ] Focused compile and regression.

### Task 5: Audit, full verification, review, and commit

**Files:**
- Create: `docs/review/t10-d-task6d-corollary63-stateful-audit.md`
- Modify: `_CoqProject`
- Modify: `Makefile`

**Interfaces:**
- Consumes: all Task 6D results.
- Produces: reproducible audit target and local commit.

- [ ] Run focused source/regression and public `Check`/`Print Assumptions`.
- [ ] Run forced `_CoqProject` rebuild and `coqchk -silent`.
- [ ] Run forbidden scan and target-only `git diff --check`.
- [ ] Perform a separate final review of contracts, encoding invariants, and assumptions.
- [ ] Stage only Task 6D files, commit locally, and do not push.
