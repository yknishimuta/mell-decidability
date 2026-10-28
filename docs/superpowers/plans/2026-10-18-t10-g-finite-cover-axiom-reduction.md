# T10-G Finite-Cover Axiom Reduction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove `ClassicalEpsilon.constructive_indefinite_description` from the two public T09 finite-cover theorems without changing their statements.

**Architecture:** Leave the arbitrary-type generic theorem available but stop using it in public concrete results.  Enumerate encoded stateless runs and encoded strong stateful decorated runs, decide validity/order, choose least escaping codes by constructive natural-number search, and contradict the existing AF theorems.  Weaken the strong stateful finite cover to `ContextOrder` through the existing one-way bridge.

**Tech Stack:** Coq 8.20.1, existing codecs/search, T09 WQOs, Kruskal AF, constructive natural-number epsilon.

**Spec:** `docs/review/t10-planning-audit.md`

## Global Constraints

- The complete public types of `irun_le_finite_cover` and `context_order_finite_cover` are immutable.
- Do not replace the result by a computable basis generator; such a generator is neither needed nor generally available.
- Do not replace the removed assumption with UIP/K, a new choice axiom, or an oracle.

## Review Focus

- Codec completeness for every valid run, including `d=0`, `q=0` vacuity, and duplicate children.
- Decidability of validity and `IRunLe`/strong decorated comparison.
- Least-code search uses a decidable predicate and the closed constructive nat-search theorem.
- Stateful weakening is only strong relation implies genuine `ContextOrder`.
- Extracted decision code remains unchanged modulo proof erasure.

---

### Task 1: RED dependency localization

**Files:**
- Create: `theories/Audit/FiniteCoverAssumptions.v`
- Modify: `Makefile`, `_CoqProject`

**Interfaces:**
- Consumes: current finite-cover theorems.
- Produces: a reproducible baseline log that expects exactly `classic` and `constructive_indefinite_description` for both covers.

- [ ] **Step 1: Record baseline.** Run `Print Assumptions` for the generic theorem and both concrete theorems.
- [ ] **Step 2: Add RED gate.** Make `audit-t10-g` fail while either concrete theorem contains `ClassicalEpsilon.constructive_indefinite_description`.
- [ ] **Step 3: Commit.** Commit the audit-only RED gate if the repository remains buildable; otherwise keep it in the implementation commit.

### Task 2: Countable decidable finite-cover lemma

**Files:**
- Create: `theories/Order/CountableFiniteBasis.v`
- Modify: `theories/BVAS/Code.v`
- Create: `theories/BVASS/Code.v`
- Modify: `_CoqProject`

**Interfaces:**
- Consumes: natural codecs, `constructive_indefinite_ground_description_nat`, `af`.
- Produces: complete run encodings, validity decision procedures, decidable `IRunLe` and strong stateful comparison, specialized countable-AF finite-cover theorem.

- [ ] **Step 1: Prove codec completeness.** Every concrete valid run must be decoded from some natural number; proofs stored in records are not compared as runtime data.
- [ ] **Step 2: Prove decidability.** Reflect validity/order propositions with Boolean functions and correctness iff theorems.
- [ ] **Step 3: Build escaping sequence by least-code search.** The only informative existence elimination is constructive search over a decidable natural predicate.
- [ ] **Step 4: Contradict AF.** Reuse `irun_le_wqo` and `strong_srun_le_wqo`; do not assume dependent choice.
- [ ] **Step 5: GREEN focused tests.** Cover invalid codes, leaf runs, permutations, duplicate states, and zero dimension.

### Task 3: Reprove public covers and verify trust/extraction

**Files:**
- Modify: `theories/Order/FiniteBasis.v`
- Modify: `theories/Audit/FiniteCoverAssumptions.v`, `Makefile`

**Interfaces:**
- Produces unchanged `irun_le_finite_cover` and `context_order_finite_cover`.

- [ ] **Step 1: Reprove stateless cover.** Instantiate the countable theorem with valid runs and `IRunLe`.
- [ ] **Step 2: Reprove stateful cover.** Cover by the decidable strong relation, then map comparisons through `ordered_embed_implies_context_insert`.
- [ ] **Step 3: GREEN assumptions.** `Print Assumptions` for both public theorems must omit `ClassicalEpsilon.constructive_indefinite_description`; separately report whether `classic` remains.
- [ ] **Step 4: Regression.** Run `make check-bridges`, `make audit-bridges`, T06 repair checks, `make audit-t10-g`, and `coqchk` for all touched modules.
- [ ] **Step 5: Extraction comparison.** Re-run conditional decision extraction and confirm no axiom stub/oracle appears and no executable definition changed unexpectedly.
- [ ] **Step 6: Independent review.** Reviewer checks unchanged theorem types, no disguised choice principle, codec completeness, and the one-way strong-to-context step.
- [ ] **Step 7: Commit.** Explicitly stage only G files and commit `refactor(t10-g): remove choice from concrete finite covers`.
