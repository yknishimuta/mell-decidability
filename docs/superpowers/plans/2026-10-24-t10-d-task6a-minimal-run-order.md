# T10-D Task 6A Minimal Run Order Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the finitely generated linear relation, refined Jančar run order, decorated-run WQO, and finite cover needed immediately before Leroux Lemma 6.1.

**Architecture:** Encode one period pair with one fixed-length coefficient vector shared by input and output generators. Put valid runs in a subtype and pair them with coefficients; restrict the product of the existing Jančar WQO and Dickson WQO to coefficient representations consistent with the linear component. Project the resulting finite subtype cover back to runs without globally selecting coefficient representations.

**Tech Stack:** Rocq/Coq, project `NVec`/VAS APIs, Coq-Kruskal Prop `af`/`afs`, existing classical finite-cover theorem.

**Spec:** User task “T10-D Task 6A: 線形関係上のrun順序と有限基底” (2026-10-24).

## Global Constraints

- Preserve all public APIs through Task 5D.
- Do not prove Lemma 6.1, Lemma 6.2, Corollary 6.3, or later Section 6 results.
- No new axioms, admitted proofs, choice oracle, functional extensionality, or reachability decider.
- Only `Classical_Prop.classic` inherited through finite-cover extraction is permitted.
- Preserve all existing audit logs, `FaceStrippingBasesExamples.v`, and `vendor/presburger/`.

## Review Focus

- Jančar comparability without a generated-period direction increment must not imply `LinearRunLe`.
- One run may have multiple coefficient representations; no uniqueness or global selection may be assumed.
- Empty generator lists and dimension zero must retain reflexivity and finite coverage.
- Transitivity must add generated pairs using the same coefficient-vector semantics.
- The transformer witness must use exactly the period increment appearing in `LinearRunLe`.

---

### Task 1: Linear relation and refined order

**Files:**
- Create: `theories/VAS/LinearReachRelation.v`
- Test: `theories/Audit/VASMinimalRunExamples.v`

**Interfaces:**
- Consumes: `NVec`, `VASRun`, `ValidVASRun`, `JancarRunLe`.
- Produces: `LinearRelationData`, generated pairs, `LinearOmegaRun`, `LinearRunLe`, reflexivity/transitivity and preservation lemmas.

- [ ] Write audit `Check` statements and boundary examples; verify RED because the module/names do not exist.
- [ ] Implement coefficient evaluation, zero/add/difference lemmas, linear membership, omega, and refined order.
- [ ] Build source and audit; verify GREEN.

### Task 2: Decorated-run WQO and finite cover

**Files:**
- Create: `theories/VAS/MinimalRunFiniteBasis.v`
- Modify: `theories/Audit/VASMinimalRunExamples.v`

**Interfaces:**
- Consumes: Task 1 order, `jancar_run_wqo`, `nvec_le_almost_full`, `af_product`, `restricted_af_finite_cover_classic`.
- Produces: decorated carrier/predicate/order, `decorated_linear_run_wqo`, `decorated_linear_run_finite_cover`, `linear_omega_finite_cover`.

- [ ] Add failing checks for all three public finite-basis theorems.
- [ ] Implement subtype product WQO and Prop-only finite cover.
- [ ] Project the decorated basis to runs and build focused tests.

### Task 3: Transformer-period bridge and audit

**Files:**
- Modify: `theories/VAS/LinearReachRelation.v`
- Modify: `theories/Audit/VASMinimalRunExamples.v`
- Create: `docs/review/t10-d-task6a-minimal-run-order-audit.md`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `jancar_run_le_transformer` and exact source/target period equations.
- Produces: `linear_run_le_transformer_period_witness` and Task 6B handoff.

- [ ] Add a failing contract check and negative regression separating Jančar and period conditions.
- [ ] Prove exact transformer-offset alignment by natural-vector cancellation.
- [ ] Run focused build, assumptions, coqchk, forbidden scan, forced full rebuild, independent review, target-only diff check, and commit only Task 6A files.
