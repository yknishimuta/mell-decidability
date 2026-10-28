# Task QA-1 Decision-Path Audit Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Kernel-check and runtime-audit the exact optimized MELL dispatch and its complete certificate-search fallback without changing the public decision API.

**Architecture:** Add an Audit-only traced dispatcher composed from the existing fast checks and fallback, then prove direct structural equality with `mell_decide`.  Observe extracted branch guards through the handwritten runner and keep path coverage separate from semantic correctness.

**Tech Stack:** Coq 8.20.1, OCaml 4.14.2, Zarith 1.14, existing extraction and native runner.

**Spec:** `docs/superpowers/specs/2026-10-27-t12-decision-path-audit-design.md`

## Global Constraints

- Branch `work/mell-formalization`, baseline `fceedd1e9d2a06d628e1c8bb30075dcd6037ba3b`.
- Preserve existing public definitions and theorem types.
- Preserve `.nra.cache` and `theories/Audit/FaceStrippingBasesExamples.v`.
- Do not import the new Audit modules from Decision, Reduction, or extraction computation modules.
- Add no axiom, oracle, extraction override, or special-case decision branch.
- Stage only explicit QA-1 files; do not push, tag, or release.

## Review Focus

- Goal saturation accepts only `Some true`; other results must continue to full saturation.
- Full saturation NO must require a proved fixed point, not exhausted fuel.
- `None` must reach complete search and never become NO.
- Fallback must enumerate RawRun and SemiCode certificates fairly.
- Runtime path labels must be derived from actual extracted guards, not guessed from expected answers.

---

### Task 1: Freeze public call graph and theorem contracts

**Files:**
- Create: `theories/Audit/DecisionPathExamples.v`
- Modify: `_CoqProject`

- [x] Add complete `Check` statements for public, fast-path, stage, search, and fallback declarations.
- [x] Record exact transparent definitions and extraction entry points.
- [x] Register the Audit modules in dependency order.

### Task 2: Kernel-checked dispatch trace

**Files:**
- Create: `theories/Audit/DecisionPathAudit.v`
- Modify: `theories/Audit/DecisionPathExamples.v`

- [x] Define only the five executable `DecisionPath` constructors.
- [x] Define `traced_mell_decide` from existing branch functions.
- [x] Prove `snd (traced_mell_decide Gamma) = mell_decide Gamma` structurally.
- [x] Prove exact branch-guard implications and traced-result soundness.
- [x] Add representative computations where feasible; record full-saturation and terminating MELL fallback as runtime-unobserved.

### Task 3: Standalone complete fallback audit

**Files:**
- Modify: `theories/Audit/DecisionPathAudit.v`
- Modify: `theories/Audit/DecisionPathExamples.v`

- [x] Prove reference-stage YES/NO soundness through `bvas_stage_sound` and `reduce_mell_correct`.
- [x] Prove fallback-stage eventual success from run completeness and `singleton_separator`.
- [x] Prove reference finite-fuel soundness and eventual success.
- [x] Prove fallback decision and successful public finite-fuel results agree with `mell_decide` semantically.

### Task 4: Extracted runtime path observation

**Files:**
- Modify: `docs/review/extraction/final_runner.ml`
- Modify: `Makefile`

- [x] Add path-reporting modes using the extracted branch functions in their real priority order.
- [x] Add a dedicated bounded path-coverage target without changing the existing 22-case gate.
- [x] Observe each practical fast path and BVAS fallback YES/NO enumeration.
- [x] Bound the practical MELL fallback attempt and report unobserved paths honestly.

### Task 5: Audit report and verification

**Files:**
- Create: `docs/review/t12-decision-path-audit.md`
- Modify: `theories/Audit/DecisionPathExamples.v`

- [x] Record exact call graph, theorem types, assumptions, and branch table.
- [x] Classify all existing 22 cases as VERIFIED/OBSERVED/UNOBSERVED as applicable.
- [x] Record Coq/extracted OCaml correspondence and trust boundaries.
- [x] Run focused/full builds, validate/coqchk, all final gates, and the new path gate.
- [x] Scan forbidden constructs, extraction oracles, reverse imports, and diffs.
- [x] Obtain independent review; explicitly stage QA-1 files and create a local commit after final diff inspection.
