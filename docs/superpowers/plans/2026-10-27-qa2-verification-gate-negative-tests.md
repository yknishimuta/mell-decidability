# Task QA-2 Verification-Gate Negative Tests Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove by isolated fault injection that the final build, audit, extraction, runtime, timeout, and scope-completeness gates fail closed.

**Architecture:** Add small verification-only shell checkers and a disposable-clone negative-test driver.  Harden existing Make targets only where a negative test demonstrates a detection gap; do not alter Gallina computation or theorem statements.

**Tech Stack:** Bash, GNU/BSD core tools, Git local clone, Coq 8.20.1, OCaml 4.14.2, Zarith 1.14, existing Make/opam switch.

**Spec:** `docs/superpowers/specs/2026-10-27-qa2-verification-gate-negative-tests-design.md`

## Global Constraints

- Branch `work/mell-formalization`, baseline `87ecb68038a2a1eba2af1a3e206ab4eff59ef3cb`.
- Fault injection occurs only in a disposable clone.
- Preserve `.nra.cache` and `theories/Audit/FaceStrippingBasesExamples.v`.
- Do not modify mathematical sources, public APIs, reduction, or decision semantics.
- No reset, clean, add-A, push, tag, or release.

## Review Focus

- A piped failing `coqc` must remain nonzero.
- `coqchk` success must not hide a newly introduced axiom.
- Every tracked `.v` must occur exactly once in `_CoqProject` and produce `.vo` evidence.
- Runtime omission, crash, timeout, and expectation mismatch must all fail.
- Extraction outputs must be freshly regenerated before compilation.

---

### Task 1: Scope-completeness checker

**Files:**
- Create: `scripts/check-verification-scope.sh`
- Modify: `Makefile`

- [x] Write isolated RED checks for an omitted manifest entry and orphan source.
- [x] Implement tracked/registered equality and required Audit-module checks.
- [x] Add optional `.vo` completeness and `.vos`-only rejection.
- [x] Confirm baseline PASS, fault FAIL, recovery PASS.

### Task 2: Runtime and timeout hardening

**Files:**
- Modify: `Makefile`

- [x] Demonstrate that removing a runtime case is not currently counted.
- [x] Add exact 22-case counting and per-case timeout handling.
- [x] Inject flipped YES, flipped NO, omission, crash, and hang faults.
- [x] Confirm every fault is nonzero and restoration passes.

### Task 3: Extraction freshness and trust checks

**Files:**
- Modify: `Makefile`

- [x] Demonstrate the stale-output risk with a sentinel.
- [x] Clear ignored extraction output and force `Extract.v` recompilation.
- [x] Reject unrealized axioms and unapproved extraction directives.
- [x] Confirm fresh extraction and OCaml compilation after restoration.

### Task 4: Disposable-clone negative-test driver

**Files:**
- Create: `scripts/audit-verification-gates.sh`
- Modify: `Makefile`

- [x] Validate the temporary clone boundary and pinned-switch link.
- [x] Implement baseline/fault/recovery orchestration for the full matrix.
- [x] Record exact exit codes and diagnostic excerpts.
- [x] Add the opt-in `audit-verification-gates` target.

### Task 5: Audit report and final verification

**Files:**
- Create: `docs/review/verification-gate-negative-tests.md`

- [x] Record every injection, exit code, message, correction, and recovery.
- [x] Run focused, forced full, validate/coqchk, final audit/extraction/runtime/path gates.
- [x] Run forbidden scans, diff checks, and independent review.
- [x] Explicitly stage only QA-2 verification settings, scripts, plan, and report; commit locally.
