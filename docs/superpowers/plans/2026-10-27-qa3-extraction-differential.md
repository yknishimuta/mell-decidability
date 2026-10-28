# Task QA-3 Extraction Differential Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Establish finite, reproducible agreement between kernel-evaluated Gallina functions and their freshly extracted OCaml counterparts.

**Architecture:** Keep production extraction unchanged.  Pair a closed-equation Audit module with a hand-written extracted-code runner and an explicit expected-result manifest, then wire them into a fail-closed Make target.

**Tech Stack:** Coq 8.20.1, OCaml 4.14.2, Zarith 1.14, Bash, existing extraction and runtime harness.

**Spec:** `docs/superpowers/specs/2026-10-27-qa3-extraction-differential-design.md`

## Global constraints

- Baseline `9aa3c86e61d1dff766857c4217debe61e018b0cc` on `work/mell-formalization`.
- Preserve protected untracked files.
- Do not change public Gallina definitions, theorem statements, reduction, or extraction configuration.
- Do not add packages, extraction overrides, axioms, or oracles.

### Task 1: Fix the comparison contract

**Files:** design, plan, audit table

- [x] Record exact Coq/OCaml function names, types, and callers.
- [x] Select bounded fixtures with explicit expected renderings.
- [x] Classify unavailable branches as NOT APPLICABLE or UNEXECUTED.

### Task 2: Kernel-checked Gallina fixtures

**Files:** `theories/Audit/ExtractionDifferentialExamples.v`, `_CoqProject`

- [x] Add closed examples for codecs and malformed inputs.
- [x] Add valid/invalid RawRun and invariant-checker examples.
- [x] Add Presburger and fast-path examples.
- [x] Add finite stage/fuel and arbitrary-precision arithmetic examples.
- [x] Focused compile and inspect assumptions.

### Task 3: Extracted OCaml differential runner

**Files:** runner, case manifest, required-name manifest

- [x] First run the manifest with missing runner cases and observe failure.
- [x] Implement the same named concrete inputs against extracted modules.
- [x] Compile against freshly generated extraction output.
- [x] Require exact fixture-name set, exact results, and per-case timeout.

### Task 4: Gate and audit report

**Files:** `Makefile`, `docs/review/qa3-extraction-differential-audit.md`

- [x] Add `check-extraction-differential` without changing `Extract.v`.
- [x] Record the function mapping and every fixture classification.
- [x] Record MATCH/MISMATCH/UNEXECUTED totals and trust boundaries.

### Task 5: Full verification and review

- [x] Run focused build and differential gate.
- [x] Run forced full build, validate/coqchk, final extraction/runtime/path gates.
- [x] Recheck staged source scope, assumptions allowlist, extraction policy/output, and diffs.
- [x] Obtain final independent-review disposition after the corrected fixture.
- [x] Explicitly stage only QA-3 files and commit locally.
