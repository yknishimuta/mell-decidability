# Task 11-D Face-Stripping Integration Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Verify and package the existing Section 6 face-stripping development as Task 11-D, with explicit regressions for corrections R07--R09.

**Architecture:** Reuse the kernel-checked T10-C geometry modules as the canonical implementation. Add one focused audit module that checks the complete public interfaces and exercises the corrected extract order, signed-vector carrier, difference-based Lemma 6.10 path, zero-based face indices, and diagonal direction. Add a Task 11-D audit record; do not refactor the established proof chain.

**Tech Stack:** Coq, project `ZVec`/`QVec` geometry APIs, Kruskal almost-full library, `Makefile.coq`, `coqchk`.

**Spec:** User-supplied Task 11-D specification in this conversation.

## Global Constraints

- Preserve all Task 11-A--C and T10-C public contracts.
- Work over `ZSet d`; do not replace signed sets by `NSet d`.
- Preserve fullness as `Q = (Q-Q) intersect Cone(Q)`.
- Apply R07 (differences, not sequence membership in Q), R08 (excluded then remaining), and R09 (later-to-earlier diagonal direction with actual zero-based indices).
- No new axioms, admitted obligations, choice oracle, UIP/K, or functional extensionality.
- Do not edit or stage the protected `FaceStrippingBasesExamples.v` or unrelated artifacts.

## Review Focus

- `ExtractFace period face excluded remaining`, never the reversed arguments.
- Lemma 6.10 uses differences/translated normalization and does not infer raw sequence elements belong to the period.
- Minimum face is cone lineality, not necessarily `{0}`.
- Theorem 6.1 gives complete, disjoint, finitary slices and finitary remainders.
- Lemma 6.3 forbids later-to-earlier edges only; the converse direction remains possible.

### Task 1: Contract and correction regressions

**Files:**
- Create: `theories/Audit/FaceStrippingSection6Examples.v`
- Modify: `_CoqProject`

**Interfaces:**
- Consumes: existing T10-C face geometry and stripping theorems.
- Produces: executable checks for R07--R09 and all Task 11-D public contracts.

- [x] Add the R08 regression and observe focused compilation fail before its proof exists.
- [x] Prove the correct extract contains zero and the reversed extract does not.
- [x] Check the direct difference/fullness helpers used by Lemma 6.10.
- [x] Reuse concrete diagonal regressions showing the forbidden and permitted directions.
- [x] Add exact `Check` and `Print Assumptions` commands for the principal results.
- [x] Register and focused-compile the audit module.

### Task 2: Task audit and full verification

**Files:**
- Create: `docs/review/t11-d-face-stripping-audit.md`

**Interfaces:**
- Consumes: Task 1 evidence and existing theorem implementations.
- Produces: source correspondence, trust-boundary, regression, and Git record.

- [x] Record exact public types and the R07--R09 mapping.
- [x] Run T10-C, Task 11-A--C, and focused regressions.
- [x] Force the full `_CoqProject` rebuild and run `validate`/`coqchk`.
- [x] Run forbidden-construct and whitespace scans.
- [x] Obtain independent read-only review.
- [x] Stage only Task 11-D files and create the requested local commit.
