# C4-3D1 Face-Stripping Finite Recursion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define and verify the finite, zero-based face-stripping recursion used before Lemma 6.11.

**Architecture:** A `nat`-recursive remainder uses `nth_error faces i`; a valid face removes its current Extract slice, while an out-of-range step leaves the remainder unchanged. `StrippingSlice` uses the same lookup and is empty out of range. Generic set-theoretic induction proves the recurrence, partition, and disjointness results; existing face and polyhedral APIs provide the geometric side conditions and finite ordered face list.

**Tech Stack:** Rocq/Coq, standard `List`/`Nat`, existing Mell face, Extract, and rational-polyhedral modules.

**Spec:** User contract T10-C4-3D1 in the active conversation.

## Global Constraints

- Preserve all public APIs through C4-3D0.
- Do not implement C4-3D2, Lemma 6.11, or the final theorem.
- Use `SameSet`, never functional extensionality, for set equality.
- Introduce no `Axiom`, `Admitted`, `Abort`, `ClassicalEpsilon`, choice oracle, UIP/K, or `Eq_rect_eq`.
- Modify and commit only D1 source, regression, audit, plan, and minimal `_CoqProject` entries; do not push.

## Review Focus

- `nth_error=None`: slice is empty and no fictitious face is introduced.
- Exact boundary `i = length faces`: every real face has been processed and the recurrence stops changing.
- Fixed `excluded`: it is never replaced by a remainder or slice.
- Disjointness across non-adjacent stages follows from decreasing remainders.
- Ordered face-list witness retains head, completeness, uniqueness up to `SameSet`, and reverse-inclusion order.

---

### Task 1: Core recursion and equations

**Files:**
- Create: `theories/Geometry/FaceStrippingRecursion.v`
- Create: `theories/Audit/FaceStrippingRecursionExamples.v`

**Interfaces:**
- Consumes: `ExtractFace`, `SameSet`, `nth_error`.
- Produces: `StrippingRemainder`, `StrippingSlice`, zero/slice/successor specifications.

- [x] Write audit checks/examples for zero, valid successor, and out-of-range empty slice.
- [x] Compile the audit and observe RED due to the absent module/API.
- [x] Implement the two definitions and recurrence specifications.
- [x] Compile source and audit to GREEN.

### Task 2: Inclusion, characterization, and disjointness

**Files:**
- Modify: `theories/Geometry/FaceStrippingRecursion.v`
- Modify: `theories/Audit/FaceStrippingRecursionExamples.v`

**Interfaces:**
- Consumes: Task 1 recurrence equations, `extract_face_subset_difference`, `excluded_subset_extract_remainder`.
- Produces: remainder/slice inclusions, excluded preservation, `ProcessedBefore`, partition and disjointness theorems.

- [x] Add audit type checks and concrete N/2N stage equations before implementation; observe RED.
- [x] Prove decreasing remainders and all D1-2 through D1-5 results by induction.
- [x] Compile focused source/audit to GREEN.

### Task 3: Ordered face-list connection and D2 interface

**Files:**
- Modify: `theories/Geometry/FaceStrippingRecursion.v`
- Modify: `theories/Audit/FaceStrippingRecursionExamples.v`
- Modify: `_CoqProject`
- Create: `docs/review/t10-c4-3d1-face-stripping-recursion-audit.md`

**Interfaces:**
- Consumes: `finitely_generated_period_cone_polyhedral`, `polyhedral_faces_linearized`.
- Produces: ordered face-list existence theorem and `StageCandidateFace`; no D2 invariant proof.

- [x] Add public type checks and actual-period boundary regressions, including N×Z lineality.
- [x] Repackage the existing finite ordered face witness and define `StageCandidateFace`.
- [x] Run focused build, full build, `coqchk`, `Print Assumptions`, prohibited scan, and diff check.
- [x] Obtain independent review, fix Important/Critical findings via RED/GREEN, commit only authorized files, and stop.
