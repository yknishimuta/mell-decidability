# C4-3D0 Minimal Face and Lemma 6.9 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize cone lineality as the least face and prove Lemma 6.9 for the existing `ExtractFace period face excluded remaining` argument order.

**Architecture:** Add one focused geometry module for lineality, inverse closure on its face period, and Lemma 6.9. Add one audit module with public-type, assumption, and boundary regressions; record the paper/API argument-order audit separately.

**Tech Stack:** Coq, repository Q/Z vector APIs, existing HRep-D and face/periodic lemmas.

**Spec:** User-provided T10-C4-3D0 contract in this thread.

## Global Constraints

- Preserve all public APIs through C4-3C2-R.
- No new axiom, `Admitted`, `Abort`, forbidden choice/UIP/extensionality principle, or external oracle.
- Do not touch or stage protected audit logs, `theories/Audit/FaceStrippingBasesExamples.v`, or `vendor/presburger/`.
- Stop after C4-3D0; do not implement C4-3D1 or later results.

## Review Focus

- Lineality of a pointed cone is `{0}`, while lineality of a full space is the full space.
- Mixed cone/group behavior such as `N × Z` retains exactly the group axis.
- Inverse closure applies only to `FacePeriod` at lineality, not arbitrary period elements.
- Extract keeps the existing `excluded, remaining` order.
- Empty, equal, and proper excluded/remaining cases preserve the difference semantics.

---

### Task 1: Cone lineality and least face

**Files:**
- Create: `theories/Geometry/FaceStrippingMinimalFace.v`
- Test: `theories/Audit/FaceStrippingMinimalFaceExamples.v`

**Interfaces:**
- Consumes: `polyhedral_cone_integer_hrep`, `FaceOf`, `SupportingNormal`, `qinner_scale_right`.
- Produces: `ConeLineality`, `MinimalConeFace`, `polyhedral_lineality_minimal_face` and supporting characterizations.

- [ ] Add RED audit checks/examples for the intended public definitions and theorem.
- [ ] Compile the audit and confirm failure because the module/API is absent.
- [ ] Prove the integer-H-representation zero characterization, facehood, and least-face theorem.
- [ ] Compile source and focused audit to GREEN.

### Task 2: Inverse closure and Lemma 6.9

**Files:**
- Modify: `theories/Geometry/FaceStrippingMinimalFace.v`
- Modify: `theories/Audit/FaceStrippingMinimalFaceExamples.v`

**Interfaces:**
- Consumes: `difference_opp`, `full_periodic_member_iff_difference_cone`, `extract_face_subset_difference`.
- Produces: `lineality_face_period_inverse`, lineality-face-period inverse closure, `lemma_6_9_minimal_extract`, and the arbitrary-minimal-face corollary when transport is direct.

- [ ] Add RED theorem checks and concrete `N`, `2N`, `Z`, `N^2`, and `N × Z` regressions.
- [ ] Compile and confirm the intended missing theorem/behavior failures.
- [ ] Implement inverse closure and both inclusions of the Extract/difference `SameSet`.
- [ ] Add and prove arbitrary-minimal-face transport if it requires no stronger premise.
- [ ] Compile source and focused audit to GREEN.

### Task 3: Integration, audit, and review

**Files:**
- Modify: `_CoqProject`
- Create: `docs/review/t10-c4-3d0-minimal-face-audit.md`

**Interfaces:**
- Consumes: Tasks 1-2.
- Produces: reproducible C4-3D0 verification record and a local commit.

- [ ] Run focused build/regressions, full Coq build, `coqchk -silent`, `Print Assumptions`, prohibited-token scan, and target-scoped `git diff --check`.
- [ ] Request independent whole-change review and address all Critical/Important findings with RED/GREEN evidence.
- [ ] Stage only C4-3D0 target files, commit locally, and verify final HEAD/status.
