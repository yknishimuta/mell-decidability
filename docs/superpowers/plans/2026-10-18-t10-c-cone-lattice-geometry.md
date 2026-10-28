# T10-C Cone and Lattice Geometry Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the rational closed-cone, lattice, closed-linearization, center, and face results required by S.

**Architecture:** Build a narrow adapter between project `QVec`/`ZVec` predicates and the pinned polyhedra/linear-algebra libraries.  Prove rational closed-cone finite generation, then lattice Gordan, then the paper's `ClosedLinearization`, `FullPeriodic`, `Center`, and face contracts.  Keep rational topology and the subgroup `P-P` explicit throughout.

**Tech Stack:** Coq 8.20.1, pinned Coq-Polyhedra/MathComp, T10-A rational definability, T10-B periodic finite generation, T06 cone bridge.

**Spec:** `docs/review/t10-planning-audit.md`

## Global Constraints

- Use rational topological closure; any real-space library theorem requires a proved rational-point adapter.
- `FullPeriodic Q` means `Q = (Q-Q) ∩ Cone(Q)`, not `Q = Z^d ∩ Cone(Q)`.
- Faces contain zero; the empty external face is never substituted for the minimal face.
- Lemmas 4.4 and 4.7 carry `NonnegativeSet P`, matching their source domain `P subset N^d`; Lemmas 4.8 and 4.9 retain the signed `Z^d` domain.

## Review Focus

- A proper sublattice such as `2Z` intersected with a ray.
- A nonclosed rational cone and its boundary.
- Zero cone, lineality space, and dimension zero.
- Lemma 4.7's `x ∈ p+Q` translation and all quantifiers.
- Strictly positive coefficients and spanning in Lemma 4.8.

---

### Task 1: Rational topology/polyhedron adapter

**Files:**
- Create: `theories/Geometry/Lattice.v`
- Create: `theories/Geometry/ClosedLinearization.v`
- Create: `theories/Audit/GeometryStatements.v`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `QDefinable`, `Cone`, pinned polyhedron finite-generation theorems.
- Produces: `TopologicallyClosed`, `IsCone`, `RationalPolyhedralCone`, `FinitelyGeneratedGroup`, `Difference`, `ClosedLinearization`, and the first four T10-C contracts.

- [ ] **Step 1: RED.** Add exact theorem statements and record failure before the adapter exists.
- [ ] **Step 2: Prove representation bridges.** Relate project vectors/equality to MathComp columns and polyhedra without assuming proof irrelevance.
- [ ] **Step 3: Prove rational closed-cone finite generation.** Track the precise external theorem and every required finite-dimensional/ordered-field hypothesis.
- [ ] **Step 4: Prove lattice Gordan.** Use the supplied subgroup `G`; test `2Z` to prevent accidental replacement by all integer points.
- [ ] **Step 5: Prove finite generation/fullness of closed linearization.** Match arXiv Lemma 4.4 and the definition immediately preceding it.
- [ ] **Step 6: GREEN.** Run focused examples, `make check-t10-c`, and commit the adapter/linearization unit.

### Task 2: Push-in and center

**Files:**
- Create: `theories/Geometry/Center.v`
- Modify: `theories/Geometry/ClosedLinearization.v`, `theories/Audit/GeometryStatements.v`, `_CoqProject`

**Interfaces:**
- Consumes: finite generation/fullness and rational linear algebra.
- Produces: `closed_linearization_push_in`, `PositiveSpanningCombination`, `Center`, `center_characterization`, `center_absorbs_closed_linearization`.

- [ ] **Step 1: RED.** State Lemmas 4.7--4.9 with the exact audit types and confirm missing proof obligations.
- [ ] **Step 2: Prove Lemma 4.7.** Preserve `exists p in P`, then `forall g in P-P`, `forall x in p+Q`, `exists r`, `forall n`.
- [ ] **Step 3: Prove Lemma 4.8.** Show both directions, strict positivity, membership in `P-P`, and spanning of `Vec(P)`.
- [ ] **Step 4: Prove Lemma 4.9.** Establish both inclusions of the Minkowski equality.
- [ ] **Step 5: GREEN.** Test a ray, a group/lineality case, and a lower-dimensional cone; commit this unit.

### Task 3: Faces and final audit

**Files:**
- Create: `theories/Geometry/Faces.v`
- Modify: `theories/Audit/GeometryStatements.v`, `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: rational polyhedral finite inequality presentations.
- Produces: `IsFace`, minimal/maximal face facts, `rational_polyhedral_faces_finite`.

- [ ] **Step 1: RED.** Test that the empty predicate is rejected as a face and that lineality is the minimal face.
- [ ] **Step 2: Implement face adapter.** Connect supporting equalities to project faces and enumerate finite subsets of inequalities.
- [ ] **Step 3: Prove finite faces.** Include exact extensional equality of every face with an enumerated face.
- [ ] **Step 4: Verify.** Run `make check-t10-c`, `make audit-t10-c`, module `coqchk`, full public `Check`, and `Print Assumptions`.
- [ ] **Step 5: Independent review.** Reviewer checks source Lemmas 4.4 and 4.7--4.9, lattice domain, closure field, and empty-face handling.
- [ ] **Step 6: Commit.** Commit only C files as `feat(t10-c): formalize periodic-set geometry`.
