# T10-A Arithmetic and Set Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Supply the semilinear closure and rational-definability operations required by the VAS and BVASS proofs.

**Architecture:** Keep extensional `Prop` sets separate from executable `SemiCode`.  Prove semilinear closure constructively where codes compose directly; use the verified Presburger backend for intersection/complement/projection and prove every conversion extensionally.  Give rational formulas their own syntax/semantics rather than reusing integer Presburger semantics unsafely.

**Tech Stack:** Coq 8.20.1, existing `NVec`/`QVec`, `SemiCode`, `compile_membership_correct`, MiniCooper backend, MathComp rationals.

**Spec:** `docs/review/t10-planning-audit.md`

## Global Constraints

- Preserve the T08 membership compiler and its complete type.
- Set closure theorems live in `Prop`; only code constructors and decision procedures may be called executable.
- Projection is existential elimination after coordinate selection, not coordinate truncation by convention.

## Review Focus

- Empty finite union and complement of the universal set.
- Cartesian product at dimensions zero/nonzero and append/split round trips.
- Projection with repeated and permuted coordinates.
- Zero periods and duplicate components in `SemiCode`.
- Integer-natural guards when Presburger elimination constructs a new code.

---

### Task 1: Extensional set and vector-product interface

**Files:**
- Create: `theories/Semilinear/Closure.v`
- Create: `theories/Audit/SemilinearClosureStatements.v`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `NVec`, `nvec_add`, `SemiCode`, `denote`, `decode_semi_encode`.
- Produces: `NSet`, `SameSet`, `Semilinear`, append/split projections, finite union, Minkowski sum, and product contracts from audit §3 T10-A.

- [ ] **Step 1: RED.** Add `Fail Check semilinear_finite_union`, `Fail Check semilinear_minkowski_sum`, and `Fail Check semilinear_product` to the audit module; run `make check-t10-a` and record the expected missing declarations.
- [ ] **Step 2: Define the interfaces.** Implement `NSet`, `SameSet`, `Semilinear`, vector append/split functions, and prove split/append inverses including `d=0` and `e=0`.
- [ ] **Step 3: Prove constructive closures.** Implement code-level finite union, Minkowski sum, and product constructors and prove the exact public types in audit §3.
- [ ] **Step 4: GREEN.** Replace `Fail Check` with `Check`; prove empty/zero-period/product regression examples and run `make check-t10-a`.
- [ ] **Step 5: Commit.** Explicitly stage only this task's four files and commit `feat(t10-a): add constructive semilinear closures`.

### Task 2: Presburger-derived closures

**Files:**
- Modify: `theories/Semilinear/Closure.v`
- Modify: `theories/Audit/SemilinearClosureStatements.v`

**Interfaces:**
- Consumes: `compile_membership_correct`, Presburger Boolean operations/QE correctness.
- Produces: `semilinear_projection`, `semilinear_intersection`, `semilinear_complement` with exactly the audit types.

- [ ] **Step 1: RED.** State all three theorems and confirm the proof file fails before conversion-back lemmas exist.
- [ ] **Step 2: Prove formula closure.** Construct closed guarded integer formulas for intersection/complement/projection and prove bound-variable shifting and natural guards.
- [ ] **Step 3: Prove representation recovery.** Formalize the required Presburger-to-semilinear direction for these generated formulas; do not postulate the general Presburger/semilinear equivalence.
- [ ] **Step 4: GREEN.** Test empty set, full set, repeated projection coordinate, negative integer witness rejection, and a zero-period component.
- [ ] **Step 5: Commit.** Stage the two files and commit `feat(t10-a): close semilinear boolean operations`.

### Task 3: Rational definability

**Files:**
- Create: `theories/Geometry/RationalDefinability.v`
- Modify: `theories/Audit/SemilinearClosureStatements.v`, `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `QVec`, exact rational equality/order.
- Produces: `QFormula`, `qformula_semantics`, `QDefinable`, `qdefinable_projection`, `qdefinable_intersection`.

- [ ] **Step 1: RED.** Add exact `Check` commands for both public theorems and record failure.
- [ ] **Step 2: Implement syntax and semantics.** Cover rational constants, addition, equality/order, Boolean connectives, and quantifiers with explicit de Bruijn shifting.
- [ ] **Step 3: Prove closures.** Prove projection by existential quantification and intersection by conjunction, including coordinate maps.
- [ ] **Step 4: GREEN and audit.** Run `make check-t10-a`, `make audit-t10-a`, and `coqchk` on both new modules.  Save exact types and `Print Assumptions`; reject any mathematical axiom.
- [ ] **Step 5: Independent review.** Reviewer checks set/code separation, binder indices, natural guards, and the audit contracts.
- [ ] **Step 6: Commit.** Stage only A files and commit `feat(t10-a): add rational definability interface`.
