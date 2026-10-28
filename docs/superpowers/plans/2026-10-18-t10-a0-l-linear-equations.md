# T10-A0-L Nonnegative Linear Equations Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that every system of integer linear equations over nonnegative integer variables has a semilinear solution set, without constructing an executable equation-to-code compiler.

**Architecture:** Define integer-matrix evaluation on the existing `NVec` representation.  Instantiate T10-G's countable finite-cover theorem with Dickson's order for nonzero homogeneous solutions and arbitrary inhomogeneous solutions.  Prove homogeneous finite generation by strong induction on coordinate sum, decompose every inhomogeneous solution into a finite basis element plus a homogeneous solution, and translate the resulting finite union into the existing `SemiCode`/`denote` semantics.

**Tech Stack:** Coq 8.20.1, existing `NVec`/`ZVec`, `SemiCode`, T10-G `countable_af_finite_cover`, and `nvec_le_almost_full`.

**Spec:** User-approved T10-A0-L contract of 2026-10-18; compatible with `docs/review/t10-planning-audit.md` and preceding T10-G plan.

## Global Constraints

- Do not implement T10-A0-QF, the rest of T10-A0, or T10-A.
- Preserve the public T10-G finite-cover theorem types and their reduced axiom footprint.
- Do not add `Admitted`, an axiom, UIP/K, or an external oracle.
- Do not stage or modify the pre-existing `vendor/presburger/` files or verification-log changes.

## Review Focus

- Empty inhomogeneous solution sets and the zero-only homogeneous monoid.
- Dimension zero and zero-row matrices.
- Negative matrix coefficients and exact integer subtraction in the difference lemma.
- Multiple incomparable inhomogeneous basis elements.
- Homogeneous monoids requiring multiple generators.

### Task 1: RED public contract and boundary examples

**Files:**
- Create: `theories/Audit/LinearEquationExamples.v`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: T10-G public finite-cover results and existing `SemiCode` semantics.
- Produces: failing checks for the four A0-L public theorems and executable boundary fixtures.

- [x] Add failing `Check` commands for homogeneous finite generation, inhomogeneous finite basis, decomposition, and semilinear representation.
- [x] Run `make check-t10-a0-l` and record failure caused by the missing declarations.

### Task 2: Matrix semantics, finite covers, and homogeneous generation

**Files:**
- Create: `theories/Semilinear/LinearEquations.v`
- Modify: `theories/Audit/LinearEquationExamples.v`, `_CoqProject`

**Interfaces:**
- Consumes: `decode_nvec`, `nvec_le_dec`, `nvec_le_almost_full`, `countable_af_finite_cover`.
- Produces: integer matrix evaluation, explicit difference/additivity lemmas, finite solution bases, and finite generation of homogeneous solutions.

- [x] Define `ZMatrix`, `matrix_apply`, `LinearSolution`, `HomogeneousSolution`, and finite-generation semantics.
- [x] Prove enumeration soundness/completeness and restricted Dickson `afs`.
- [x] Obtain finite covers for nonzero homogeneous and arbitrary inhomogeneous solutions.
- [x] Prove that `g <= h` gives an exact natural difference and that matrix evaluation sends the difference of two equal-image vectors to zero.
- [x] Prove homogeneous finite generation by strong induction on coordinate sum.

### Task 3: Decomposition, `SemiCode`, GREEN, and audit

**Files:**
- Modify: `theories/Semilinear/LinearEquations.v`, `theories/Audit/LinearEquationExamples.v`, `Makefile`

**Interfaces:**
- Consumes: Task 2 finite bases and generators.
- Produces: exact inhomogeneous decomposition and `SemiCode` existence theorem.

- [x] Prove every inhomogeneous solution is a basis element plus a homogeneous solution.
- [x] Prove equivalence between generated homogeneous solutions and `weighted_sum`.
- [x] Construct the finite `SemiCode` and prove exact extensional equivalence with `denote`.
- [x] GREEN all required boundary examples.
- [x] Run focused regression, T10-G regression, `coqchk`, complete `Check`, and `Print Assumptions` audits.
- [x] Obtain independent review and explicitly stage only A0-L files.
