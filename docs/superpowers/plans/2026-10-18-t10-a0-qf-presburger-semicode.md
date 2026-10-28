# T10-A0-QF Quantifier-Free Presburger Semicode Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that every well-scoped quantifier-free MiniCooper formula, interpreted over a natural-vector environment and a fixed abstract-constant environment, denotes an existing `SemiCode`.

**Architecture:** Convert MiniCooper's quantifier-free syntax directly to mutually defined positive/negative finite DNF, preserving the original scoped terms while proving the same negation-normal semantics. Compile each conjunction to one integer linear-equation system over the free natural variables plus finitely many natural witnesses, invoke T10-A0-L, and project the resulting `SemiCode` back to the free coordinates. Concatenate the projected codes for the finite disjunction.

**Tech Stack:** Coq 8.20.1, vendored Armael/minicooper, existing `NVec`, `SemiCode`, `denote`, and T10-A0-L `linear_equations_semicode`.

**Spec:** User-approved T10-A0-QF contract of 2026-10-18 and `docs/review/t10-planning-audit.md`.

## Global Constraints

- Implement T10-A0-QF only; do not implement A0-QE, T10-A, or later work groups.
- Preserve MiniCooper de Bruijn variable positions and interpret its `CAbstract` constants through an explicit fixed `cenv`.
- Do not depend on the unfinished `semilinear_intersection` or `semilinear_complement` theorems.
- Do not add `Admitted`, an axiom, UIP/K, or an oracle.
- Do not modify or stage pre-existing review logs or `vendor/presburger/`.

## Public Contract

`qf_well_scoped d phi` is an `MC.all` predicate and therefore both excludes `FExists` and requires every term variable to be strictly below `d`.

```coq
qf_semicode :
  forall d (cenv : MC.environment) (phi : MC.formula),
    qf_well_scoped d phi ->
    exists code : SemiCode d,
      forall value : NVec d,
        MC.interpret_formula cenv (nat_environment value) phi <->
        denote code value
```

## Review Focus

- `Dv` and negated `Dv` at negative, zero, unit, and larger absolute divisors.
- Strict inequality and disequality witnesses when the interpreted term is negative.
- Empty conjunction/disjunction and dimension zero.
- Repeated free-variable occurrences and negative coefficients.
- Projection preserving the same coefficient list for bases and every period.

---

### Task 1: RED contract, scoped syntax, and NNF/DNF

**Files:**
- Create: `theories/Audit/QFSemilinearExamples.v`
- Create: `theories/Semilinear/QuantifierFree.v`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `MiniCooper.Theory.qf`, its `all` induction principle, and MiniCooper's term/formula semantics.
- Produces: `nat_environment`, `qf_well_scoped`, normalized literals, finite DNF, and their exact semantic equivalences.

- [x] Add a failing `Check qf_semicode` and boundary fixtures; run `make check-t10-a0-qf` and record the missing declaration failure.
- [x] Define the term/formula scope predicate without changing MiniCooper variable indices.
- [x] Convert quantifier-free syntax to finite signed DNF, expanding negated equality and negated divisibility into finite alternatives, and prove exact semantics.
- [x] Test truth, falsity, empty branches, negative/zero divisors, repeated variables, and dimension zero.

### Task 2: Diophantine compilation and projection

**Files:**
- Modify: `theories/Semilinear/QuantifierFree.v`
- Modify: `theories/Audit/QFSemilinearExamples.v`

**Interfaces:**
- Consumes: Task 1 DNF and T10-A0-L `linear_equations_semicode`.
- Produces: conjunction-to-equation-system semantics and `project_semicode` correctness.

- [x] Define integer linear forms for MiniCooper terms and prove evaluation under `nat_environment`.
- [x] Allocate natural witnesses for strict inequalities and signed quotients; prove both directions for every normalized literal.
- [x] Compile each conjunction to one `ZMatrix`/constant vector and prove equivalence with existential natural witnesses.
- [x] Define prefix projection on vectors, bases, periods, and codes; prove weighted-sum, linear-component, and `denote` projection equivalences.
- [x] Apply `linear_equations_semicode` and projection to obtain a `SemiCode d` for every DNF conjunction.

### Task 3: Public theorem and verification

**Files:**
- Modify: `theories/Semilinear/QuantifierFree.v`
- Modify: `theories/Audit/QFSemilinearExamples.v`
- Modify: `Makefile`

**Interfaces:**
- Consumes: Tasks 1--2.
- Produces: the exact `qf_semicode` public theorem.

- [x] Concatenate branch codes and prove finite-union semantics, including the empty disjunction.
- [x] Complete `qf_semicode` and turn the RED check GREEN.
- [x] Run all boundary examples, focused regression, complete type and `Print Assumptions` audit, and `coqchk`.
- [x] Obtain an independent read-only review; address any blocking finding through RED/GREEN.
- [ ] Explicitly stage and commit only the five A0-QF target files; do not push.
