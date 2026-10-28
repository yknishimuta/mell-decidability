# Task 6E3 Bounded VASS Section Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct a finite Gallina VASS section for exactly the BVASS configurations reachable by runs of branching depth at most a supplied bound.

**Architecture:** Add a section record around the existing finite-control `VAS`: an auxiliary counter dimension, an internal finite state count, a transition list, finite initial configurations, and an accepting-state map. Section acceptance targets `visible ++ zero_aux`, so projection never hides auxiliary residue. Build constructive combinators for initial sections, disjoint finite union, unary closure, and a branching-rule image with isolated child counter blocks and a finite phase controller; then mirror the BVASS bounded-depth decomposition by recursion on the bound.

**Tech Stack:** Coq/Gallina, standard `Vector`, `List`, `Fin`, existing `Mell.VAS.StatefulVAS`, `Mell.BVASS.Stateful`, and Task 6E2 `branching_depth`.

**Spec:** User Task 6E3 instruction, 2026-10-24.

## Global Constraints

- Preserve all existing public definitions and Task 6E0–6E2 theorems.
- The compiler is a transparent finite Gallina function and does not use the non-computable finite basis.
- Auxiliary counters must be zero before visible-coordinate projection.
- No new axioms, `Admitted`, choice oracle, UIP/K, or functional extensionality.
- Do not implement Task 6E4.

## Review Focus

- Residual child or section auxiliary counters must prevent acceptance.
- Disjoint union and rule-image phases must not permit cross-component control flow.
- Duplicate child states remain distinct child occurrences and their counters are both accumulated.
- Negative rule actions are enabled only through ordinary VAS nonnegativity.
- Bound zero includes arbitrary unary chains but no branching root.

---

### Task 1: VASS section core and finite union

**Files:**
- Create: `theories/BVASS/VASSSection.v`
- Test: `theories/Audit/BoundedVASSSectionExamples.v`

**Interfaces:**
- Produces: `VASSSection`, `VASSSectionReach`, empty/initial sections, binary/list union, and exact reach iff theorems.

- [ ] Add failing `Check`/example statements for empty, initial, and union sections.
- [ ] Compile them to confirm the section API is absent.
- [ ] Implement vector embeddings, transition/state renaming, section semantics, and union.
- [ ] Prove exact empty/initial/union semantics and rerun focused compilation.

### Task 2: Unary closure

**Files:**
- Modify: `theories/BVASS/VASSSection.v`
- Modify: `theories/Audit/BoundedVASSSectionExamples.v`

**Interfaces:**
- Consumes: core section combinators.
- Produces: `UnaryClosure`, `compile_unary_closure`, and exact section semantics.

- [ ] Add failing base/unary-chain examples.
- [ ] Define the unary-rule reflexive-transitive closure and compiler.
- [ ] Prove soundness/completeness and run focused tests.

### Task 3: Branching rule image

**Files:**
- Create: `theories/BVASS/BoundedVASSSection.v`
- Modify: `theories/Audit/BoundedVASSSectionExamples.v`

**Interfaces:**
- Consumes: `VASSSection` and unary closure.
- Produces: `RuleImage`, `compile_rule_image`, and its iff theorem.

- [ ] Add failing binary/duplicate-state/negative-action/residual-aux examples.
- [ ] Implement finite child block layout, phase states, copied transitions, transfer loops, and final action.
- [ ] Prove copied execution, phase normalization, exact transfer, soundness, and completeness.
- [ ] Run focused compiler and regression checks.

### Task 4: Bounded-depth semantics and recursive compiler

**Files:**
- Modify: `theories/BVASS/BoundedVASSSection.v`
- Modify: `theories/Audit/BoundedVASSSectionExamples.v`

**Interfaces:**
- Produces: `compile_bounded_vass_section`, `bounded_vass_section_correct`, and `lemma_11_bounded_depth_vass_section`.

- [ ] Add failing depth 0/1/2 and persistent-initial examples.
- [ ] Prove the BVASS unary-spine bounded-depth decomposition.
- [ ] Define the recursive compiler from initial section, branching rule images, finite union, and unary closure.
- [ ] Prove correctness by induction on the bound and rerun focused tests.

### Task 5: Audit, review, and integration

**Files:**
- Modify: `_CoqProject`, `Makefile`
- Create: `docs/review/t10-e3-bounded-vass-section-audit.md`

- [ ] Register modules and add focused/audit targets.
- [ ] Run Task 6E0–6E3 regressions, T09 bridge audit, and T10-G audit.
- [ ] Run forced full `_CoqProject` build, full `validate`, public `Check`, assumptions, and prohibited scans.
- [ ] Obtain independent read-only review focused on zero constraints, phase isolation, multiplicity, transfers, bounds, and constructivity.
- [ ] Stage only Task 6E3 files, check the cached diff, and create one local commit without pushing.
