# Task 11-C Safe Linearization Implementation Plan

> Execute in the current `work/mell-formalization` checkout. Preserve all pre-existing dirty and untracked files. Do not use a worktree because the approved baseline and protected artifacts are in this checkout.

## Goal

Formalize Bizière–Leroux–Sutre Section 5 Lemmas 5.7, 5.4, and 5.1 using the completed Task 11-A/11-B APIs, without adding choice axioms or weakening the published contracts.

## Task 1: C1 one-source reduction

- Add `theories/BVAS/OneSourceReduction.v`.
- Define occurrence-preserving multi-source shuffle predicates over Task 11-B free-run source words.
- First add failing `Check` declarations to the audit module for the intended public API.
- Prove marked-leaf shift, child classification, exact period redistribution, and `lemma_5_7_one_source_reduction` by mutual structural induction over free runs/child lists.
- Focused check: compile the module and inspect `Print Assumptions`.

## Task 2: C2 semilinear ray almost-fullness

- Add `theories/WSVAS/SemilinearRayOrder.v`.
- Define `RayLe` with exact signed-vector differences and an explicit nonnegative point witness.
- Prove almost-fullness componentwise from a semilinear presentation and the existing finitely generated periodic order.
- Combine `af` relations directly. Do not claim `RayLe` is transitive.
- Derive the complement instance using `semilinear_complement`.
- Focused check and assumptions audit.

## Task 3: C3 WSVAS safe linearization

- Add `theories/WSVAS/SafeLinearization.v`.
- Define reachability from a source set and the N/Z embeddings used by closed linearization.
- Reuse `closed_linearization_push_in`, `closed_linearization_finitely_generated`, WSVAS run WQO, and exact scaling.
- Prove the contradiction by `af` induction, requesting only the finitely many counterexample witnesses demanded by the induction. Never construct `nat -> WSRun` from `forall n, exists run`.
- Establish exact source and target extrapolation and publish `lemma_5_4_wsvas_safe_linearization`.
- Focused check and assumptions audit.

## Task 4: C4 BVAS safe linearization

- Add `theories/Separator/SafeLinearization.v`.
- Extract a finite semilinear presentation in Prop, instantiate `concrete_wsvas`, and bridge its `SimulationInvariant` extensionally to `A \/ Reach S`.
- Reuse Lemmas 5.5 and 5.6, apply Lemma 5.4, derive `X + Q <= X`, then apply Lemma 5.7.
- Publish `lemma_5_1_bvas_safe_linearization` without additional computability or finiteness premises.
- Focused check and assumptions audit.

## Task 5: C5 regression, audit, review, commit

- Add `theories/Audit/SafeLinearizationExamples.v` with public `Check`s and boundary regressions; register all modules in `_CoqProject`.
- Write `docs/review/t11-c-safe-linearization-audit.md`, including the restriction-before-selection argument and exact public types.
- Run focused builds, Task 11-A/11-B and T06/T09/T10-C regressions, forced full rebuild, validation, coqchk, forbidden-token scan, and both diff checks.
- Request an independent review focused on AF versus WQO, witness selection, exact scaling, marked occurrence handling, and the Lemma 5.1 composition.
- Stage only Task 11-C deliverables and create a local commit; do not push.
