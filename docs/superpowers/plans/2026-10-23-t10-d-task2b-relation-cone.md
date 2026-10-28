# T10-D Task 2B Relation-Cone Composition Plan

**Goal:** Prove Leroux Lemma 5.1 for periodic integer and natural-vector relations, without proving capacity-transformer asymptotic definability.

**Spec:** The user-approved T10-D Task 2B contract in this thread.

**Architecture:** Encode relation pairs with vector append/split, reuse the existing periodic cone denominator-clearing theorem for positive multiples, prove cone/composition exchange using a common product multiplier, and express rational relation composition with a narrowly scoped formula-renaming lemma plus the existing intersection/projection API.

## Task 1: RED and pair adapters

- Create `theories/Audit/VASAsymptoticRelationExamples.v` with failing imports/checks.
- Create `theories/VAS/RelationCone.v`.
- Define `ZRelation`, composition, Z/Q pair pack/unpack, extensionality, addition, embedding compatibility, and the exact nonnegative `NRelation` lift.
- Focused compile.

## Task 2: Periodicity, rational cone, and positive multiples

- Define `PeriodicZRelation` and prove composition/lift preservation.
- Define `RationalRelationCone` through existing `Cone`.
- Prove its structural closure and pair characterization.
- Wrap `periodic_standard_cone_denominator_clearing` as `periodic_cone_positive_multiple_iff` with explicit positive natural multiplier.
- Focused compile.

## Task 3: Cone/composition exchange

- Prove the forward direction using the integer middle witness from the cleared composed pair.
- Prove the reverse direction using the product multiplier, periodic natural scaling, and injectivity of `zvec_to_qvec` to identify the two scaled middle vectors.
- Add a nonperiodic counterexample regression.
- Focused compile.

## Task 4: QDefinable composition

- Create `theories/VAS/AsymptoticRelation.v`.
- Add only the coordinate-renaming syntax/semantics/closedness lemmas needed to pull two pair formulas back to a triple.
- Combine by intersection and project away the middle block with `qdefinable_projection`.
- Prove `qdefinable_relation_compose` including dimension zero.
- Focused compile.

## Task 5: Lemma 5.1 and run-transformer conditional lift

- Define integer/natural asymptotic-definability predicates.
- Combine periodicity, cone exchange, and Q-definability into both Lemma 5.1 variants.
- Start from the mandatory source-capacity transformer and induct over
  `TransformerAlongTargets`; no empty-composition identity case is needed.
- Add required signed, asymmetric, denominator, `2x/3y`, and multi-capacity regressions.

## Task 6: Verification and handoff

- Add `_CoqProject`/Makefile focused targets and the audit document.
- Run focused build/regression, full project build, `coqchk -silent`, `Check`, `Print Assumptions`, forbidden scan, and target-only diff check.
- Request an independent review, fix any Critical/Important findings, stage only Task 2B files, commit locally, and stop before Task 3.
