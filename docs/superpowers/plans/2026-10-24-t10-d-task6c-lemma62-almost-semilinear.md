# T10-D Task 6C Implementation Plan

**Goal:** Prove Leroux Lemma 6.2 for periodic cones and assemble the finite-run-basis decomposition into an almost-semilinear relation.

**Design:** Keep the existing `Periodic`, `AsymptoticallyDefinable`, and `AsymptoticallyDefinableNRelation` APIs.  Add one module for periodic intersections and the finitely generated period adapter, one module for finite translated components, and one assembly module for restricted reachability.  All equalities of predicates remain pointwise; no functional extensionality or witness-selection function is introduced.

## Steps

1. Add a RED audit driver importing the three new modules and checking the requested public contracts; confirm it fails because the first module is absent.
2. Implement `PeriodicIntersection.v`: periodic intersection, common-positive-multiple cone intersection, Lemma 6.2, the exact `NRelationAsZ` intersection adapter, and the finitely generated `GeneratedPeriodPair` cone/Q-definability bridge.
3. Implement `AlmostSemilinear.v`: finite translated-component representation and finite-union closure.
4. Implement `LinearReachAlmostSemilinear.v`: transformer/period intersection, one-run component, and the finite-basis assembly theorem.
5. Complete boundary regressions and full public `Check`/`Print Assumptions` driver.
6. Run focused builds, forced `_CoqProject` rebuild, `coqchk -silent`, forbidden-construct scan, and `git diff --check`.
7. Request an independent read-only review, write the audit report, stage only Task 6C files, and create the requested local commit.
