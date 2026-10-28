# T10-E2 bounded branching implementation plan

1. Add a RED audit importing `Mell.BVASS.BoundedBranching` and checking the requested public contracts.
2. Implement `branching_depth` and its structural/isomorphism lemmas.
3. Define `RunBasis`, `SameTargetAndSize`, indexed `R` membership/cardinality, and prove invariance, non-emptiness, bounds, and subrun monotonicity.
4. Define positional bad children, prove minimal representatives, simultaneous sibling replacement, and strict `R` decrease.
5. Prove the strong bounded-depth construction through `extend_local_root_shortening`, then the finite-basis and uniform Lemma 9 interfaces.
6. Add focused examples and the audit report; register only the new modules.
7. Run focused checks, inherited 6E0/6E1 and T09/T10-G regressions, forced full build, assumptions checks, scans, `coqchk`, and an independent read-only review.
8. Stage only Task 6E2 files and commit locally if every check passes.
