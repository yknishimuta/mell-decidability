# Task 6E4: Theorem 12 and Corollary 14

1. Audit the exact Lemma 9, Lemma 11, VASS-section, and stateful semilinearity APIs.
2. Add the Theorem 12 composition and verify its assumptions.
3. Add finite-initial-set, exact visible/zero-suffix lifting, and almost-semilinear coordinate-projection adapters.
4. Apply the stateful VAS post theorem state-by-state and prove the section semantics equivalence.
5. Prove Corollary 14, add focused regressions and audit targets, then run the required full verification.
6. Request an independent review, stage only Task 6E4 files, and create one local commit.

The implementation preserves the existing public definitions.  In particular,
the VASS-section zero suffix is imposed before visible-coordinate projection,
and the existential finite basis from Lemma 9 is not exposed as a Gallina
selection algorithm.
