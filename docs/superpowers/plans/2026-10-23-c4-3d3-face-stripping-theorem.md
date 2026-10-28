# C4-3D3 Face-Stripping Theorem 6.1 implementation plan

**Goal:** Complete the final Face-Stripping Theorem by identifying the final remainder, proving the disjoint slice partition, packaging all finite-basis facts, and proving the optional empty-first-slice conclusion.

**Architecture:** Add one integration module over C4-3D0--D2.  The terminal remainder proof combines Lemma 6.9 on the lineality face with D2's no-candidate theorem.  D1's partition and disjointness results then yield the exact slice decomposition.  Existing finitary remainder/slice theorems are packaged pointwise over stages, and the final existential theorem uses the ordered face list already produced by D1.

**Scope:** C4-3D3 only.  Do not begin Lemma 6.3, C4-3E, or T10-D.

## Review focus

- The minimum face is `ConeLineality (Cone period)`, never assumed to be `{0}`.
- The final-remainder contradiction uses a genuine `StageCandidateFace` at `length faces`.
- All set equalities remain `SameSet`.
- Slice coverage is exactly `initial_remaining \\ excluded`, with D1 pairwise disjointness retained.
- `BackwardPeriodCover` means an existential forward period increment into `excluded`.
- The final theorem merely packages existing existential finite bases; it introduces no choice function.

### Task 1: Terminal remainder

- Add RED checks for `stripping_final_remainder_eq_excluded`.
- Prove `excluded <= R_n` from D1.
- Apply Lemma 6.9 to the lineality face and contradict `stripping_no_candidate_at_end` for any point in `R_n \\ excluded`.
- Focused compile to GREEN.

### Task 2: Complete disjoint partition

- Add RED checks for `stripping_complete_partition` and a public disjointness wrapper.
- Use `stripping_initial_partition`, terminal equality, `ProcessedBefore`, and `stripping_slice_subset_initial_difference`.
- Focused compile to GREEN.

### Task 3: Finite-basis package

- Package remainder finitarity plus excluded containment for every `stage <= n`.
- Package slice finitarity for every in-range `nth_error` face.
- Reuse D2 directly; do not reconstruct WQO or basis selection.
- Focused compile to GREEN.

### Task 4: Empty first slice and final theorem

- Define `BackwardPeriodCover` and prove `stripping_first_slice_empty` from the head-face equation and Extract's universal condition.
- Obtain the ordered list from `ordered_stripping_faces_exists` and assemble `face_stripping_theorem` with all eleven requested properties.
- Focused compile to GREEN.

### Task 5: Regression and verification

- Cover dimension zero, generated zero/N/2N/N²/Z/N×Z cases through generic and concrete prior traces.
- Verify the N trace, the translated 2N trace, lineality, equal/empty sets, and backward cover.
- Register source/audit files, write the D3 audit, run full Coq regression, `coqchk -silent`, `Print Assumptions`, prohibited scan, and `git diff --check`.
- Obtain independent review, fix all Critical/Important findings, commit only D3 targets, and stop.
