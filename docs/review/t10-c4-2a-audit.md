# T10-C4-2A audit: extensional face order

Baseline: `9f3a1a5755ce5dfc64b8dea0f17a9b67b6b05519`.

The implementation follows Bizière–Leroux–Sutre (2026), Section 6.  The
ordering convention is the paragraph preceding Example 6.2:
`F_i ⊇ F_j` implies `i <= j`.  The converse-looking sentence in Example 6.2
is not used.

## Construction

- `FaceSubset` is pointwise inclusion and `ProperFaceSubset` is inclusion
  together with failure of `SameSet`.
- `deduplicate_same_set` removes duplicates propositionally, using
  `NoDupA SameSet`; it neither compares set functions by Leibniz equality nor
  assumes functional extensionality.  Its output is a `ListSubsequence`, so
  its length cannot exceed the input length.
- `finite_faces_reverse_inclusion_order` repeatedly chooses an
  inclusion-maximal member of the remaining finite list.  Irreflexivity and
  transitivity of proper inclusion establish the topological ordering.
- `polyhedral_faces_linearized` removes representatives extensionally equal
  to the original cone, deduplicates and orders the remaining representatives,
  then prepends the original `cone` itself.  Consequently its head equality is
  Leibniz equality while all duplicate and coverage statements remain
  extensional.

## Verification

- Focused GREEN: `make audit-t10-c4-2a` succeeded.
- `coqchk -silent` succeeded for `Mell.Geometry.FaceOrder` and
  `Mell.Audit.FaceOrderExamples`.
- `Print Assumptions` reports only `Classical_Prop.classic` for the
  proposition-level deduplication/maximal-selection construction.
- The audit rejects `ClassicalEpsilon`, `Eq_rect_eq`, UIP/K, functional
  extensionality, `Admitted`, `Axiom`, and `Abort` in the C4-2A files.

An independent review checked the complete proof, the exact-head property,
the `SameSet` coverage/no-duplicate properties, and the ordering direction;
it reported no blocker or material finding.

The remaining C4-2B obligation is genuine rational-linear dimension and its
strict decrease under proper face inclusion.  It is intentionally not assumed
by C4-2A.
