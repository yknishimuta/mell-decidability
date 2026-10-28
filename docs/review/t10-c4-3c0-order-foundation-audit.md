# T10-C4-3C0 order-foundation audit

Baseline: `9200e9c92278992fc12f0ae62560ba3a45c4dd73`.

## Implemented boundary

This checkpoint stops before C4-3C1 and Lemma 6.10.  It adds:

- `MaximalNonemptyExtractFace` and existence of such a face when a
  polyhedral cone has at least one face with nonempty extraction;
- antitonicity of `ExtractFace` under face inclusion and invariance under
  `SameSet` replacement;
- `finitary_qcylindric_afs`, obtained by transporting the product of finite
  base equality and the period order through `(base, increment) |->
  base + increment`;
- a strong eventually-constant/tail-unbounded dichotomy for nondecreasing
  integer sequences;
- monotonicity of integer supporting-normal inner products along
  `PeriodicLe` chains;
- a finite-list classification into unbounded and eventually constant
  normals, with one common tail index for the constant family.

The Extract direction is intentionally
`ExtractFace larger value -> ExtractFace smaller value`: every increment in
the smaller face period is also an increment in the larger face period.

## Existing APIs used

- finite faces: `polyhedral_faces_finite`, `select_property_subsequence`,
  `finite_list_has_maximal`;
- order: `periodic_order_wqo_iff_finitely_generated`;
- almost-full transport: `afs_eq_fin`, `afs_af_sub_rel`, `af_product`,
  `af_rel_morph`, `af_good_pair`;
- supporting normals: `cone_contains_source`,
  `integer_qinner_nonnegative_iff`, `zinner_zsmul`.

## Infinite subsequence audit

The installed KruskalAfProp API exposes `af_good_pair`:

```coq
forall sequence,
  (forall n, set (sequence n)) ->
  exists n i j,
    i < j < n /\ PeriodicLe period (sequence i) (sequence j).
```

This consequence is published as `finitary_qcylindric_good_pair`.  No
installed theorem was found that turns `afs set R` directly into an infinite
strictly indexed nondecreasing subsequence.  The exact bridge still needed by
C4-3C1 is:

```coq
forall d (period set : ZSet d),
  afs set (PeriodicLe period) ->
  forall sequence : nat -> ZVec d,
    (forall n, set (sequence n)) ->
    exists indices : nat -> nat,
      (forall n, indices n < indices (S n)) /\
      (forall n,
        PeriodicLe period
          (sequence (indices n))
          (sequence (indices (S n)))).
```

Iterating `af_good_pair` over tails would require a countable/dependent
choice bridge not present in the current imports.  C4-3C1 can instead avoid
constructing the entire subsequence at once: use finite translate coverage
and the finite-bad-sequence interpretation of `afs` to obtain each finite
prefix needed by the contradiction argument.  No `ClassicalEpsilon` or
choice oracle was introduced here.

## Axiom audit

`extract_face_antitone`, `extract_face_same_set`, and supporting-normal
monotonicity are closed under the global context.
`maximal_nonempty_extract_face_exists`, `finitary_qcylindric_afs`, the
integer-tail dichotomy, the finite-normal classification, and the good-pair
corollary use only `Classical_Prop.classic` (directly or through
`periodic_order_wqo_iff_finitely_generated` and the installed finite-selection
APIs).  There are no new axioms, admitted proofs,
`ClassicalEpsilon`, UIP/K, `Eq_rect_eq`, functional extensionality, or external
oracles.

## Regression coverage

The focused audit checks exact public types, the Extract inclusion direction
and `SameSet` replacement, maximal-face existence, and direct applications of
the new `afs` theorem to dimension 0, the zero period, `N`, `2N`, `N2`, `Z`,
and a low-rank signed period.  It also checks supporting-normal sequence
monotonicity, constant negative sequences, unbounded natural and
negative-start sequences, an eventually constant sequence, the empty finite
normal family, and a duplicate-normal family.  Existing face and
face-stripping audit suites retain empty/nonempty Extract, maximal/proper face,
and zero-normal geometric coverage.

## Verification

- RED: the focused audit initially marked the three missing C3C0 declarations
  with `Fail Check`; implementation and import-boundary failures were then
  resolved without weakening the statements.
- GREEN: the focused source and audit modules compile.
- Full `make -f Makefile.coq -j2` succeeds.
- `coqchk -silent -Q theories Mell` succeeds for
  `Mell.Geometry.FaceStrippingOrderFoundation` and
  `Mell.Audit.FaceStrippingOrderFoundationExamples`.
- The prohibited-token scan, trailing-whitespace check, and scoped
  `git diff --check` succeed.

## Independent review

An independent read-only review returned `ready` with no Critical, Important,
or Minor findings after two review findings were corrected: the audit now
records the inherited `Classical_Prop.classic` dependency of
`finitary_qcylindric_afs`, and the focused regression directly connects the
new theorems to all requested representative periods and duplicate normals.
