# T10-C4-3D2 Lemma 6.11 and slice finitarity audit

## Scope

This checkpoint proves the two Lemma 6.11 stripping invariants, finitarity of
every remainder, maximality of a nonempty current slice, finitarity of every
slice, and absence of candidate faces after the final stage.  It does not
identify the final remainder with `excluded` and does not prove Theorem 6.1.

The implementation reuses the zero-based recursion and reverse-inclusion face
ordering from C4-3D1.  The set `excluded` remains fixed throughout the
recursion.

## Ordered face-list interface

```coq
OrderedStrippingFaces :
  forall d, ZSet d -> list (QSet d) -> Prop
```

This packages the nonempty/head, soundness, completeness up to `SameSet`,
distinct-representative, and reverse-inclusion ordering properties supplied by
`face_stripping_ordered_recursion`.  The public theorem
`ordered_stripping_faces_exists` obtains such a list without defining a
Set-valued choice function or a new enumeration algorithm.

## Lemma 6.11 invariants

```coq
lemma_6_11_stripping_invariants :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
  Periodic period ->
  QCylindric period excluded ->
  QCylindric period initial_remaining ->
  (forall value, excluded value -> initial_remaining value) ->
  OrderedStrippingFaces period faces ->
  (forall stage,
    stage <= length faces ->
    QCylindric period
      (StrippingRemainder period excluded initial_remaining faces stage)) /\
  (forall stage,
    stage <= length faces ->
    forall face,
    StageCandidateFace period excluded initial_remaining faces stage face ->
    exists index representative,
      stage <= index /\
      index < length faces /\
      nth_error faces index = Some representative /\
      SameSet face representative).
```

Remainder cylindricity is an induction using
`extract_remainder_cylindric`, D1 excluded preservation, and the original
fixed `excluded`.  Candidate faces move monotonically backward from stage
`S i` to stage `i`.  The current representative, including any extensionally
equal `QSet`, is eliminated at the successor stage.  Completeness of the face
list gives a representative initially, and successor elimination strengthens
its lower index bound.

## Finitary remainders and slices

```coq
stripping_remainder_finitary :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
  Periodic period ->
  FinitelyGeneratedPeriodic period ->
  QCylindric period excluded ->
  FinitaryQCylindric period initial_remaining ->
  (forall value, excluded value -> initial_remaining value) ->
  OrderedStrippingFaces period faces ->
  forall stage,
  stage <= length faces ->
  FinitaryQCylindric period
    (StrippingRemainder period excluded initial_remaining faces stage).

stripping_slice_finitary :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
  Periodic period ->
  FinitelyGeneratedPeriodic period ->
  FullPeriodic period ->
  FinitaryQCylindric period excluded ->
  FinitaryQCylindric period initial_remaining ->
  (forall value, excluded value -> initial_remaining value) ->
  OrderedStrippingFaces period faces ->
  forall stage face,
  stage < length faces ->
  nth_error faces stage = Some face ->
  FinitaryQCylindric (FacePeriod period face)
    (StrippingSlice period excluded initial_remaining faces stage).
```

Remainder finitarity is the existing C4-3B-0 subset theorem
`finitary_qcylindric_sub`, applied after Lemma 6.11 and the D1 inclusion
`R i` in the initial remainder.  For a slice, the empty case uses
`empty_finitary_qcylindric`; the nonempty case first proves that the current
face is maximal among nonempty Extract faces and then applies the completed
Lemma 6.10 theorem `lemma_6_10_maximal_extract_finitary`.

## Maximality and final-stage exclusion

```coq
stripping_nonempty_slice_maximal_face :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
  Periodic period ->
  OrderedStrippingFaces period faces ->
  forall stage face,
  stage < length faces ->
  nth_error faces stage = Some face ->
  (exists value,
    StrippingSlice period excluded initial_remaining faces stage value) ->
  MaximalNonemptyExtractFace period excluded
    (StrippingRemainder period excluded initial_remaining faces stage) face.

stripping_no_candidate_at_end :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
  Periodic period ->
  OrderedStrippingFaces period faces ->
  forall face,
  ~ StageCandidateFace period excluded initial_remaining
      faces (length faces) face.
```

For nonempty current slices, the rear-representative invariant gives an index
at least `stage`, while reverse inclusion gives an index at most `stage`.
Thus the larger candidate is `SameSet` to the current face.  At the final
stage, the same invariant would require `length faces <= index < length
faces`, which is impossible.

## Regression coverage

`FaceStrippingLemma611Examples.v` checks dimension zero and obtains a valid
ordered-list existence witness from the existing finite-face theorem.  It checks
the full invariant and finitary remainder/slice APIs on `N`; confirms that the
maximum face is not a candidate at stage zero in the established
`X = 2 + N`, `Y = N` trace; confirms the minimum face is a candidate at stage
one; and proves there is no candidate after both faces.  The four standard
faces of the two-dimensional nonnegative quadrant are checked against the
existing reverse-inclusion linearization.  A separate `N^2` example applies
the D2 rear-representative theorem to the ordered quadrant list and retains
the explicit `stage <= index` conclusion.  Existing regressions for `2N`,
`N^2`, `Z`, `N x Z`, empty slices, and nonzero lineality are retained and
referenced.

## Assumption audit

`Print Assumptions` reports `Closed under the global context` for Extract
remaining monotonicity, candidate monotonicity, current-face elimination,
`SameSet` current-face elimination, nonempty-slice maximality, and final-stage
candidate exclusion.  The combined invariant inherits only
`Classical_Prop.classic` from `extract_remainder_cylindric`; remainder
finitarity also inherits it from the existing arbitrary-Prop finite-cover
path.  Slice finitarity uses `Classical_Prop.classic` for
the empty/nonempty split and inherits the already audited Lemma 6.10 path.

No new axiom, admission, abort, `ClassicalEpsilon`, countable/dependent choice,
UIP/K, `Eq_rect_eq`, functional extensionality, or external oracle is used.

## Obligations left to C4-3D3

- apply the no-candidate theorem to the minimum face;
- use Lemma 6.9 to identify the final remainder with `excluded`;
- assemble the finite, pairwise-disjoint slice decomposition;
- package every nonempty slice with its corresponding face-period finite
  basis, while retaining empty slices as appropriate;
- prove the final Theorem 6.1 statement and its optional first-slice
  condition.
