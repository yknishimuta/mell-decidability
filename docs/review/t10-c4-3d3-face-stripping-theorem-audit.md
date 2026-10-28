# T10-C4-3D3 Face-Stripping Theorem 6.1 audit

## Scope

This checkpoint completes the finite face-stripping construction of Theorem
6.1.  It identifies the final remainder with `excluded`, proves that the
slices form an exact pairwise-disjoint partition of
`initial_remaining \ excluded`, packages the existing finite-basis results
for every remainder and slice, and proves the optional empty-first-slice
condition.  It does not implement Lemma 6.3 or any C4-3E result.

The implementation retains the established zero-based convention and the
argument order `excluded = X`, `initial_remaining = Y`.

## Final remainder

```coq
stripping_final_remainder_eq_excluded :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
  Periodic period ->
  FinitelyGeneratedPeriodic period ->
  FullPeriodic period ->
  FinitaryQCylindric period excluded ->
  FinitaryQCylindric period initial_remaining ->
  (forall value, excluded value -> initial_remaining value) ->
  OrderedStrippingFaces period faces ->
  SameSet
    (StrippingRemainder period excluded initial_remaining faces
      (length faces))
    excluded.
```

The forward inclusion uses the actual minimum face
`ConeLineality (Cone period)`.  Lemma 6.9 identifies its final-stage Extract
with the set difference between the final remainder and `excluded`.  Any
point in that difference would make the lineality face a final-stage
candidate, contradicting `stripping_no_candidate_at_end`.  No pointedness or
zero-lineality assumption is introduced.

## Exact partition

```coq
stripping_complete_partition :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
  Periodic period ->
  FinitelyGeneratedPeriodic period ->
  FullPeriodic period ->
  FinitaryQCylindric period excluded ->
  FinitaryQCylindric period initial_remaining ->
  (forall value, excluded value -> initial_remaining value) ->
  OrderedStrippingFaces period faces ->
  forall value,
    (initial_remaining value /\ ~ excluded value) <->
    exists stage,
      stage < length faces /\
      StrippingSlice period excluded initial_remaining faces stage value.
```

The forward direction applies `stripping_initial_partition` at the terminal
stage and rules out its remainder case with the final-remainder theorem.  The
reverse direction is `stripping_slice_subset_initial_difference`.  Pairwise
disjointness is exported separately as
`stripping_partition_slices_disjoint`, directly preserving the D1 theorem.

## Finite-basis package

`stripping_finitary_stage_package` returns, in one proposition-level package:

- for every `stage <= length faces`, a finite period-basis for the remainder
  and preservation of `excluded` in that remainder; and
- for every `stage < length faces` and the face found by `nth_error`, a finite
  `FacePeriod`-basis for the corresponding slice.

It reuses `stripping_remainder_finitary` and `stripping_slice_finitary`; no
new WQO, basis-selection function, or executable choice operation is added.

## First slice

```coq
Definition BackwardPeriodCover {d}
    (period excluded remaining : ZSet d) : Prop :=
  forall value,
    remaining value ->
    exists increment,
      period increment /\
      excluded (zvec_add value increment).

stripping_first_slice_empty :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)),
  Periodic period ->
  OrderedStrippingFaces period faces ->
  BackwardPeriodCover period excluded initial_remaining ->
  forall value,
    ~ StrippingSlice period excluded initial_remaining faces 0 value.
```

The ordered list supplies `faces[0] = Cone period`.  A covering period
increment belongs to `FacePeriod period (Cone period)`, contradicting the
universal exclusion clause of the first Extract instantiated at that
increment.  The theorem does not
replace the required backward-period cover by the weaker inclusion
`excluded` in `initial_remaining`.

## Theorem 6.1 package

`face_stripping_theorem` obtains the common ordered face list from
`ordered_stripping_faces_exists`.  `OrderedStrippingFaces` already packages
nonemptiness, the head cone, all faces up to `SameSet`, distinct
representatives, and reverse-inclusion order.  The theorem additionally
packages the initial and final remainders, all remainder and slice finite
bases, containment in the set difference, pairwise disjointness, exact
coverage, and the optional first-slice conclusion.

## Regression coverage

`FaceStrippingTheoremExamples.v` applies the complete theorem to the concrete
`Q = N`, `X = 2 + N`, `Y = N` trace, including its backward-period cover.  It
retains and checks the established exact trace `S_0 = empty`,
`S_1 = {0,1}`, `R_2 = X`, and the translated `Q = 2N`, `X = empty`,
`Y = 1 + 2N` trace `S_0 = Y`, `R_1 = empty`.  Existing dimension-zero,
empty/equal-set, `N^2`, `Z`, and nonzero-lineality (`N x Z`) regressions are
also referenced.  In particular, the final-remainder proof uses lineality
rather than assuming that every minimum face is the zero cone.

## Assumption audit

`Print Assumptions` reports:

- `stripping_partition_slices_disjoint`: closed under the global context;
- `stripping_first_slice_empty`: closed under the global context;
- `stripping_final_remainder_eq_excluded`,
  `stripping_complete_partition`, `stripping_finitary_stage_package`, and
  `face_stripping_theorem`: only `Classical_Prop.classic`.

The classical dependency is inherited from the already audited finite-face,
remainder, and finite-basis paths, plus the proposition-level final-remainder
membership split.  There is no new axiom, admission, abort,
`ClassicalEpsilon`, countable/dependent choice, UIP/K, `Eq_rect_eq`,
functional extensionality, or external oracle.

## Obligations left to C4-3E

C4-3E retains Lemma 6.3 and its use of the completed finite disjoint
face-stripping decomposition.  No C4-3E definition or proof is introduced by
this checkpoint.
