# T10-C4-3D1 Face-Stripping finite recursion audit

## Scope and convention

This checkpoint implements only the finite, zero-based stripping recursion that
prepares Lemma 6.11.  It does not prove cylindricity/finitarity of intermediate
remainders, apply Lemma 6.10 to a stage, identify the final remainder, or prove
Theorem 6.1.

For `faces : list (QSet d)`, stage zero starts at `initial_remaining`.
At an in-range stage `i`, the slice is
`ExtractFace period faces[i] excluded (R i)` and `R (S i)` removes that slice.
The fixed set `excluded` is never updated.  `nth_error` is used throughout:
an out-of-range slice is empty, and an out-of-range successor leaves the
remainder unchanged, so no fictitious face is introduced.

## Public definitions

```coq
StrippingRemainder :
  forall d : nat,
    ZSet d -> ZSet d -> ZSet d -> list (QSet d) -> nat -> ZSet d

StrippingSlice :
  forall d : nat,
    ZSet d -> ZSet d -> ZSet d -> list (QSet d) -> nat -> ZSet d

ProcessedBefore :
  forall d : nat,
    ZSet d -> ZSet d -> ZSet d -> list (QSet d) -> nat -> ZSet d

StageCandidateFace :
  forall d : nat,
    ZSet d -> ZSet d -> ZSet d -> list (QSet d) -> nat -> QSet d -> Prop
```

`StageCandidateFace period excluded initial_remaining faces i face` means
`face` is a face of `Cone period` and its Extract against `R i` is nonempty.
This records the D2 interface without proving its tail-occurrence invariant.

## Recursion equations

```coq
stripping_remainder_zero :
  forall d period excluded initial_remaining faces,
    SameSet
      (StrippingRemainder period excluded initial_remaining faces 0)
      initial_remaining

stripping_slice_spec :
  forall d period excluded initial_remaining faces stage face,
    stage < length faces ->
    nth_error faces stage = Some face ->
    SameSet
      (StrippingSlice period excluded initial_remaining faces stage)
      (ExtractFace period face excluded
        (StrippingRemainder period excluded initial_remaining faces stage))

stripping_remainder_succ :
  forall d period excluded initial_remaining faces stage,
    stage < length faces ->
    SameSet
      (StrippingRemainder period excluded initial_remaining faces (S stage))
      (fun value =>
        StrippingRemainder period excluded initial_remaining faces stage value /\
        ~ StrippingSlice period excluded initial_remaining faces stage value)
```

The public `stripping_slice_out_of_range` additionally proves that a slice at
`length faces <= stage` is empty.

## Set invariants

The implementation proves:

- every remainder is contained in the initial remainder;
- every in-range slice is contained in its current remainder and avoids
  `excluded`, hence lies in `initial_remaining \ excluded`;
- if `excluded` is initially contained in `initial_remaining`, it remains in
  every `R i` for `i <= length faces`;
- for `i <= length faces`, `R i` is exactly the initial remainder minus
  `ProcessedBefore i`;
- the initial remainder is the union of `R i` and `ProcessedBefore i`, and the
  two sets are disjoint;
- slices at two distinct increasing in-range stages are disjoint.

All set equalities are `SameSet`; no function extensionality is used.

## Finite ordered face list

`face_stripping_ordered_recursion` combines
`finitely_generated_period_cone_polyhedral` and
`polyhedral_faces_linearized`.  From a periodic finitely generated period it
returns one nonempty list whose head is `Cone period`, whose members are all
faces, which represents every face up to `SameSet`, has no two distinct
positions representing the same face, and satisfies the reverse-inclusion
order

```text
FaceSubset face_j face_i -> i <= j.
```

The theorem also exposes the initial equation `R 0 = initial_remaining`.
No face enumeration algorithm or Set-valued choice function is introduced.

## Regression coverage

`FaceStrippingRecursionExamples.v` checks dimension zero, the zero period,
`N`, `2N`, `N^2`, `Z`, and `N x Z`, including the nonzero lineality direction
of `N x Z`.  It covers empty initial remaining, equal excluded/remaining,
single-face lists, an out-of-range empty slice, and one valid two-face `N`
run where both stage 0 and stage 1 slices are nonempty.

The concrete `N` trace with faces `[Cone N; ConeLineality (Cone N)]` proves
`S 0 = empty`, `S 1 = {0,1}`, `R 0 = N`, `R 1 = N`, and `R 2 = 2+N`.
The `2N` translate regression proves that for `Y = 1+2N`, empty excluded, and
the maximum face only, `S 0 = Y` and `R 1 = empty`.

## Assumption audit

`Print Assumptions` reports `Closed under the global context` for the core
recursion equations, excluded preservation, remainder characterization, and
slice disjointness.  `stripping_initial_partition` uses
`Classical_Prop.classic` exactly once to split on membership in the
arbitrary-Prop set `ProcessedBefore`; no decidability of `QSet` or Extract is
assumed.  `face_stripping_ordered_recursion` also inherits
`Classical_Prop.classic` through the existing finite-face linearization
theorem.  No new axiom, admission, choice oracle, UIP/K, proof irrelevance,
`Eq_rect_eq`, or functional extensionality is introduced.

## Obligations deliberately left to C4-3D2

- `QCylindric period (R i)` for all `i <= length faces`;
- a proof that every `StageCandidateFace i face` has a `SameSet`
  representative at position `i` or later;
- maximal-nonempty-face identification at a nonempty stage;
- use of Lemma 6.10 to obtain finitary slices;
- finitary/cylindric properties of remainders;
- identification of the final remainder with `excluded`;
- the Theorem 6.1 decomposition and its optional first-slice condition.

The source paper's one-based presentation is intentionally translated to the
zero-based convention above.
