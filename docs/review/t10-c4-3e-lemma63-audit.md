# T10-C4-3E Lemma 6.3 audit

## Scope

This checkpoint formalizes the directional relation property of
Bizière–Leroux–Sutre Lemma 6.3 and combines it with the completed Theorem
6.1 package.  It proves only that an edge from a later slice to an earlier
slice is impossible.  It does not prohibit the reverse direction and does
not assume that the relation is symmetric, transitive, or reflexive.

No T10-D/E/F or Section 7 result is implemented.

## Relation predicates

```coq
Definition QDiagonal {d}
    (period : ZSet d)
    (relation : ZVec d -> ZVec d -> Prop) : Prop :=
  forall left right increment,
    relation left right ->
    period increment ->
    relation
      (zvec_add left increment)
      (zvec_add right increment).

Definition NoBoundaryEdge {d}
    (excluded remaining : ZSet d)
    (relation : ZVec d -> ZVec d -> Prop) : Prop :=
  forall left right,
    relation left right ->
    excluded left ->
    remaining right ->
    ~ excluded right ->
    False.
```

Thus `NoBoundaryEdge X Y R` represents the emptiness of
`R ∩ (X × (Y \ X))`, with no reversal of the endpoints.

## Structural bridges

```coq
stripping_slice_face_cylindric :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)) stage face,
  Periodic period ->
  (forall candidate,
    List.In candidate faces -> FaceOf (Cone period) candidate) ->
  nth_error faces stage = Some face ->
  QCylindric
    (FacePeriod period face)
    (StrippingSlice period excluded initial_remaining faces stage).
```

This theorem needs neither finite generation, fullness, nor finitarity.  It
rewrites the slice to its `ExtractFace`, obtains periodicity of the face
period via `face_periodic`, and applies `extract_face_cylindric`.

```coq
stripping_later_slice_in_earlier_remainder :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)) earlier later,
  Periodic period ->
  (forall face,
    List.In face faces -> FaceOf (Cone period) face) ->
  earlier < later ->
  later < length faces ->
  forall value,
    StrippingSlice period excluded initial_remaining faces later value ->
    StrippingRemainder period excluded initial_remaining faces earlier value.
```

It combines `stripping_slice_subset_remainder` at `later` with
`stripping_remainder_decreasing` from `later` to `earlier`.

## Lemma 6.3

```coq
lemma_6_3_stripping_diagonal :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d))
    (relation : ZVec d -> ZVec d -> Prop),
  Periodic period ->
  FinitelyGeneratedPeriodic period ->
  FullPeriodic period ->
  FinitaryQCylindric period excluded ->
  FinitaryQCylindric period initial_remaining ->
  (forall value, excluded value -> initial_remaining value) ->
  OrderedStrippingFaces period faces ->
  QDiagonal period relation ->
  NoBoundaryEdge excluded initial_remaining relation ->
  forall earlier later left right,
    earlier < later ->
    later < length faces ->
    StrippingSlice period excluded initial_remaining faces later left ->
    StrippingSlice period excluded initial_remaining faces earlier right ->
    ~ relation left right.
```

The internal theorem `lemma_6_3_stripping_diagonal_core` is stronger: it
does not require finite generation, fullness, or finitarity, and instead
receives the cylindricity of all remainders directly.  The public theorem
derives that premise from `lemma_6_11_stripping_invariants`.

For a supposed edge `R(left,right)` from slice `later` to slice `earlier`,
the proof translates `right` by every member of the earlier face period.
Slice cylindricity keeps the translated right endpoint in
`initial_remaining \ excluded`.  Diagonality translates the edge, so the
boundary prohibition makes the translated left endpoint non-excluded.
The later-slice bridge and Lemma 6.11 keep that endpoint in the earlier
remainder.  Hence `left` satisfies the earlier Extract, contradicting slice
disjointness.

## Theorem 6.1 integration

`face_stripping_theorem_diagonal` returns one list `faces`.  Its first
conjunct is the complete, unchanged conclusion package returned by
`face_stripping_theorem`: ordered faces, head cone, initial and final
remainders, all finite-basis results, slice containment, disjointness,
complete coverage, and optional first-slice emptiness.  Its second conjunct
is the Lemma 6.3 later-to-earlier prohibition.  The proof destructs
`face_stripping_theorem` exactly once and applies Lemma 6.3 to that same
witness; it does not enumerate or select a second face list.

## Directional regression

The audit defines the asymmetric translation relation

```coq
d3e_shift_one_relation left right :=
  right = zvec_add left (d0_z1 1).
```

It proves that this relation is Q-diagonal for every one-dimensional
period, proves the concrete edge `R(0,1)`, and disproves `R(1,0)`.  It also
checks the public theorem with this asymmetric relation on the established
`Q = N`, `X = 2 + N`, `Y = N` setting.  Consequently the regression does
not smuggle relation symmetry into the theorem: only
`R(S_later,S_earlier)` is ruled out.

A second regression makes the permitted reverse direction explicit.  For
`Q = 2N`, `Y = N`, `X = 2 + 2N`, and the ordered faces consisting of the
whole cone followed by its lineality face, the earlier slice contains `1`
and the later slice contains `0`.  The relation generated from the edge
`R(1,0)` by simultaneous `2N` translations is Q-diagonal and satisfies
`NoBoundaryEdge`: every left endpoint is odd whereas `X` contains only even
points.  The proved edge from the earlier slice to the later slice therefore
shows concretely that the theorem does not forbid the reverse orientation.
Empty and identity relations are also proved Q-diagonal.  Existing
dimension-zero, `2N`, `N^2`, `Z`, `N x Z`, nonzero-lineality, empty-slice,
and multiple-nonempty-slice regressions are referenced.

## Assumption audit

`Print Assumptions` reports:

- `stripping_slice_face_cylindric`: closed under the global context;
- `stripping_later_slice_in_earlier_remainder`: closed under the global
  context;
- `lemma_6_3_stripping_diagonal_core`: closed under the global context;
- `lemma_6_3_stripping_diagonal`: only `Classical_Prop.classic`, inherited
  from `lemma_6_11_stripping_invariants`;
- `face_stripping_theorem_diagonal`: only `Classical_Prop.classic`, inherited
  from Theorem 6.1 and the preceding public theorem.

No new axiom, admission, abort, `ClassicalEpsilon`, countable/dependent
choice, UIP/K, `Eq_rect_eq`, functional extensionality, or external oracle
is used.

## Remaining connections

T10-C4 is complete through Lemma 6.3.  T10-D/E/F may consume the complete
finite face-stripping package and its directional diagonal relation theorem;
they remain outside this checkpoint.
