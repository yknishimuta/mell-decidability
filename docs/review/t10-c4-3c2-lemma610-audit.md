# T10-C4-3C2 Lemma 6.10 assembly audit

## Scope and status

This checkpoint completes C2-1 through C2-4: translation of the two finitary
sets, normalization of an arbitrary Extract sequence into the period, the C1B
geometric collapse, and the second monotone-subsequence extraction.  C2-5 is
blocked at the constructive connection from the resulting infinite-sequence
property to the library's inductive `afs` predicate.  Accordingly,
`lemma_6_10_maximal_extract_finitary` is not declared and Lemma 6.11 and later
work are untouched.

The implementation is in `theories/Geometry/FaceStrippingLemma610.v`; focused
checks and assumption output are in
`theories/Audit/FaceStrippingLemma610Examples.v`.

## Translation and normalization

`ShiftedSet anchor set value` is `set (anchor + value)`.  The module proves
that QCylindricity, finitary QCylindricity, inclusion, `ExtractFace`, and
`MaximalNonemptyExtractFace` are preserved when excluded and remaining are
translated together.  The key equivalence is:

```coq
shifted_extract_face :
  forall d period excluded remaining face anchor value,
    ExtractFace period face
      (ShiftedSet anchor excluded) (ShiftedSet anchor remaining) value <->
    ExtractFace period face excluded remaining (zvec_add anchor value)
```

`maximal_extract_first_normalization` first extracts a Q-monotone subsequence
inside `remaining`, takes its reindexed zeroth term as anchor, and subtracts
that anchor from the whole subsequence.  The normalized zeroth term is zero,
every normalized term is in `period`, the sequence remains Q-monotone, and it
lies in the translated Extract problem.  This directly handles the specified
`2N` / `1 + 2N` counterexample: no original Extract value is assumed to lie in
the period.

## Geometry and the two subsequences

`finitely_generated_period_cone_polyhedral` supplies the minimal bridge from a
finitely generated period to `RationalPolyhedralCone (Cone period)`.

`maximal_extract_monotone_subsequence` then composes:

1. the first monotone subsequence in `remaining`;
2. anchor subtraction;
3. the common integer H-representation;
4. finite supporting-normal tail reindexing;
5. `maximal_extract_prepared_chain_face_collapse` on the translated problem;
6. the second monotone subsequence inside the C1B threshold slice; and
7. transport from the C1B face back to the original face by `SameSet`.

Its final index function is the composition of the first indices, the common
tail shift, and the second indices.  Strict increase is proved explicitly.

## C2-5 blocker

The available order API proves the forward implication

```coq
finitary_qcylindric_afs :
  FinitaryQCylindric period set -> afs set (PeriodicLe period)
```

and `restricted_af_finite_cover_classic` converts an already established
`afs` proof into a finite cover.  There is no converse theorem from

```coq
forall sequence : nat -> ZVec d,
  (forall n, ExtractFace ... (sequence n)) ->
  exists indices,
    StrictlyIncreasing indices /\
    forall n, PeriodicLe (FacePeriod period face)
      (sequence (indices n)) (sequence (indices (S n)))
```

to the inductive `afs` predicate.

The standard contradiction constructs an infinite bad sequence by repeatedly
choosing an Extract element escaping a finite prefix.  In Coq this requires
either a countable/dependent choice principle, which the contract forbids, or
a decidable enumeration of `ExtractFace`.  Existing constructive least-code
search (`constructive_indefinite_description_nat`) works only for decidable
predicates.  The repository provides decidable finite generated
representations and linear equations, but no decision theorem for the
universally quantified `ExtractFace` predicate.  Producing one would require a
new Presburger/semilinear decision connection outside the approved C3C2
assembly scope.

The exact missing bridge can be supplied in either of these permitted forms:

```coq
extract_face_dec :
  forall d period excluded remaining face value,
    (* the current finite-generation/finitary hypotheses *) ->
    {ExtractFace period face excluded remaining value} +
    {~ ExtractFace period face excluded remaining value}
```

together with a countable least-code finite-cover argument, or a verified
choice-free theorem connecting the displayed infinite-subsequence property to
`afs`.  The least-code route also needs

```coq
face_periodic_le_dec :
  forall d period face left right,
    (* the current finite-generation/face hypotheses *) ->
    {PeriodicLe (FacePeriod period face) left right} +
    {~ PeriodicLe (FacePeriod period face) left right}
```

to decide whether a candidate escapes a finite bad prefix.  Neither direct
decision API nor the sequence-to-`afs` theorem exists in the current
dependency set.

## Assumptions

The translation lemmas and the finitely-generated-cone bridge are closed under
the global context.  The normalization and final two-stage subsequence theorem
inherit only `Classical_Prop.classic` from finite face/normal selection.  No
choice axiom, `ClassicalEpsilon`, functional extensionality, UIP/K,
`Eq_rect_eq`, new axiom, admitted proof, or aborted proof is introduced.

## Independent review

An independent source/API review confirmed the translation direction, the
anchor normalization, the strict composite indices, the cancellation of the
common anchor, the `SameSet` transport, and the stated axiom dependencies.  It
also independently found no existing sequence-to-`afs` converse.  The review
noted that both Extract membership and the face-period order relation must be
decidable for the least-code alternative above.

The focused regression proves the generic zero-shift and zero-shift Extract
identities.  The requested concrete `2N`, proper-face `2N^2`, and explicit
two-index examples were not completed before the C2-5 blocker; they must not be
reported as formally exercised examples, although the generic normalization
and composite-index theorems cover their mechanisms.

## Verification

- RED: the focused audit initially used `Fail Check` for the absent C3C2
  declarations.
- GREEN for the completed scope: the new source and focused audit compile both
  directly and through `Makefile.coq`.
- The complete `_CoqProject` build has no pending or failing target.
- `coqchk -silent` succeeds for the source and focused audit modules.
- The prohibited-construction scan and target-scoped `git diff --check`
  succeed.
- `lemma_6_10_maximal_extract_finitary` deliberately remains absent and is
  guarded by `Fail Check` in the focused audit.
