# Task 11-D face-stripping audit

## Scope and source

This audit records the Task 11-D verification of Section 6 of
Bizière–Leroux–Sutre, *Solving the Reachability Problem for Branching Vector
Addition Systems via Semilinear Inductive Invariants*, arXiv:2607.09558v1.
The Section 6 Gallina development was already present in the canonical T10-C
geometry modules. Task 11-D preserves those public contracts and adds a
focused kernel-checked audit for corrections R07--R09. Task 11-E is outside
this change.

All carrier sets in this development have type `ZSet d`. In particular,
signed period elements are not replaced by natural vectors, and fullness is
the existing `FullPeriodic` predicate rather than an identification of the
difference group with the whole integer lattice.

## Public theorem contracts

The face restriction of a finitely generated period remains finitely
generated:

```coq
face_periodic_finitely_generated :
  forall d (period : ZSet d) (face : QSet d),
    FinitelyGeneratedPeriodic period ->
    FaceOf (Cone period) face ->
    FinitelyGeneratedPeriodic (FacePeriod period face).
```

Its full-period companion, added by Task 11-D, is constructive:

```coq
face_period_full :
  forall d (period : ZSet d) (face : QSet d),
    Periodic period -> FullPeriodic period ->
    FaceOf (Cone period) face ->
    FullPeriodic (FacePeriod period face).
```

It uses `Difference period` as the integer additive group and the selected
face as the rational cone; it does not enlarge the difference group to
`Z^d`.

The common zero-pattern witness (paper Lemma 6.5) is:

```coq
face_zero_pattern_witness :
  forall d (period : ZSet d) (face : QSet d)
    (normals : list (ZVec d)),
    Periodic period ->
    FaceOf (Cone period) face ->
    Forall (fun normal =>
      SupportingNormal (Cone period) (zvec_to_qvec normal)) normals ->
    exists witness,
      FacePeriod period face witness /\
      forall normal, In normal normals ->
        (IntegerNormalOrthogonalToFace face normal <->
         qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0).
```

The residual cylindricity result (Lemma 6.8) is:

```coq
extract_remainder_cylindric :
  forall d (period excluded remaining : ZSet d) (face : QSet d),
    Periodic period -> FaceOf (Cone period) face ->
    QCylindric period excluded -> QCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    QCylindric period
      (fun value => remaining value /\
        ~ ExtractFace period face excluded remaining value).
```

The minimal-face result (Lemma 6.9) uses cone lineality, not an assumed zero
face:

```coq
lemma_6_9_minimal_extract :
  forall d (period excluded remaining : ZSet d),
    Periodic period -> FinitelyGeneratedPeriodic period ->
    FullPeriodic period -> QCylindric period excluded ->
    QCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    SameSet
      (ExtractFace period (ConeLineality (Cone period)) excluded remaining)
      (fun value => remaining value /\ ~ excluded value).
```

The maximal-face finite-basis result (Lemma 6.10) is:

```coq
lemma_6_10_maximal_extract_finitary :
  forall d (period excluded remaining : ZSet d) (face : QSet d),
    Periodic period -> FinitelyGeneratedPeriodic period ->
    FullPeriodic period -> FinitaryQCylindric period excluded ->
    FinitaryQCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    MaximalNonemptyExtractFace period excluded remaining face ->
    FinitaryQCylindric (FacePeriod period face)
      (ExtractFace period face excluded remaining).
```

The stage invariant (Lemma 6.11) is:

```coq
lemma_6_11_stripping_invariants :
  forall d (period excluded initial_remaining : ZSet d) faces,
    Periodic period -> QCylindric period excluded ->
    QCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces ->
    (forall stage, stage <= length faces ->
      QCylindric period
        (StrippingRemainder period excluded initial_remaining faces stage)) /\
    (forall stage, stage <= length faces -> forall face,
      StageCandidateFace period excluded initial_remaining faces stage face ->
      exists index representative,
        stage <= index /\ index < length faces /\
        nth_error faces index = Some representative /\
        SameSet face representative).
```

The complete Theorem 6.1 package is `face_stripping_theorem`. It returns an
ordered face list starting with `Cone period`, initial/final remainder
equalities, finitary cylindricity and preservation of the excluded set for
every remainder, finitary `FacePeriod`-cylindricity for every slice,
pairwise disjointness, an iff characterizing the union of all slices as
`initial_remaining \ excluded`, and emptiness of the maximal-cone slice
under `BackwardPeriodCover`.

```coq
face_stripping_theorem :
  forall d (period excluded initial_remaining : ZSet d),
    Periodic period -> FinitelyGeneratedPeriodic period ->
    FullPeriodic period -> FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    exists faces : list (QSet d),
      OrderedStrippingFaces period faces /\
      nth_error faces 0 = Some (Cone period) /\
      SameSet
        (StrippingRemainder period excluded initial_remaining faces 0)
        initial_remaining /\
      SameSet
        (StrippingRemainder period excluded initial_remaining
          faces (length faces))
        excluded /\
      (forall stage, stage <= length faces ->
        FinitaryQCylindric period
          (StrippingRemainder period excluded initial_remaining
            faces stage) /\
        forall value, excluded value ->
          StrippingRemainder period excluded initial_remaining
            faces stage value) /\
      (forall stage face, stage < length faces ->
        nth_error faces stage = Some face ->
        FinitaryQCylindric (FacePeriod period face)
          (StrippingSlice period excluded initial_remaining faces stage) /\
        forall value,
          StrippingSlice period excluded initial_remaining faces stage value ->
          initial_remaining value /\ ~ excluded value) /\
      (forall earlier later, earlier < later -> later < length faces ->
        forall value,
          ~ (StrippingSlice period excluded initial_remaining
                faces earlier value /\
             StrippingSlice period excluded initial_remaining
                faces later value)) /\
      (forall value,
        initial_remaining value /\ ~ excluded value <->
        exists stage, stage < length faces /\
          StrippingSlice period excluded initial_remaining
            faces stage value) /\
      (BackwardPeriodCover period excluded initial_remaining ->
        forall value,
          ~ StrippingSlice period excluded initial_remaining faces 0 value).
```

The proper-face rank decrease is:

```coq
proper_face_dimension_lt :
  forall d (cone face larger : QSet d)
    face_dimension larger_dimension,
    RationalPolyhedralCone cone -> FaceOf cone face -> FaceOf cone larger ->
    ProperFaceSubset face larger ->
    SpanDimension face face_dimension ->
    SpanDimension larger larger_dimension ->
    face_dimension < larger_dimension.
```

The stripping-list bridge required for the rank argument is:

```coq
ordered_stripping_noninitial_face_proper :
  forall d (period : ZSet d) faces index face,
    OrderedStrippingFaces period faces -> 0 < index ->
    nth_error faces index = Some face ->
    ProperFaceSubset face (Cone period).

ordered_stripping_noninitial_face_dimension_lt :
  forall d (period : ZSet d) faces index face face_dimension cone_dimension,
    Periodic period -> FinitelyGeneratedPeriodic period ->
    OrderedStrippingFaces period faces -> 0 < index ->
    nth_error faces index = Some face ->
    SpanDimension face face_dimension ->
    SpanDimension (Cone period) cone_dimension ->
    face_dimension < cone_dimension.
```

The directional Lemma 6.3 contract is:

```coq
lemma_6_3_stripping_diagonal :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d)) (relation : ZVec d -> ZVec d -> Prop),
    Periodic period -> FinitelyGeneratedPeriodic period ->
    FullPeriodic period -> FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces -> QDiagonal period relation ->
    NoBoundaryEdge excluded initial_remaining relation ->
    forall earlier later left right,
      earlier < later -> later < length faces ->
      StrippingSlice period excluded initial_remaining faces later left ->
      StrippingSlice period excluded initial_remaining faces earlier right ->
      ~ relation left right.
```

`face_stripping_theorem_diagonal` packages the same face witness returned by
Theorem 6.1 together with this directional conclusion.

## Extract and corrections R07--R09

`ExtractFace period face excluded remaining value` is definitionally

```coq
forall increment,
  FacePeriod period face increment ->
  remaining (value + increment) /\ ~ excluded (value + increment).
```

Thus the first set is the removed/lower set and the second set is the current
remainder. The focused R08 regression proves that for `Q = N`, excluded
`{z | 1 <= z}`, remaining `{z | 0 <= z}`, and the zero face, the correct
argument order extracts zero while the reversed order cannot extract zero.

For R07, the maximal-face proof uses `PeriodicLe`, hence period membership of
successive differences, and forms the corrected remainder from
`sequence(index) - sequence(0)`, the tested face increment, and a scaled
zero-pattern witness. Membership in `Q` is obtained only after proving both
`Difference Q` and `Cone Q` and applying fullness. It never infers that an
arbitrary translated sequence element belongs to `Q`. The focused regression
exhibits a chain whose origin is `-1`, outside `N`, while every successive
difference is in `N`.

The proof does use `corollary_6_7_finitary` for the rational threshold slice
needed to build a finite basis. This is not the invalid R07 step: the direct
difference argument remains the source of period membership, while the
corollary supplies finitary cylindricity of an auxiliary slice. No claim that
the raw sequence lies in the period is derived from it.

For R09, indices are the actual zero-based list indices. Lemma 6.3 forbids a
relation edge from a later slice to an earlier slice. The converse is not
asserted; the imported concrete regression
`d3e_allowed_earlier_to_later_edge` kernel-checks an earlier-to-later edge.

## Geometry and stripping invariants

Faces are represented extensionally by `QSet d`, with `FaceOf`, and the
finite reverse-inclusion linearization is captured by
`OrderedStrippingFaces`. `polyhedral_faces_linearized` supplies a duplicate-
free list beginning with the whole cone. `FacePeriod` is the exact integer
period/face intersection. Its finite generation follows from the existing
lattice-Gordan geometry and never substitutes the ambient `Z^d` for the
difference group.

The stripping recursion starts with `initial_remaining`, extracts
`ExtractFace ... excluded remainder` at each face, and removes that slice.
Lemma 6.8 preserves cylindricity; Lemma 6.11 confines every remaining
nonempty candidate to the unprocessed suffix. The final minimal face extracts
the entire residual difference by Lemma 6.9. These facts yield both directions
of coverage and pairwise disjointness in Theorem 6.1.

## Axiom and trust-boundary audit

`Print Assumptions` was run for every principal declaration. The focused
R07--R09 examples add no assumptions. `face_period_full`,
`ordered_stripping_noninitial_face_proper`, and `proper_face_dimension_lt`
are closed under the global context. The noninitial-face dimension bridge and
the remaining principal geometry/finite-basis results report at most the
already-established `Classical_Prop.classic`; no new axiom or choice principle
is introduced.

The task files contain no `Axiom`, `Admitted`, `admit`, `Abort`,
`ClassicalEpsilon`, `ClassicalChoice`, UIP/K, `Eq_rect_eq`, functional
extensionality, or disabled kernel checks.

## Verification

- Direct focused `coqc` compilation of `FaceStrippingSection6.v` and the
  Task 11-D audit module: PASS.
- Focused `Makefile.coq` build of all Section 6 modules, T10-G finite-cover
  audit, and Task 11-A--C regression modules: PASS.
- Forced complete `_CoqProject` rebuild (`make -f Makefile.coq -B -j2`):
  PASS.
- `make -f Makefile.coq validate`, including whole-project dependency-closure
  `coqchk -silent`: PASS.
- Explicit `coqchk -silent` for the new bridge, Theorem 6.1, Lemma 6.3, and
  the focused audit module: PASS.
- Public `Check` and `Print Assumptions`: PASS.
- New-source forbidden-construction scan: PASS.
- Task-scoped whitespace check: PASS.

The global unstaged `git diff --check` still reports only pre-existing
trailing whitespace in protected conditional-audit log files. Those files
were not changed for Task 11-D and are not staged.

## Independent review

An independent read-only review first identified the missing arbitrary-face
fullness and stripping-list dimension bridges. After those exact helpers were
added, the reviewer checked their proofs, R07--R09, maximality/fullness in
Lemma 6.10, complete/disjoint/finitary decomposition, Corollary 6.7's actual
non-circular role, and the Lemma 6.3 direction. Final disposition: **PASS**,
with no unresolved findings.

## Git information and obligations

- Branch: `work/mell-formalization`
- Baseline: `584d8dfa58ffa5074b5f176b24c45264df452860`
- Result commit: recorded by Git history and the completion report
- Unresolved Task 11-D proof obligations: none at the focused-check stage
- Push performed: no
