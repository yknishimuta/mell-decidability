# T10-C4-3B-1-B4 audit

Baseline: `53ce1225200546daa599373698d84a4efd2a7d01`.

Scope: Bizière–Leroux–Sutre Corollary 6.7.  This change stops after the
finite-basis result for rational threshold slices.  Lemma 6.10 and the
face-stripping theorem are not implemented.

## B4-0: public objects

`ThresholdFace C K` is `C` intersected with the zero hyperplanes indexed by
`K`.  `RationalThresholdSlice Q E K lambda` retains membership in `Q`, lower
bounds for every normal in `E`, and equalities for every normal in `K`.
Duplicates in either list are retained.

## B4-1: integer inner products and rational thresholds

`qinner_zvec_to_qvec` proves that rationalizing two integer vectors commutes
with the integer inner product.  The ceiling interface is:

```coq
integer_ge_rational_iff_ceiling :
  forall (n : Z) (r : Q),
    r <= inject_Z n <-> (Qceiling r <= n)%Z

integer_eq_rational_iff_two_ceilings :
  forall (n : Z) (r : Q),
    inject_Z n == r <->
      (Qceiling r <= n)%Z /\
      (Qceiling (- r) <= - n)%Z
```

Thus a nonintegral equality threshold becomes an inconsistent pair rather
than being rounded to a spurious solution.

## B4-2: exact affine constraint encoding

`rational_threshold_constraints E K lambda` concatenates three lists:

1. `(e, 0)` for every `e` in `E`;
2. `(e, Qceiling (lambda e))` for every `e` in `E`;
3. `(-e, Qceiling (-lambda e))` for every `e` in `K`.

The first block is deliberately independent of the threshold.  It preserves
membership in `Cone Q` when a threshold is negative.  Under `FullPeriodic Q`
and the H-representation hypothesis, `rational_slice_affine_group_iff`
proves the exact `SameSet` between the rational slice and
`AffineGroupSolutions (Difference Q)` for this list.

## B4-3: homogeneous solutions

`homogeneous_group_face_period_iff` proves:

```coq
SameSet
  (HomogeneousGroupSolutions (Difference Q)
    (rational_threshold_constraints E K lambda))
  (FacePeriod Q (ThresholdFace (Cone Q) K)).
```

All constants disappear in the homogeneous system.  The positive `E`
constraints establish cone membership.  For `K`, the positive and negative
normal constraints force inner product zero.  `FullPeriodic` then converts
`Difference Q` intersected with `Cone Q` back to `Q`.  The auxiliary theorem
`threshold_face_is_face` shows that the threshold face is a genuine face;
periodicity and finite generation corollaries are also exposed.

## B4-4: finite basis

The main theorem is:

```coq
corollary_6_7_finitary : forall d
    (period : ZSet d) (normals tight : list (ZVec d))
    (threshold : ZVec d -> Q),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    (forall point : QVec d,
      Cone period point <->
      forall normal, List.In normal normals ->
        0 <= qinner (zvec_to_qvec normal) point) ->
    (forall normal, List.In normal tight -> List.In normal normals) ->
    FinitaryQCylindric
      (FacePeriod period (ThresholdFace (Cone period) tight))
      (RationalThresholdSlice period normals tight threshold)
```

`difference_group_finitely_generated` supplies the group hypothesis for B1's
`affine_group_inequalities_finitary`.  `finitary_qcylindric_congr` transports
the B1 result across the two `SameSet` equivalences without function
extensionality.

## Regression coverage

Focused regressions include dimension zero, empty and duplicate normal lists,
positive, negative, half-integral, and nonintegral equality thresholds.  The
requested examples are formalized as follows:

- for `Q = 2N`, `K = []`, and threshold 1, the slice is exactly `2 + 2N`;
- for the nonnegative quadrant with the first normal tight at 2 and the
  second threshold `1/2`, the slice is exactly `(2,y)` with `y >= 1`;
- for `Q = 2N` (indeed, for any period set), a tight threshold `3/2` has no
  integer point.

A separate negative-threshold regression proves that the threshold-only
constraint accepts `-1`, while the complete three-block encoding rejects it
through the zero cone constraint.

## Axiom audit

The ceiling lemmas, exact slice encoding, and homogeneous-set equivalence are
closed under the global context.  `corollary_6_7_finitary` inherits only
`Classical_Prop.classic` from B1's finite-basis theorem.  There is no new
`Axiom`, `Admitted`, `Abort`, `ClassicalEpsilon`, UIP/K, `Eq_rect_eq`,
functional extensionality, or external oracle.

## Independent review

An independent read-only review returned `READY` with no Critical,
Important, or Minor findings.  It checked the signs and directions of both
ceiling equivalences, all three constraint blocks, the two uses of
`FullPeriodic`, the `ThresholdFace` face proof, the homogeneous zero
conditions, both `SameSet` transports into B1, examples A/B/C, the axiom
report, and the B4 scope boundary.

## Deliberately remaining for C4-3C

Lemma 6.10 must combine B3's common-list zero-pattern witness with this B4
finite-basis theorem for the appropriate face slice, then connect the result
to the face-stripping decomposition.  No part of that construction is
included here.
