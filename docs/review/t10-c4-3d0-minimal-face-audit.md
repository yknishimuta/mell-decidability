# T10-C4-3D0 minimal face and Lemma 6.9 audit

## Scope and result

This change formalizes only C4-3D0.  It introduces cone lineality, proves
that it is the least face of a rational polyhedral cone, proves inverse
closure for period vectors lying on that face, and proves Lemma 6.9.  It
does not contain C4-3D1, Lemma 6.11, or Theorem 6.1.

The implementation is in
`theories/Geometry/FaceStrippingMinimalFace.v`; focused type, assumption,
and boundary regressions are in
`theories/Audit/FaceStrippingMinimalFaceExamples.v`.

## Public definitions and the least face

```coq
Definition ConeLineality {d} (cone : QSet d) : QSet d :=
  fun value =>
    cone value /\
    cone (qvec_scale (-1) value).

Definition MinimalConeFace {d} (cone face : QSet d) : Prop :=
  FaceOf cone face /\
  forall other,
    FaceOf cone other ->
    FaceSubset face other.

polyhedral_lineality_minimal_face :
  forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    MinimalConeFace cone (ConeLineality cone).
```

`polyhedral_cone_integer_hrep` supplies a finite integer normal list.
`cone_lineality_hrep` proves that a point lies in lineality exactly when it
lies in the cone and every H-representation normal has zero inner product.
This is a `FaceOf` witness.  For any other face, its supporting normals are
nonnegative on both `x` and `-x`; `qinner_scale_right` and antisymmetry of
`Qle` force each inner product to be zero.  Hence lineality is contained in
every face.  No pointedness or full-dimensionality assumption is used.

## Inverse closure on the minimal face

```coq
lineality_face_period_inverse :
  forall d (period : ZSet d) (value : ZVec d),
    Periodic period ->
    FullPeriodic period ->
    FacePeriod period (ConeLineality (Cone period)) value ->
    period (zvec_opp value).

lineality_face_period_inverse_closed :
  forall d (period : ZSet d) (value : ZVec d),
    Periodic period ->
    FullPeriodic period ->
    FacePeriod period (ConeLineality (Cone period)) value ->
    FacePeriod period (ConeLineality (Cone period)) (zvec_opp value).
```

For `q` in the face period, membership in `period` yields membership in
`Difference period`; `difference_opp` supplies the difference condition for
`-q`.  Lineality supplies the cone condition.  The existing
`full_periodic_member_iff_difference_cone` then returns `-q` to `period`.
The stronger lemma also proves that `-q` remains in the same face period.
Nothing claims inverse closure for an arbitrary member of `period`.

## Lemma 6.9

```coq
lemma_6_9_minimal_extract :
  forall d (period excluded remaining : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    QCylindric period excluded ->
    QCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    SameSet
      (ExtractFace period
        (ConeLineality (Cone period)) excluded remaining)
      (fun value => remaining value /\ ~ excluded value).
```

The forward inclusion is `extract_face_subset_difference`.  For the reverse
inclusion, cylindricity of `remaining` gives `remaining (y+q)`.  If
`excluded (y+q)`, inverse closure gives `period (-q)`, so cylindricity of
`excluded` gives `excluded ((y+q)+(-q))`, contradicting `~ excluded y`.

The arbitrary-minimal-face transport is also public:

```coq
lemma_6_9_any_minimal_face :
  forall d (period excluded remaining : ZSet d) (face : QSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    QCylindric period excluded ->
    QCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    MinimalConeFace (Cone period) face ->
    SameSet
      (ExtractFace period face excluded remaining)
      (fun value => remaining value /\ ~ excluded value).
```

It proves `SameSet face (ConeLineality (Cone period))` by mutual minimal
inclusion and transports Extract with `extract_face_same_set`; no function
extensionality is used.

## Paper/API argument-order audit

The Coq API remains the established
`ExtractFace period face excluded remaining` order.  Throughout this module,
`excluded = X` and `remaining = Y`.  This agrees with the theorem-level
construction `extract_F(X, Y minus S_<i>)` and intentionally does not follow the
reversed notation occurring in part of the Section 6 prose.

## Focused regressions

The audit covers dimension zero, the zero cone, the full space, the
nonnegative ray (the common cone of `N` and `2N`), the full integer line,
the nonnegative quadrant, and `N × Z`.  It checks respectively that the
lineality is the full zero-dimensional space, `{0}`, the full space, `{0}`,
the full line, `{0}`, and the second coordinate axis.  These distinguish
pointed and nonpointed cones and a cone with a nontrivial lineality space.

In addition to those rational-predicate checks, concrete integer periods for
`N`, `2N`, `Z`, `N²`, and `N × Z` are passed through their actual `Cone` and
`FacePeriod`.  The resulting minimal face periods are respectively `{0}`,
`{0}`, the full integer line, `{0}`, and the second integer coordinate axis.
For `N × Z`, the audit applies `lineality_face_period_inverse_closed` to the
nonzero axis vector `(0,1)`, obtains its inverse `(0,-1)`, and separately
rejects the off-axis period vector `(1,0)`.

The concrete Lemma 6.9 regression constructs `N` as a periodic, finitely
generated, full set and proves that, for `excluded = 2+N` and
`remaining = N`, minimal-face Extract membership is equivalent to the sole
coordinate being `0` or `1`.  The public theorem additionally covers empty
excluded sets, `excluded = remaining`, proper inclusions, zero and
low-rank periods, and all finite dimensions without extra assumptions.

## Assumptions and prohibited constructions

`Print Assumptions` reports `Closed under the global context` for:

- `polyhedral_lineality_minimal_face`;
- `lineality_face_period_inverse`;
- `lineality_face_period_inverse_closed`;
- `lemma_6_9_minimal_extract`; and
- `lemma_6_9_any_minimal_face`.

There is no new axiom, `Admitted`, `Abort`, `ClassicalEpsilon`, countable or
dependent choice, UIP/K, `Eq_rect_eq`, functional extensionality, or external
oracle.  The public theorems do not depend on `Classical_Prop.classic`.

## Verification record

- RED: the focused audit failed because
  `Mell.Geometry.FaceStrippingMinimalFace` did not exist; the second RED
  failed on the absent inverse theorem.
- GREEN: focused source and audit compilation succeeded.
- Full `_CoqProject` build succeeded (`real-all` had no remaining work).
- `coqchk -silent` succeeded for the source and audit modules.
- Public types and assumptions were read directly from Coq.
- The prohibited-token scan and target-scoped `git diff --check` succeeded.
- Independent review disposition and final commit are recorded in the
  completion report.
