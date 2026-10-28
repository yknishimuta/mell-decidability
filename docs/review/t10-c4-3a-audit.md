# T10-C4-3A audit: face extraction and cylindricity

The baseline is `bdde38fba58700a5f324d1c2e73fb4681f6c6e8e`.
This checkpoint implements only the extraction operation and the cylindricity
claims used in Bizière--Leroux--Sutre (2026), Section 6, Lemma 6.8.  It does
not implement C4-3B, Lemma 6.10, or the Face-Stripping Theorem.

## Definitions

`QCylindric period set` says that `set` is closed under adding any member of
`period`.  `FinitaryQCylindric period set` is deliberately separate: it says
that `set` is, up to `SameSet`, the Minkowski sum of `period` with a finite
list of bases.  No executable equality test on sets is assumed.

`FacePeriod period face` is the exact integer intersection

```
period value /\ face (zvec_to_qvec value).
```

For the paper's `extract(X,Y,F)`, `ExtractFace period face excluded remaining`
requires every translate by `FacePeriod period face` to lie in `remaining`
and outside `excluded`.  In particular, the extraction is cylindric only for
the face-period, not in general for the whole period.

## Finite generation along a face

`face_periodic` uses the additive closure of the original period and the cone
structure of a face.  `face_periodic_finitely_generated` retains the original
nonnegative integer representation: it filters the given integer generator
list by the finite supporting-normal family of the face.

The key lemma `face_linear_combination_filter` works positionally, so repeated
generators remain distinct occurrences.  Every supporting-normal value is
nonnegative on each generator and on the generated tail.  If their total is
zero, an off-face generator has coefficient zero.  Removing exactly those
zero-coefficient occurrences therefore preserves the integer linear
combination.  The proof does not replace the result by all integer points of
the rational face cone.

## Extraction and Lemma 6.8

`extract_face_subset_difference` applies the extraction condition at the zero
face-period increment, proving inclusion in `remaining \ excluded`.
`extract_face_cylindric` composes two face-period increments and is therefore
constructive.

For `extract_remainder_cylindric`, failure of extraction at a base produces a
face-period increment witnessing failure of the defining implication.  The
remaining cylinder rules out failure of the positive conjunct, hence the
translate is in `excluded`.  Cylindricity of `excluded` then transports that
witness across an arbitrary period increment; associativity and commutativity
of vector addition give failure of extraction at the translated base.  The
separate theorem `excluded_subset_extract_remainder` supplies the inclusion
needed by the later induction.

`extract_face_not_period_cylindric_if_proper` records the important boundary:
when the period contains an element outside a proper face, extraction with
empty excluded set and face-period as remaining is not cylindric for the full
period.  Thus the implementation does not strengthen the paper's claim.

## Boundary regressions

`FaceStrippingExtractExamples.v` covers dimension zero, the zero period,
one- and two-dimensional nonnegative generated periods, a nonpointed
one-dimensional period with lineality, the maximal face, empty `excluded`,
and `excluded = remaining`.  It also instantiates the remainder theorem and
the generic proper-face obstruction above.  The maximal-face theorem
`face_period_self` establishes `FacePeriod period (Cone period) = period`
extensionally for every periodic set.

## Finite-basis handoff to C4-3B

The existing theorem

```coq
restricted_af_finite_cover_classic :
  forall (X : Type) (P : X -> Prop) (R : X -> X -> Prop),
    KruskalAfProp.af.afs P R ->
    exists basis : list {x : X | P x},
      forall x : {x : X | P x},
        exists b : {x : X | P x},
          List.In b basis /\ R (proj1_sig b) (proj1_sig x)
```

provides the required finite cover once an appropriate WQO is available.
`periodic_order_wqo_iff_finitely_generated` supplies that WQO from a
`FinitelyGeneratedPeriodic period` hypothesis (and `Periodic period`).  It
does not justify the unrestricted inheritance statement for an arbitrary
period.

The exact proposed C4-3B interface is therefore:

```coq
finitary_qcylindric_sub :
  forall d (period A B : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    QCylindric period A ->
    FinitaryQCylindric period B ->
    (forall x, A x -> B x) ->
    FinitaryQCylindric period A.
```

For each finite base `b` of `B`, the fiber
`fun q => period q /\ A (b + q)` is upward closed for `PeriodicLe period`.
Applying the restricted finite-cover theorem to each fiber and concatenating
the translated finite bases is the planned proof.  This nontrivial finite
basis construction is intentionally deferred to C4-3B, as permitted by the
contract.

## Trust boundary

`face_periodic`, extraction inclusion, and extraction cylindricity are closed
under the global context.  `face_periodic_finitely_generated` inherits only
`Classical_Prop.classic` to select a supporting normal witnessing failure of
finite orthogonality.  `extract_remainder_cylindric` inherits only
`Classical_Prop.classic` to extract a counterexample from a failed universal
condition.  There is no dependency on `ClassicalEpsilon`, UIP/K,
`Eq_rect_eq`, functional extensionality, an admitted statement, a new axiom,
or an external oracle.

Focused and full builds, `Print Assumptions`, `coqchk -silent`, and the final
independent review are recorded in the completion report after their final
runs.

The independent delta review initially found that the generic proper-face
obstruction had not been instantiated by a concrete regression.  The final
version adds a nonzero one-dimensional period, its exposed zero face, finite
generation of that face-period, and an explicit proof that the extraction is
not cylindric for the full period.  Re-review approved the corrected change
with no remaining critical, important, or minor findings.
