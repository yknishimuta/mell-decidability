# T10-C4-3B-0 audit: WQO finite bases for cylindric sets

The baseline is `b8ebb3c614f53ea0d523c8e34dae3583bf0f27b2`.
This checkpoint proves only the finite-basis inheritance used after the
C4-3A extraction step.  It does not implement supporting inequalities,
Lemmas 6.5--6.7 or 6.10, the Face-Stripping Theorem, or C4-3B-1.

## Existing interfaces

The proof reuses the exact existing types:

```coq
PeriodicLe P x y := P (zvec_sub y x)

restricted_af_finite_cover_classic :
  forall (X : Type) (P : X -> Prop) (R : X -> X -> Prop),
    KruskalAfProp.af.af.afs P R ->
    exists basis : list {x : X | P x},
      forall x : {x : X | P x},
        exists b : {x : X | P x},
          List.In b basis /\ R (proj1_sig b) (proj1_sig x)

periodic_order_wqo_iff_finitely_generated :
  forall d (P : ZSet d),
    Periodic P ->
    (KruskalAfProp.af.af.afs P (PeriodicLe P) <->
       FinitelyGeneratedPeriodic P)
```

In particular, WQO is obtained only from both `Periodic period` and
`FinitelyGeneratedPeriodic period`; it is not assumed for arbitrary periodic
sets.

## Slice finite cover

For a finite ambient base `b`, `CylindricSlice period A b q` is

```coq
period q /\ A (b + q).
```

`slice_subset_period` records the ambient inclusion.
`slice_upward_closed` shows closure under `PeriodicLe period`: if
`q' - q` is in the period, cylindricity transports `A (b+q)` to
`A (b+q')`.

`slice_finite_cover` first obtains `afs period (PeriodicLe period)` from the
T10-B equivalence.  `afs_mono` restricts that WQO to the slice predicate, and
`restricted_af_finite_cover_classic` returns a finite list of sigma values
`{q | CylindricSlice ... q}`.  Consequently every selected basis element is
proved to belong to the slice, not merely to the ambient vector space.

## Finite translated bases

For each slice basis element `m`, `finite_base_translation` selects the point
`b+m`, which belongs to `A`.  If `m <= q` in `PeriodicLe`, the remainder is
`q-m`, belongs to `period`, and

```text
b + q = (b + m) + (q - m).
```

`finite_base_union` performs ordinary list induction over the finite base
list of the containing finitary cylinder.  It concatenates the translated
slice bases.  No choice function over an infinite index set and no
executable membership oracle is introduced.

The resulting public theorem is exactly:

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

The proof is propositional.  It establishes existence of a finite basis; it
does not claim to compute one.

## Extraction handoff

`finitary_qcylindric_implies_cylindric` turns a finite base presentation into
ordinary cylindricity using periodic addition.  Therefore
`extract_remainder_finitary` obtains cylindricity of `remaining`, invokes the
C4-3A `extract_remainder_cylindric`, observes that the remainder is a subset
of `remaining`, and applies `finitary_qcylindric_sub`.

The existing `excluded_subset_extract_remainder` remains the separate
inclusion used by the later induction.  No finite-basis assumption on
`excluded` is introduced.

## Boundary regressions

`FaceStrippingFinitaryExamples.v` covers dimension zero, the zero period,
the generated periods N and N^2, the signed one-dimensional period Z, a
signed low-rank period in dimension two, empty `A`, `A=B`, empty `B`, and an
explicit two-translate finitary cylinder.  Extraction regressions cover
empty `excluded`, `excluded=remaining`, the maximal face, and the concrete
proper zero face from C4-3A.  A separate example reuses
`excluded_subset_extract_remainder`.

## Trust boundary

`slice_finite_cover`, `finitary_qcylindric_sub`, and
`extract_remainder_finitary` inherit `Classical_Prop.classic` from the
existing finite-cover theorem.  No dependency on `ClassicalEpsilon`, UIP/K,
`Eq_rect_eq`, functional extensionality, an admitted statement, a new axiom,
or an external oracle is introduced.

Focused and full builds, `Print Assumptions`, `coqchk -silent`, and the final
independent review are recorded in the completion report after their final
runs.

## Verification record

The focused `audit-t10-c4-3b-0` target completed successfully.  It compiled
the implementation and examples, printed the complete public types, checked
the three principal assumption sets, ran `coqchk -silent`, and rejected the
forbidden proof shortcuts listed above.  The related `PeriodicOrder` and
C4-3A modules also passed focused build and kernel checks, and the complete
`Makefile.coq` regression completed successfully.

An independent review reported Critical 0, Important 0, Minor 0.  It checked
the WQO restriction, proof-carrying slice basis, translation equalities,
finite list union, exact public contracts, extraction handoff, assumption
boundary, regression coverage, and target-only Git scope.

## C4-3B-1 boundary

C4-3B-1 still must formalize the supporting inequalities and their use in
the face-stripping development.  This checkpoint supplies only the WQO-based
finite-basis inheritance and its extraction-remainder corollary; it proves
none of Lemmas 6.5--6.7 or 6.10 and no instance of Theorem 6.1.
