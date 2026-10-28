# T10-C2-L2 audit: closed linearization

Date: 2026-10-20

Baseline: `e99195b08092b4da89c0882aa224084b1d1623b7`

Scope: T10-C2-L2 only.  This unit proves general fullness and finite
generation of the closed linearization.  It does not implement C2-L3, C3,
center, push-in, or face results.

## Public interface

The planning audit fixed `NonnegativeSet` but no Gallina declaration existed
before L2.  L2 introduces exactly the audited definition:

```coq
NonnegativeSet set :=
  forall value, set value -> forall index,
    (0 <= Vector.nth value index)%Z.
```

The completed public theorems have the following types:

```coq
closed_linearization_full :
  forall (d : nat) (set : ZSet d),
    Periodic set -> FullPeriodic (ClosedLinearization set)

closed_linearization_finitely_generated :
  forall (d : nat) (set : ZSet d),
    Periodic set ->
    NonnegativeSet set ->
    AsymptoticallyDefinable set ->
    FinitelyGeneratedPeriodic (ClosedLinearization set)
```

No existing L0, L0-R, L1, C1, or G1 definition or theorem type is changed.

## General fullness

`closed_linearization_periodic` proves closure under zero and addition.
The integer component uses `difference_zero` and `difference_add`.  The
rational component uses `qclosure_extensive`, `qclosure_add`, and the
`QVecEq` bridge `zvec_to_qvec_add`.

`qclosure_is_rational_cone` combines L1's `qclosure_is_cone` with
`qclosure_qvec_extensional`.  The witnesses for general `FullPeriodic` are
therefore exactly:

```text
group = Difference set
cone  = QClosure (Cone set)
```

The group is supplied by `difference_is_integer_additive_group`; the cone is
an arbitrary `RationalCone`.  No finite-generation or polyhedral premise is
used for `closed_linearization_full`.

## Finite generation

For an asymptotically definable set, L1 supplies:

- `qclosure_qdefinable` for `QClosure (Cone set)`;
- `qclosure_is_cone`, using `cone_is_cone`;
- `qclosure_topologically_closed`.

The C1/G1-I adapter `rational_closed_cone_is_polyhedral` converts these facts
to a finite V-representation.  L0 supplies
`difference_group_finitely_generated`, and G1 supplies `lattice_gordan` for
their intersection.  Unfolding `ClosedLinearization` makes that intersection
definitionally the requested set.

The signed construction proves a slightly stronger internal fact, so the
`NonnegativeSet` premise is not needed in the proof term.  It remains in the
public type exactly as required by the source-domain contract; it is neither
removed nor used to redefine the integer ambient space.

## RED/GREEN and regression

RED: the audit module imported `ClosedLinearizationL2` and failed because the
module did not exist.

GREEN checks both complete public types, the two main connection lemmas, and
dimension-zero instances of both fullness and finite generation.  The
dimension-zero finite-generation example supplies explicit periodicity,
nonnegativity, and rational definability evidence.

Final verification uses the focused and complete Coq builds, direct
`coqtop` output for `Print Assumptions`, `coqchk -silent`, forbidden-source
scans, and independent review.  Direct commands are used for the final run
so that pre-existing uncommitted audit logs are not overwritten.

The focused build and the complete `Makefile.coq` build both completed with
exit status 0.  Direct `coqchk -silent` of the implementation and audit
modules also completed with exit status 0 and no output.  Source and
dependency scans found none of the prohibited proof mechanisms.

## Trust boundary

`closed_linearization_full` is closed under the global context.
`closed_linearization_finitely_generated` inherits only
`Classical_Prop.classic`; its existing sources are C1's nonempty-cell case
split and L0's T10-B finite-generation theorem.  It does not depend on
ClassicalEpsilon, UIP/K, `Eq_rect_eq`, functional extensionality, a new
axiom, or an oracle.

## Independent review

The fresh-context reviewer returned **Ready**, with Critical 0, Important 0,
and Minor 0.  It independently checked both public types, the general
non-polyhedral fullness witnesses, the zero/addition and `QVecEq` bridges,
the L0/L1/C1/G1 finite-generation chain, assumptions, examples, and scope.
Its independent elaboration, `Print All Dependencies`, and
`coqchk -silent` runs all succeeded.
