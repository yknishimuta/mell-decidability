# T10-C2-L0-R audit: full periodicity

Date: 2026-10-20

Baseline: `8ffdf3878a6f8ec2a9da6a56c6ea43f1c8628c44`

Scope: correct `FullPeriodic` only, retain the stronger polyhedral property
under a distinct name, and formalize the standard fixed-point
characterization.  C2-L1 and later tasks are not included.

## Primary-source check

The checked primary source is Biziere--Leroux--Sutre, *Solving the
Reachability Problem for Branching Vector Addition Systems via Semilinear
Inductive Invariants*, arXiv:2607.09558v1, Section 2.3, PDF SHA-256
`61ca188e9899b911de5662a3b0672653e9d0a3d58d2ae39d34a870a46b5fa422`.

Section 2.3 defines a periodic set `P` to be full when `P = G intersection C`
for a group `G` in the integer lattice and a rational cone `C`.  Its footnote
explicitly says that, unlike the older cited definition, `C` is not required
to be finitely generated.  Example 2.3 gives
`{(0,0)} union N^2_{>0}` as a full, non-finitely-generated periodic set.

## Old and corrected definitions

The baseline `Print FullPeriodic` required:

```coq
Periodic set /\
exists group cone,
  FinitelyGeneratedGroup group /\
  RationalPolyhedralCone cone /\
  SameSet set (fun z => group z /\ cone (zvec_to_qvec z))
```

This is retained as `PolyhedralFullPeriodic`.  The corrected definition is:

```coq
FullPeriodic set :=
  Periodic set /\
  exists group cone,
    IntegerAdditiveGroup group /\
    RationalCone cone /\
    SameSet set (fun z => group z /\ cone (zvec_to_qvec z)).
```

`RationalCone C` consists of `IsCone C` plus preservation under `QVecEq`.
The latter is not a finite-generation condition: it merely makes Coq's raw
`Q` representation model an actual set of rational vectors, where numerically
equal fractions denote the same point.

## Fixed-point correspondence

The unclosed linearization is fixed as:

```coq
Linearization P z :=
  Difference P z /\ Cone P (zvec_to_qvec z).
```

The paper's characterization is proved with complete type:

```coq
full_periodic_iff_linearization_fixed :
  forall (d : nat) (P : ZSet d),
    Periodic P ->
    (FullPeriodic P <-> SameSet P (Linearization P)).
```

The forward proof embeds `P-P` in the witnessing integer group and `Cone P`
in the witnessing rational cone.  The reverse proof chooses exactly
`Difference P` and `Cone P`; supporting lemmas prove the former is an integer
additive group and the latter is a `QVecEq`-extensional rational cone.

## Regression example

`paper_positive_periodic` formalizes
`{(0,0)} union N^2_{>0}`.  The regression proves:

```coq
paper_positive_full_periodic : FullPeriodic paper_positive_periodic

paper_example_2_3_is_linearization_fixed :
  SameSet paper_positive_periodic (Linearization paper_positive_periodic)
```

The witness group is the whole integer lattice and the witness cone is
`{0} union Q^2_{>0}`.  No finite list of group or cone generators occurs in
the statement or witness.

## Preservation

The definitions and theorem types of `Periodic`, `Difference`, `Cone`,
`ClosedLinearization`, `closed_linearization_spec`, `lattice_gordan`, and
`difference_group_finitely_generated` are unchanged.  In particular,
closed linearization continues to use `QClosure (Cone P)` and not `Cone P`.

## RED/GREEN and trust boundary

RED: after adding checks for `PolyhedralFullPeriodic`, `Linearization`, and
`full_periodic_iff_linearization_fixed`, compilation failed because
`PolyhedralFullPeriodic` did not exist.

GREEN and final verification are performed by
`make audit-t10-c2-l0-r`, which builds both affected modules, prints the two
definitions and public types, checks assumptions, runs `coqchk -silent`, and
rejects `Admitted`, declared `Axiom`, `Abort`, ClassicalEpsilon, UIP/K,
`Eq_rect_eq`, and functional extensionality.

The focused target completed successfully.  Direct regression builds and
silent `coqchk` also succeeded for T10-B's `PeriodicOrder`, C1's
`RationalConeAssembly`, and all Gordan modules from `LatticeGordanH` through
`LatticeGordanMain`.  The complete `Makefile.coq` build reported no pending
or failed targets.

`Print Assumptions` reports the fixed-point theorem, the paper example, and
`closed_linearization_spec` as closed under the global context.
`difference_group_finitely_generated` retains exactly its prior dependency:

```text
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

## Independent review

The independent review approved the corrected tree with Critical 0,
Important 0, and Minor 0.  It independently checked the primary-source
definition and example, confirmed that `QVecEq` extensionality is only
representation coherence and not finite generation, checked both directions
of the fixed-point theorem, and verified that the protected L0 and Gordan
interfaces are unchanged.  Its separate `coqchk -silent` run also completed
with exit status 0 and no output.
