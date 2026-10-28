# T10-C2-G1-I audit — public interfaces and adapters

## Baseline and scope

- Baseline: `413803be4cd7e8019468cfaed594daf0e40ea93e`.
- Scope: interface definitions, C1 adapters, and the future
  `lattice_gordan` RED contract only.
- G1-Hilbert, G1-Pullback, G1-Main, and closed linearization are not
  implemented here.

The completed C1 and G0 sources and their public declarations are unchanged.

## Public definitions

With implicit arguments shown, the new interfaces are:

    @FinitelyGeneratedGroup
      : forall d : nat, ZSet d -> Prop

    @RationalPolyhedralCone
      : forall d : nat, QSet d -> Prop

They expand to:

    FinitelyGeneratedGroup G :=
      exists generators : list (ZVec d),
        SameSet G (ZGroupGenerated generators)

    RationalPolyhedralCone C :=
      exists generators : list (QVec d),
        SameSet C (qcone_generated generators)

Thus group coefficients are integers, while the cone has the finite V
representation produced by C1.  The cone interface does not silently assert
an H representation.

## Representation and extensionality adapters

The audit module prints the complete types of:

- `finitely_generated_group_iff`;
- `zgroup_generated_is_finitely_generated_group`;
- `finitely_generated_group_ext`;
- `rational_polyhedral_cone_iff`;
- `qcone_generated_is_rational_polyhedral_cone`;
- `rational_polyhedral_cone_ext`;
- `rational_polyhedral_cone_qvec_ext`.

The first two groups of lemmas expose and transport the `SameSet` witnesses.
The last Q-vector lemma proves membership invariance under coordinatewise
`Qeq`; it is derived from `qcone_generated_qvec_ext` rather than assumed for
an arbitrary `QSet`.

## C1 adapters

    rational_hcone_is_polyhedral
      : forall (rows d : nat) (matrix : QMatrix rows d),
          @RationalPolyhedralCone d
            (@HConicalConstraints rows d matrix)

uses `rational_hcone_finitely_generated`.

    rational_closed_cone_is_polyhedral
      : forall (d : nat) (cone : QSet d),
          @QDefinable d cone ->
          @IsCone d cone ->
          @TopologicallyClosed d cone ->
          @RationalPolyhedralCone d cone

uses the final C1 theorem `rational_closed_cone_finitely_generated`.

## Future public contract and RED boundary

The exact future statement is stored without a proof as the proposition:

    lattice_gordan_contract =
      forall (d : nat) (group : ZSet d) (cone : QSet d),
        @FinitelyGeneratedGroup d group ->
        @RationalPolyhedralCone d cone ->
        @FinitelyGeneratedPeriodic d
          (fun value : ZVec d =>
            group value /\ cone (@zvec_to_qvec d value))

The audit source contains `Fail Check lattice_gordan`.  This records that the
future theorem is deliberately absent and prevents G1-I from being reported
as G1-Main.

The remaining proof obligations are:

1. **G1-Hilbert:** prove finite generation for an explicit integer-generated
   group intersected with a finite V-generated rational cone.  The existing
   H-matrix G0 theorem cannot be applied until an H representation has been
   proved; V and H presentations are not identified definitionally.
2. **G1-Pullback:** transport the explicit-list theorem through both
   `SameSet` witnesses, preserving the supplied subgroup and cone rather than
   replacing either with an ambient space.
3. **G1-Main:** instantiate the witnesses once and prove
   `lattice_gordan_contract`, finally exporting the theorem
   `lattice_gordan` with exactly that type.

## Trust boundary

The representation, canonical-constructor, extensionality, and Qeq lemmas
are closed under the global context.  The explicit H-cone adapter inherits
only `Classical_Prop.classic` from C1-HL/A0-L, and the closed definable cone
adapter inherits only the same axiom from C1 assembly.  No new axiom, choice
oracle, UIP/K, `Eq_rect_eq`, or functional extensionality is introduced.

## Verification

- RED: compiling `LatticeGordanInterfaceExamples.v` before the interface
  existed failed with the expected `Cannot find ... LatticeGordanInterface`.
- A second focused RED required the two canonical representation adapters and
  failed because their names were absent; after their implementation the
  same client passed.
- GREEN: `opam exec --switch . -- make audit-t10-c2-g1-i` exited 0.  It
  rebuilt both modules, replayed the complete types and contract, checked all
  assumptions, rejected forbidden dependencies and declarations, and ran
  `coqchk -silent` on both modules.
- Focused C1/G0/G1-I regression through `Makefile.coq` exited 0.
- Full `opam exec --switch . -- make -f Makefile.coq -j2` exited 0
  (`Nothing to be done for real-all`).
- Independent read-only review found no Critical, Important, or Minor issue
  and returned Ready.  It independently replayed both source files, confirmed
  seven structural lemmas closed and both C1 adapters dependent only on
  `Classical_Prop.classic`, and ran `coqchk -silent` on both modules with exit
  code 0.  It did not independently rerun the historical RED or full-project
  regression; those are covered by the implementer runs above.
