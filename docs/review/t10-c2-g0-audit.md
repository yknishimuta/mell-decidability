# T10-C2-G0 audit — explicit H-cone lattice Gordan

## Contract and baseline

- Baseline: 9281d192ddd3f030a5b14f77297e49cf22d3fa01.
- Contract source: /Users/nishimuta/Downloads/2026-10-20-t10-c2-g0-gordan-hcone-plan.md.
- The source and tracked copy have SHA-256
  2dd3d434cf48c73541e7f6b603e269cff2e4dc97b7222c54ade2f00ae761f954;
  cmp exits 0.

FinitelyGeneratedGroup and RationalPolyhedralCone are not Coq declarations
at this baseline. This task therefore proves the approved lower theorem with
an explicit group-generator list and explicit H-matrix. It does not define
those future G1 interfaces or claim an H/V conversion.

## Audited input interfaces

    @FinitelyGeneratedPeriodic
      : forall d : nat, ZSet d -> Prop

    @HConicalConstraints
      : forall rows d : nat, QMatrix rows d -> QVec d -> Prop

    homogeneous_solutions_finitely_generated
      : forall (rows d : nat) (matrix : ZMatrix rows d),
          exists generators : list (NVec d),
            (forall generator, List.In generator generators ->
              HomogeneousSolution matrix generator) /\
            (forall value, HomogeneousSolution matrix value <->
              GeneratedBy generators value)

FinitelyGeneratedPeriodic expands to a fixed finite generator list whose
members satisfy the predicate, with predicate membership equivalent to
zvec_generated.

## Completed theorem

With implicit arguments printed:

    lattice_gordan_hmatrix
      : forall (d rows : nat) (matrix : QMatrix rows d)
          (generators : list (ZVec d)),
          @FinitelyGeneratedPeriodic d
            (fun value : ZVec d =>
              @ZGroupGenerated d generators value /\
              @HConicalConstraints rows d matrix
                (@zvec_to_qvec d value))

ZGroupGenerated uses a vector of integer coefficients, not the natural
coefficients used by zvec_generated.

## Mathematical bridge

1. pulled_qmatrix is the H-matrix on the integer coefficient space.
   pulled_constraints_iff identifies its semantics with the original H
   constraints on the corresponding group combination.
2. qmatrix_clear_denominators supplies a positive common denominator and an
   integer matrix MF.
3. Existing homogenized_matrix forms [MF,-MF,-I]. Positive and negative
   natural coefficient vectors encode signed integer coefficients; the last
   component is nonnegative slack.
4. homogeneous_solutions_finitely_generated fixes a finite generator list
   before any target point is considered.
5. solution_coefficients_add/scale and project_group_solution_add/scale prove
   that projection preserves the additive monoid operations.
6. project_group_solution_constraints proves generator soundness, and
   weighted_sum_project_group_generated proves completeness under projection.
7. group_hcone_intersection_periodic supplies zero and additive closure.

The audit module prints the complete types of pulled_constraints_iff,
project_group_solution_constraints, weighted_sum_project_group_generated,
and lattice_gordan_hmatrix.

## Regression coverage

- dimension zero, zero rows, and an empty group-generator list;
- Z intersect Q>=0, 2Z intersect Q>=0, and Z intersect Q<=0;
- the rank-one diagonal subgroup Z(1,1) in the nonnegative orthant;
- an H-cone with lineality;
- redundant and zero H-rows, redundant and zero group generators;
- a non-normalized representation of rational one;
- integer group coefficients generate -1 from generator 1, while natural
  monoid coefficients do not.

## Trust boundary

Print Assumptions reports:

    pulled_constraints_iff:
      Closed under the global context

    project_group_solution_constraints:
      Closed under the global context

    weighted_sum_project_group_generated:
      Closed under the global context

    lattice_gordan_hmatrix:
      Classical_Prop.classic

The final dependency is inherited from A0-L's finite-basis construction.
There is no dependency on constructive indefinite description, UIP/K,
Eq_rect_eq, functional extensionality, a new axiom, or an oracle.

## Remaining G1 and closed-linearization obligations

C2-G1 must introduce or locate the intended declarations for
FinitelyGeneratedGroup and RationalPolyhedralCone. If the cone contract is
V-represented, it additionally needs a proved V-to-H bridge or a separate
V-representation Gordan argument. Closed linearization still requires the
actual P-P group representation and the definability, conicity, and
closedness properties of the rational closure. None is claimed by C2-G0.

## Verification

- RED: before `LatticeGordanH.v` existed, compiling
  `theories/Audit/LatticeGordanHExamples.v` failed with the expected
  `Cannot find ... Mell.Geometry.LatticeGordanH` error.
- GREEN: `opam exec --switch . -- make audit-t10-c2-g0` exited 0.  This
  rebuilt the focused modules, replayed the complete types and assumptions,
  rejected the forbidden dependencies, and ran `coqchk -silent` on
  `Mell.Geometry.LatticeGordanH` and `Mell.Audit.LatticeGordanHExamples`.
- Focused regression: `opam exec --switch . -- make -f Makefile.coq -j2`
  on `LinearEquations.vo`, `PeriodicOrder.vo`, all four C1 geometry modules,
  and both C2-G0 modules exited 0.
- Full regression: `opam exec --switch . -- make -f Makefile.coq -j2`
  exited 0 (`Nothing to be done for real-all`).
- Independent review replayed both source files with `coqtop`, checked both
  modules with `coqchk -silent`, and found no Critical or Important issue.
  Its only Minor finding was this previously missing verification record;
  the reviewer judged the mathematical construction, public type, examples,
  and trust boundary ready after this documentation fix.
