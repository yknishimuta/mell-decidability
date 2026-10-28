# T10-C4-3B-1-HRep-D audit

## Scope and baseline

- Baseline: `c6248ea6469bbcad2df51ed33aadcba88c49a838`.
- Scope: clear denominators in the finite rational normal list produced by
  HRep-C and transport its homogeneous inequalities to integer normals.
- Face-Stripping Lemmas 6.5--6.7 and C4-3C remain outside this change.

## D0: reused interfaces

The implementation reuses `qvector_clear_denominators` from
`RationalHToV.v`. It returns a positive natural denominator and an integer
vector whose embedded coordinates equal that denominator times the input
coordinates. `qmatrix_clear_denominators` has the analogous rectangular
matrix interface, but applying it to a list would require an unnecessary
list-to-`Vector.t` conversion.

```coq
qmatrix_clear_denominators : forall rows d (matrix : QMatrix rows d),
  exists denominator integer_matrix,
    (0 < denominator)%nat /\
    forall row column,
      inject_Z (Vector.nth (Vector.nth integer_matrix row) column) ==
        q_of_nat denominator *
          Vector.nth (Vector.nth matrix row) column

polyhedra_cone_homogeneous_base : forall d
    (generators : list (QVec d)),
  exists normals : list (QVec d),
    forall value : QVec d,
      qcone_generated generators value <->
      forall normal : QVec d,
        List.In normal normals -> Qle 0 (qinner normal value)
```

The remaining bridge uses `qdot_ext`, `qdot_scale_left`, `Qmult_le_l`,
`polyhedra_cone_homogeneous_base`, and the defining generator witness in
`RationalPolyhedralCone`.

## D1--D2: one normal and its inequality

`qnormal_clear_denominators` destructs the positive natural denominator as
`S n` and exposes it as `Pos.of_succ_nat n`. Thus its public multiplier is a
`positive`, not an integer carrying a separate positivity proof. The
underlying algorithm is the existing product of all coordinate denominators;
dimension zero uses the existing denominator `1` branch.

`qnormal_integer_inner` transports the coordinate equations through the
finite dot product and proves that the integer inner product is the same
strictly positive multiple of the rational inner product. The forward order
direction uses nonnegative multiplication; the reverse direction uses
`Qmult_le_l` with the explicit strict-positivity proof.

## D3--D4: finite systems and cones

`qnormal_list_integer_hrep` is structural induction on the rational normal
list. It retains order and duplicates, permits a separate multiplier for
each normal, and maps the empty list to the empty list. No equality of
`QVec` functions is required.

`polyhedral_cone_integer_hrep` opens the generator witness supplied by
`RationalPolyhedralCone`, applies HRep-C, integerizes the resulting finite
normal list, and composes both equivalences with `SameSet`. There are no
pointedness, rank, linear-independence, or full-dimensionality assumptions.

## Regression coverage

The focused regression checks dimension zero, an empty normal list, a zero
normal, duplicate normals, mixed signs and denominators, and the explicit
conversion `(1/2,-3/4) -> (2,-3)` with multiplier `4`. Generic generated-cone
regressions instantiate the final theorem for the empty-generator zero cone,
positive and negative rays, a lineality space, the two-dimensional
nonnegative orthant, and a redundant low-rank generating list.

The empty normal list is tested separately as the H-representation of full
space, so it is not confused with the empty generator list, which generates
only the zero cone.

## Verification and assumptions

The HRep-D focused check and audit compile both new modules, run
`Print Assumptions` for all five public proof results, run `coqchk -silent`,
and scan the target sources for prohibited axioms and proof escapes. Full
repository compilation and target-only `git diff --check` are also required
before commit. All five results are expected to report `Closed under the
global context`.

## Remaining boundary

C4-3B-1 still owns the later Face-Stripping uses of the integer
H-representation. This change does not begin Lemmas 6.5--6.7, C4-3C, or any
normal-minimization/normalization procedure.
