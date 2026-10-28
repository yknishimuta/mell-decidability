# T10-C4-3B-1-B1 audit

Baseline: `a6877a86244f6c5e38d7b74d9eaf7c60acd4c98e`.

Scope: Lemma 6.6 finite bases for integer affine inequalities and its
restriction to a finitely generated integer subgroup.  B2--B4 are audited
below but are not implemented here.

## B1-0: reused interfaces

The installed decomposition theorem is:

```coq
linear_solution_decomposition :
  forall rows d (matrix : ZMatrix rows d) (constant : ZVec rows),
    exists basis : list (NVec d),
      (forall base, In base basis ->
        LinearSolution matrix constant base) /\
      (forall value, LinearSolution matrix constant value ->
        exists base homogeneous,
          In base basis /\
          HomogeneousSolution matrix homogeneous /\
          value = nvec_add base homogeneous)
```

The implementation also reuses `homogenized_matrix`,
`homogenized_solution_exact`, `zvec_positive`, `zvec_negative`,
`solution_coefficients`, `solution_coefficients_add`, `F_Z`, `F_Z_add`,
`F_Z_zero`, `ZGroupGenerated`, `FinitelyGeneratedGroup`, and
`FinitaryQCylindric`.

## B1-a: the full integer lattice

For `k = length constraints`, a signed value is represented by nonnegative
vectors `positive` and `negative`, and every inequality gets a nonnegative
slack coordinate.  Thus the constructed equation has dimension
`d + (d + k)` and rows

```text
a * positive - a * negative - slack = constant.
```

`affine_solution_lift` lifts every affine solution using coordinatewise
positive/negative parts and the exact slack `a*z-c`.
`linear_solution_projects_affine` and `homogeneous_solution_projects`
project equation solutions through `solution_coefficients`, i.e. `u-v`.
`solution_coefficients_lift` proves that lifting and projecting returns the
original signed vector.  Finally `affine_solutions_add_homogeneous` proves the
reverse inclusion.

The public result is:

```coq
integer_affine_inequalities_finitary :
  forall (d : nat) (constraints : list (ZVec d * Z)),
    exists bases : list (ZVec d),
      List.Forall (AffineSolutions constraints) bases /\
      SameSet (AffineSolutions constraints)
        (fun value : ZVec d =>
          exists base homogeneous : ZVec d,
            List.In base bases /\
            HomogeneousSolutions constraints homogeneous /\
            value = zvec_add base homogeneous)
```

The homogeneous set is periodic by `homogeneous_solutions_periodic`.

## B1-b: restriction to a finitely generated group

For group generators `g_1,...,g_k`, `pull_integer_normal a generators`
has coordinates `a . g_i`.  The key equality and membership bridges are:

```coq
zinner_pull_integer_normal :
  forall d normal generators coefficients,
    zinner (pull_integer_normal normal generators) coefficients =
    zinner normal (F_Z generators coefficients)

affine_solutions_pull_iff :
  forall d generators constraints coefficients,
    AffineSolutions (pull_integer_constraints generators constraints)
      coefficients <->
    AffineSolutions constraints (F_Z generators coefficients)

homogeneous_solutions_pull_iff :
  forall d generators constraints coefficients,
    HomogeneousSolutions (pull_integer_constraints generators constraints)
      coefficients <->
    HomogeneousSolutions constraints (F_Z generators coefficients)
```

B1-a is applied in the coefficient lattice `Z^k`, and its finite bases are
mapped by `F_Z`.  `F_Z_add` transports the base-plus-period decomposition;
the defining equivalence for `ZGroupGenerated` proves that the image is
exactly the requested group, rather than the full ambient lattice.

The public result is:

```coq
affine_group_inequalities_finitary :
  forall (d : nat) (group : ZSet d)
      (constraints : list (ZVec d * Z)),
    FinitelyGeneratedGroup group ->
    FinitaryQCylindric
      (HomogeneousGroupSolutions group constraints)
      (AffineGroupSolutions group constraints)
```

`homogeneous_group_solutions_periodic` proves periodicity of the intersection
with the group.

## Boundary regression

The focused examples cover dimension zero, empty constraints, negative and
positive thresholds, equality encoded by opposite inequalities, a zero
normal that is always true, an inconsistent zero-normal constraint and its
empty finite basis, signed solutions, homogeneous sets `{0}` and `Z^d`, the
zero group, the full rank-one group, `2Z`, a low-rank subgroup, and duplicate
group generators.  The `2Z` test separately proves that `1` satisfies the
ambient inequality but is not in the restricted solution set, while `2` is.

## Axiom audit

`integer_affine_inequalities_finitary` and
`affine_group_inequalities_finitary` inherit exactly
`Classical_Prop.classic` from the existing
`linear_solution_decomposition`.  The two periodicity lemmas are closed under
the global context.  This change introduces no `Axiom`, `Admitted`, `Abort`,
choice operator, UIP/K, proof irrelevance, or functional extensionality.

## B2--B4 connection audit (not implemented)

- `Difference` is already defined in `ClosedLinearization.v` as differences
  of two points.  `difference_is_integer_additive_group` provides its group
  laws.  A future B4 use of B1-b additionally needs a proof that the relevant
  `Difference Q` is a `FinitelyGeneratedGroup`; the weaker group theorem alone
  is not sufficient.
- For periodic `Q`, `full_periodic_iff_linearization_fixed` gives
  `FullPeriodic Q <-> SameSet Q (Linearization Q)`, where
  `Linearization Q z` is exactly
  `Difference Q z /\ Cone Q (zvec_to_qvec z)`.
- `polyhedral_cone_integer_hrep` supplies a finite list of integer normals for
  the cone part.  B2 must still produce and orient the common supporting
  normal/face data required by the later face-stripping argument.
- For an integer inner product `n`, a rational inequality `lambda <= n` can be
  converted to the integer threshold `ceil(lambda) <= n`.  The project does
  not yet expose the dedicated ceiling bridge needed by B4, so its exact Coq
  lemma and conversion proof remain obligations.
- A rational equality must **not** be converted by ceiling.  B4 must decide
  whether `lambda` is an integer: if so it may encode equality by the two
  integer inequalities `n >= lambda` and `-n >= -lambda`; if not, the integer
  solution set is empty.  The corresponding divisibility/integrality lemma is
  still required.
- `FacePeriod Q F` is already the intersection
  `Q z /\ F (zvec_to_qvec z)`.  `face_periodic` proves periodicity, and
  `face_periodic_finitely_generated` proves finite generation when the
  original period is finitely generated and `F` is a face of `Cone Q`.
  B4 must identify the homogeneous group-inequality set produced from its
  integerized constraints with this `FacePeriod Q F`; that `SameSet` bridge is
  not part of B1.

No theorem for B2, Lemma 6.5 (B3), or Corollary 6.7 (B4) is added here.
