# T10-C1-HL implementation and trust audit

Date: 2026-10-19

Baseline: `ee181e0e59e52feee7eab41c8d48634f724c7e9b`

Scope: C1-0 and C1-HL only. C1-QE1, C1-QE2, C1-Assembly, and T10-C2 were not started.

## Contract and preflight

The implementation follows `docs/superpowers/plans/2026-10-19-t10-c1-implementation-plan-revised.md`. The initial HEAD matched the baseline. The pre-existing modified audit logs and the 18 untracked files under `vendor/presburger/` were recorded and excluded from this change.

The reused A0-L theorem has the following actual type:

```coq
homogeneous_solutions_finitely_generated :
  forall (rows d : nat) (matrix : ZMatrix rows d),
    exists generators : list (NVec d),
      (forall generator,
        List.In generator generators ->
        HomogeneousSolution matrix generator) /\
      (forall value,
        HomogeneousSolution matrix value <->
        GeneratedBy generators value)
```

Its `Print Assumptions` output is exactly:

```text
Axioms:
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

The existing rational interface was retained: `QVec d = Fin.t d -> Q`, `QSet d = QVec d -> Prop`, and `QDefinable` is the T10-A formula-semantics witness. No Coq-Polyhedra dependency was added.

## RED

Before adding the modules, a client importing `Mell.Geometry.RationalHToV` and checking `rational_hcone_finitely_generated` failed with:

```text
Error: Cannot find a physical path bound to logical path
RationalHToV with prefix Mell.Geometry.
```

This was the intended missing-contract failure.

## C1-0 definitions and bridges

`QConeCore.v` fixes the following meanings:

- `QVecEq`: coordinatewise `Qeq`, not Leibniz equality;
- `qcone_generated`: a finite inductive nonnegative rational combination, followed by coordinatewise `Qeq`;
- `IsCone`: zero, addition, and nonnegative rational scaling closure;
- `QClosure`: coordinatewise rational approximation for every positive rational radius;
- `TopologicallyClosed`: membership of every point in that relative rational closure;
- `SameSet`: pointwise logical equivalence.

The module proves `Qeq` compatibility for addition, scaling, generated-cone membership, rational terms and formula semantics. In particular:

```coq
qdefinable_qvec_extensional :
  forall (d : nat) (set : QSet d),
    QDefinable set ->
    forall left right : QVec d,
      QVecEq left right -> set left <-> set right
```

The result is closed under the global context.

## C1-HL proof decomposition

### HL-1: denominator clearing

`qvector_clear_denominators`, `qvec_clear_denominators`, and `qmatrix_clear_denominators` use products of positive denominators. The public matrix result is:

```coq
qmatrix_clear_denominators :
  forall (rows d : nat) (matrix : QMatrix rows d),
    exists (denominator : nat) (integer_matrix : Vector.t (Vector.t Z d) rows),
      0 < denominator /\
      forall (row : Fin.t rows) (column : Fin.t d),
        inject_Z (Vector.nth (Vector.nth integer_matrix row) column) ==
        q_of_nat denominator *
          Vector.nth (Vector.nth matrix row) column
```

`cleared_matrix_constraints_iff` proves that multiplication by the positive common denominator preserves every row inequality in both directions.

### HL-2: homogeneous nonnegative equations

`homogenized_matrix` has dimension `rows × (d + (d + rows))` and implements `B=[M,-M,-I]`. Natural vectors are split as `u`, `v`, and `s`; subtraction occurs only after embedding into `Z`/`Q`. The exact equation is:

```coq
homogenized_solution_exact :
  forall (rows d : nat) (matrix : ZMatrix rows d)
         (positive negative : NVec d) (slack : NVec rows),
    HomogeneousSolution (homogenized_matrix matrix)
      (Vector.append positive (Vector.append negative slack)) <->
    forall row : Fin.t rows,
      (zrow_apply (Vector.nth matrix row) positive -
       zrow_apply (Vector.nth matrix row) negative)%Z =
      Z.of_nat (Vector.nth slack row)
```

The signed projection `project_solution` preserves zero, addition, natural scaling, and weighted sums. `homogeneous_project_nonnegative` maps every homogeneous solution to an H-cone point.

### HL-3: application of A0-L

The proof applies `homogeneous_solutions_finitely_generated` once to the fixed matrix B, then maps the resulting fixed finite generator list through `project_solution`.

For completeness, a rational point is cleared by a positive denominator, the integer vector is decomposed coordinatewise into positive and negative natural parts, and the nonnegative integer slack is built from `Mz`. The A0-L coefficient vector is then divided by the point denominator. For soundness, each projected generator satisfies all integer H-constraints and cone closure handles every nonnegative rational combination.

The final theorem is:

```coq
rational_hcone_finitely_generated :
  forall (rows d : nat) (matrix : QMatrix rows d),
    exists generators : list (QVec d),
      forall value : QVec d,
        HConicalConstraints matrix value <->
        qcone_generated generators value
```

With implicit arguments printed:

```coq
rational_hcone_finitely_generated :
  forall (rows d : nat) (matrix : QMatrix rows d),
    exists generators : list (QVec d),
      forall value : QVec d,
        @HConicalConstraints rows d matrix value <->
        @qcone_generated d generators value
```

## Boundary coverage

`RationalHToVExamples.v` checks:

- `d=0` and `rows=0`;
- a `rows=0,d=1` matrix is checked directly to accept every point;
- a one-row zero constraint is checked directly to accept every point;
- the one-dimensional nonnegative ray;
- a negative coefficient producing the nonpositive ray;
- the zero cone from opposite inequalities;
- a two-dimensional halfspace with lineality;
- duplicate/redundant constraints and the non-normalized rational coefficient `2#2`.

The construction itself admits empty row sets, empty dimensions, zero rows, zero/repeated generators, and negative matrix coefficients. Signed points are decomposed into separate natural positive/negative vectors rather than coerced to `NVec`.

## Verification

Successful focused commands (exit status 0):

```text
make check-t10-c1-hl
make audit-t10-c1-hl
```

The audit target ran:

```text
coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper \
  Mell.Geometry.QConeCore \
  Mell.Geometry.RationalHToV \
  Mell.Audit.RationalHToVExamples
```

with exit status 0. It also found no `Admitted`, top-level `Axiom`, or `Abort`, and rejected any occurrence in the audit output of:

- `ClassicalEpsilon.constructive_indefinite_description`;
- `Eqdep.Eq_rect_eq.eq_rect_eq`;
- `FunctionalExtensionality.functional_extensionality_dep`.

Regression `.vo` targets for T10-A0-L, T10-A0-QF, T10-A0-QE-Adapter, T10-A, and T10-B were rebuilt directly (without overwriting their pre-existing audit logs) and all succeeded.

## Complete assumptions audit

```text
Print Assumptions qdefinable_qvec_extensional.
Closed under the global context

Print Assumptions qmatrix_clear_denominators.
Closed under the global context

Print Assumptions homogenized_solution_exact.
Closed under the global context

Print Assumptions weighted_sum_project_cone.
Closed under the global context

Print Assumptions rational_hcone_finitely_generated.
Axioms:
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

Thus the sole axiom dependency of the final theorem is the contractually permitted `Classical_Prop.classic`, inherited through A0-L. There is no constructive indefinite description, UIP/K, `Eq_rect_eq`, functional extensionality, new axiom, or oracle dependency.

## Independent review

The independent reviewer reported no Critical or Important findings and one
Minor finding: the original boundary examples were theorem specializations and
did not include a zero coefficient row. The reviewer otherwise confirmed the
Qeq contract, denominator clearing, the exact `B=[M,-M,-I]` construction,
signed difference, nonnegative slack, fixed A0-L generator list, both theorem
directions, scope boundary, and trust audit. The reviewer independently ran
`coqchk` and the `coqtop -batch` audit successfully.

The Minor finding was resolved before commit by adding direct semantic tests
that an empty row set and a zero coefficient row accept every point. The final
disposition is **APPROVED; no unresolved findings**.
