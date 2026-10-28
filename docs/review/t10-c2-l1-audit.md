# T10-C2-L1 audit: rational closure

Date: 2026-10-20

Baseline: `384002eb9990d2410012c9d941076a77435c5de8`

Scope: T10-C2-L1 only.  This change proves definability, conic closure, and
topological closedness of the existing rational closure.  It does not prove
the C2-L2 closed-linearization theorems.

## Audited interfaces

The existing closure is the coordinatewise rational sup-neighborhood
closure:

```coq
QClosure C x :=
  forall delta : Q, 0 < delta ->
    exists y : QVec d,
      C y /\
      forall i : Fin.t d, Qabs (x i - y i) < delta.
```

`TopologicallyClosed C` is `forall x, QClosure C x -> C x`.
`QDefinable C` supplies a `QFormula` closed at the number of free coordinates
and an equivalence with its semantics under `qvec_environment`.  `QFormula`
contains affine rational terms, equality, strict and weak order, Boolean
connectives, and existential and universal quantification.  It contains no
variable multiplication.  `IsCone` supplies zero, addition, and nonnegative
rational scaling.  `RationalCone` additionally records `QVecEq` extensionality.

## Definability bridge

For a defining formula `body` with `d` free variables,
`qclosure_formula d body` represents

```text
forall delta,
  delta <= 0 \/
  exists y_0 ... y_(d-1),
    body(y) /\ forall i, x_i - delta < y_i < x_i + delta.
```

Inside the innermost formula, indices `0 .. d-1` are the approximation
coordinates, index `d` is `delta`, and indices `d+1 .. 2d` are the original
free coordinates.  `qclosure_formula_correct` proves the equivalence for an
arbitrary free-variable environment induced by `QVec d`; it does not replace
the universal-positive-radius condition by a closed-form decision.

The complete public theorem is:

```coq
qclosure_qdefinable :
  forall (d : nat) (C : QSet d),
    QDefinable C -> QDefinable (QClosure C)
```

## Metric and cone lemmas

The implementation proves `QVecEq` extensionality, extensivity, monotonicity,
coordinate-neighborhood/formula equivalence, addition and nonnegative-scaling
preservation, and closure idempotence.  Addition and idempotence use radius
`delta/2`; positive scaling uses `delta/coefficient`, with the zero scalar
handled separately.

The remaining complete public types are:

```coq
qclosure_is_cone :
  forall (d : nat) (C : QSet d),
    IsCone C -> IsCone (QClosure C)

qclosure_topologically_closed :
  forall (d : nat) (C : QSet d),
    TopologicallyClosed (QClosure C)
```

## Regression coverage

The audit module checks dimension zero, the empty and full sets, exact closure
of a singleton, definability of the closure of the open positive ray, the new
zero boundary point of that ray, a boundary point of the open positive
quadrant, a nonclosed cone with linearly missing boundary points, and a pair of
numerically equal but non-normalized rational representations.  In particular,
the open-ray and open-quadrant examples show that `QClosure` is not treated as
the identity operation.

## RED/GREEN and trust boundary

RED: the audit module first requested the three public names and failed at
`qclosure_qdefinable`, which did not exist.

GREEN provides `make audit-t10-c2-l1`.  The target builds the implementation
and examples, prints the complete audited definitions and public types with
implicit arguments, runs `Print Assumptions`, executes `coqchk -silent`, and
rejects `Admitted`, declared `Axiom`, `Abort`, ClassicalEpsilon, UIP/K,
`Eq_rect_eq`, and functional extensionality.  For the final fresh run, the
same underlying commands were invoked directly so that pre-existing
uncommitted audit logs were not overwritten.

All three public theorems are closed under the global context.  In particular,
this proof introduces no `Classical_Prop.classic` dependency and no choice
principle.

The L1 implementation also avoids direct use of the standard-library
`Fin.to_nat_of_nat` proof and of the pre-existing
`qvec_bind_environment_agree` adapter.  Their required value-level facts are
proved locally by structural induction as
`fin_of_nat_lt_value` and `qvec_bind_environment_prefix_agree`.  A direct
source scan rejects UIP/K, `Eq_rect_eq`, functional extensionality, and
constructive indefinite description identifiers in both L1 source files.
Thus the trust claim is both that the kernel reports no axiom dependency and
that L1 does not invoke a derived UIP/K interface directly.

## Verification record

- The RED audit failed at the absent name `qclosure_qdefinable` before the
  implementation was added.
- The focused build of `RationalClosure.vo` and
  `RationalClosureExamples.vo` succeeds.
- The audit module prints all three complete public types and reports
  `Closed under the global context` for every `Print Assumptions` query.
- `coqchk -silent` accepts both new modules.
- The repository-wide Coq build and the focused source scans succeed.
- Independent review found no critical or important issue.  Its one trust
  precision observation prompted the structural-induction change above; the
  non-normalized-rational regression was also strengthened to use a singleton
  rather than the full set.
