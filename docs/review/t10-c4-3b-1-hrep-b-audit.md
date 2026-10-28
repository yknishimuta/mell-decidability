# T10-C4-3B-1-HRep-B audit

## Scope and baseline

- Baseline: `0bf0b5e59df8b740ee792b9d1ffadbc230e5763c`.
- Scope: finite generator lists, MathComp finite sets, Coq-Polyhedra cone
  membership, and the membership equivalence with `qcone_generated`.
- H-representation extraction, homogenization, integer H-representations, and
  HRep-C remain outside this change.

## Installed Coq-Polyhedra interface

The installed library has the following effective API:

```coq
polyhedron.cone : forall (R : realFieldType) (n : nat),
  {fset 'cV[R]_n} -> 'poly[R]_n

polyhedron.in_coneP : forall (R : realFieldType) (n : nat)
    (V : {fset 'cV[R]_n}) (x : 'cV[R]_n),
  reflect
    (exists2 w : {conic 'cV[R]_n ~> R},
       (finsupp w `<=` V)%fset & x = combine w)
    (x \in polyhedron.cone V)
```

Thus the adapter uses rational column vectors and translates between list
coefficients and a finite-support conic function.

## Public API

```coq
rat_fset_of_columns : forall {d},
  list ('cV[rat]_d) -> {fset 'cV[rat]_d}

rat_fset_of_generators : forall {d},
  list (QVec d) -> {fset 'cV[rat]_d}

rat_columns_polyhedra_cone : forall d
    (columns : list ('cV[rat]_d)) (value : 'cV[rat]_d),
  value \in polyhedron.cone (rat_fset_of_columns columns) <->
  exists coefficients : list rat,
    length coefficients = length columns /\
    List.Forall
      (fun coefficient => is_true (((0 : rat) <= coefficient)%R))
      coefficients /\
    value = rat_linear_combination columns coefficients

qcone_generated_polyhedra_cone : forall d
    (generators : list (QVec d)) (value : QVec d),
  qcone_generated generators value <->
  qvec_to_rat_col value \in
    polyhedron.cone (rat_fset_of_generators generators)
```

The B0 membership lemmas state that each converted list generator belongs to
the finite set and every finite-set member has an originating list element.
Permutation, duplicate collapse, and collapse of `QVecEq`-equivalent
generators are also proved without function extensionality.

## Duplicate coefficient handling

`rat_weight_of_lists` is the sum of one-point finite-support functions. If a
column occurs repeatedly, finite-function addition combines its positional
coefficients. `combine_rat_weight_of_lists` proves that `combine` of the
result is the original ordered list linear combination.

In the reverse direction, `rat_coefficients_of_weight` assigns the current
finite-support coefficient to the first list element and removes that key
before recurring. Later duplicates therefore receive zero. The length,
nonnegativity, support, and linear-combination value are preserved. No choice
operator is used.

## Standard-Q connection

The forward proof uses `qcone_generated_aligned_coefficients`,
`q_to_rat_coefficients_nonnegative_iff`,
`qvec_to_rat_linear_combination`, and `qvec_to_rat_col_eq_iff`. The reverse
proof maps coefficients through `rat_to_q`, uses
`rat_to_q_nonnegative`, both scalar round trips, and the same A2 vector and
linear-combination API. Standard vectors are compared with `QVecEq`; no
Leibniz equality of `QVec` or nonnormalized `Q` values is required.

## Regression coverage

Focused examples cover dimension zero, the empty cone, zero, a positive ray,
the exclusion of the negative direction from `cone([1])`, lineality from
`cone([1;-1])`, `cone([2])` containing `1` through coefficient `1/2`, list
permutation, exact duplicates, numerically equal nonnormalized generators,
coefficient aggregation, and redundant/dependent generators.

## Verification and assumptions

The following commands exited zero on the final pre-review tree:

```text
make OPAMEXEC= check-t10-c4-3b-1-hrep-b
make OPAMEXEC= audit-t10-c4-3b-1-hrep-b
make -f Makefile.coq -j2
git diff --check -- <the five HRep-B target files>
```

The focused audit runs `coqchk -silent` for
`Mell.Geometry.QratConeAdapter` and
`Mell.Audit.QratConeAdapterExamples`. Fifteen public proof results were
checked with `Print Assumptions`; every result printed `Closed under the
global context`. The source gates found no `Admitted`, `Abort`, new `Axiom`,
`Classical_Prop.classic`, `ClassicalEpsilon`, UIP/K, `Eq_rect_eq`, functional
extensionality, constructive indefinite description, or external oracle.

## Independent review

An independent read-only review found no Critical or Important issues. Its
single Minor finding was that the two new Make targets were initially absent
from `.PHONY`; they are now registered there. The reviewer independently
recompiled the two modules, reran `coqchk`, confirmed all 15 assumption
reports were closed, and found no scope expansion into HRep-C.

The final commit identifier is recorded in the completion report.
