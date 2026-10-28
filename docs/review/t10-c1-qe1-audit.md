# T10-C1-QE1 implementation and trust audit

Date: 2026-10-19

Baseline: `2275e7f3261065593c3af07ca112d447cf380f69`

Scope: C1-QE1 only. C1-QE2, C1-Assembly, and T10-C2 were not started.

## Preflight and syntax audit

The initial HEAD matched the baseline. Pre-existing modified audit logs and the 18 untracked files under `vendor/presburger/` were excluded from the change.

The existing rational syntax is affine:

```coq
Inductive QTerm :=
| QTVar : nat -> QTerm
| QTConst : Q -> QTerm
| QTAdd : QTerm -> QTerm -> QTerm
| QTOpp : QTerm -> QTerm
| QTScale : Q -> QTerm -> QTerm.
```

There is no constructor multiplying two terms. `QFExists` interprets its bound value at environment index 0 through `qenvironment_extend`; every previous variable moves to its successor index. Atomic equality uses `Qeq`; weak and strict inequalities use `Qle` and `Qlt`.

## RED

Before `RationalQEOne.v` existed, compiling the public client failed with:

```text
Error: Cannot find a physical path bound to logical path
RationalQEOne with prefix Mell.Geometry.
```

## Affine normalization and binder removal

`separate_term` decomposes a term under one binder into a rational coefficient of index 0 and a tail term whose variables have been shifted down by one. Its public correctness theorem is:

```coq
separate_term_correct :
  forall (term : QTerm) (environment : QEnvironment) (bound : Q),
    qterm_semantics (qenvironment_extend environment bound) term ==
    separated_semantics environment bound (separate_term term)
```

`normalize_atom` converts equality to two weak constraints and converts weak/strict atoms into constraints of the form `a*z <= rhs` or `a*z < rhs`. `normalize_atom_correct` and `normalize_conjunction_correct` prove evaluation preservation for arbitrary environments.

## Fourier–Motzkin elimination

Constraints are classified by the sign of `a`:

- `a<0`: lower bound `rhs/a`;
- `a=0`: residual quantifier-free constraint;
- `a>0`: upper bound `rhs/a`.

Division direction is proved separately for strict and weak inequalities. The eliminated conjunction contains every lower/upper pair, marked strict exactly when either endpoint is strict, plus every zero-coefficient residual. Since the input is one conjunction, the resulting finite DNF contains one conjunction.

The witness proof uses a finite maximum lower endpoint and finite minimum upper endpoint:

- no bounds: `0`;
- upper bounds only: minimum minus `1`;
- lower bounds only: maximum plus `1`;
- separated extrema: the rational midpoint `(lower+upper)/2`;
- equal extrema: their common value, with pair compatibility proving every active endpoint weak at equality.

No integer-discreteness transformation such as `u<v <-> u+1<=v` is used.

The central existence lemma is:

```coq
finite_bounds_have_witness :
  forall (environment : QEnvironment) (lowers uppers : list QEndpoint),
    Forall (fun lower =>
      Forall (endpoints_compatible environment lower) uppers) lowers ->
    exists bound : Q,
      Forall (lower_holds environment bound) lowers /\
      Forall (upper_holds environment bound) uppers
```

The final public theorem is:

```coq
eliminate_one_correct :
  forall (body : QAffineConjunction) (environment : QEnvironment),
    (exists bound : Q,
      qconjunction_semantics
        (qenvironment_extend environment bound) body) <->
    qdnf_semantics environment (eliminate_one body)
```

This quantifies over every free-variable environment and therefore includes the de Bruijn shift/renaming contract.

## Boundary regressions

`RationalQEOneExamples.v` checks:

- `exists z, 0<z /\ z<1` is true;
- `exists z, 0<z /\ z<=0` is false;
- `exists z, 0<=z /\ z<=0` is true;
- `exists z, 0<z /\ z<0` is false;
- upper-only, lower-only, and no-bound cases;
- `exists z, 2*z=1`;
- a zero coefficient constraint;
- a free variable at index 1 becoming index 0 after binder removal;
- the non-normalized rational boundary `2#2`.

## Verification

The following completed with exit status 0:

```text
make audit-t10-c1-qe1
```

This includes focused build, execution of every example, forbidden-assumption scans, and:

```text
coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper \
  Mell.Geometry.RationalQEOne Mell.Audit.RationalQEOneExamples
```

Regression `.vo` targets for C1-HL, T10-A0-L, T10-A0-QF, T10-A0-QE-Adapter, T10-A, and T10-B also built successfully without overwriting their audit logs.

## Assumptions

```text
Print Assumptions separate_term_correct.
Closed under the global context

Print Assumptions finite_bounds_have_witness.
Closed under the global context

Print Assumptions eliminate_one_correct.
Closed under the global context
```

There is no dependency on classical logic, constructive indefinite description, UIP/K, `Eq_rect_eq`, functional extensionality, a new axiom, or an oracle.

## Independent review

An independent read-only review found no Critical or code-level Important
findings.  It checked the affine-only source syntax, the de Bruijn index-0
separation and successor renaming, equality expansion, all coefficient-sign
and strictness branches, lower/upper cross products, witness construction, and
the arbitrary-environment equivalence.  The reviewer initially requested that
the canonical audit evidence be refreshed because the source was newer than
the recorded build artifacts.  `make audit-t10-c1-qe1` was consequently rerun
against the final source and completed with exit status 0.  No Minor findings
remain.  C1-QE2 and later stages were explicitly outside the review scope.
