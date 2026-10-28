# T10-C1-QE2 audit

## Scope and baseline

- Baseline: `92ea1804ff44b9abc7a06b752cd0834d17b0da51`.
- Scope: revised C1 plan, Section 4 only.
- C1-HL and C1-QE1 declarations are consumed without modification.
- C1-Assembly and T10-C2 or later work are not included.

## Syntax and environment audit

`QTerm` contains variables, rational constants, addition, negation, and
rational scaling.  It has no multiplication of two variable terms.
`QFormula` contains `Top`, `Bot`, rational affine equality, strict and weak
order, Boolean connectives, negation, and existential and universal binders.
Both quantifiers extend the environment at de Bruijn index 0; the preceding
environment is observed at successor indices.

The output type is `QAffineDNF := list QAffineConjunction`.  An empty DNF is
false and an empty conjunction is true.  Cell membership is interpreted by
`qconjunction_semantics`; rational equality remains `Qeq`.

## RED/GREEN

The RED example module imported `Mell.Geometry.RationalQENormalForm` and
required the public correctness, scope, and finite-cell theorems.  Before the
implementation, `coqc` failed only because that logical path did not exist.

The GREEN implementation constructs finite DNF directly:

- conjunction is the finite Cartesian product of cell lists;
- disjunction is list append;
- positive equality is normalized to the conjunction of its two weak
  inequality orientations;
- equality negation is the disjunction of the two strict orientations;
- weak-order negation reverses to strict order;
- strict-order negation reverses to weak order;
- DNF negation applies De Morgan structurally;
- existential elimination distributes over the finite cell list and invokes
  C1-QE1's `eliminate_one_correct` for each cell;
- universal elimination is `not (exists (not body))`.  Its reverse proof uses
  the explicitly proved decidability of finite affine-DNF semantics, not
  classical logic.

`qformula_to_dnf_closed` follows the de Bruijn shift through C1-QE1:
`separate_term_tail_closed` proves that a term closed under `S d` has a
separated tail closed under `d`; the proof then propagates closure through
constraint classification, endpoint formation, pair constraints, and output
cell conversion.

## Complete public types

```coq
qaffine_dnf_and_correct :
  forall (environment : QEnvironment) (left right : QAffineDNF),
    qaffine_dnf_semantics environment (qaffine_dnf_and left right) <->
    qaffine_dnf_semantics environment left /\
    qaffine_dnf_semantics environment right

qaffine_dnf_neg_correct :
  forall (environment : QEnvironment) (dnf : QAffineDNF),
    qaffine_dnf_semantics environment (qaffine_dnf_neg dnf) <->
    ~ qaffine_dnf_semantics environment dnf

qaffine_dnf_exists_correct :
  forall (environment : QEnvironment) (dnf : QAffineDNF),
    qaffine_dnf_semantics environment (qaffine_dnf_exists dnf) <->
    exists bound : Q,
      qaffine_dnf_semantics
        (qenvironment_extend environment bound) dnf

qformula_to_dnf_correct :
  forall (formula : QFormula) (environment : QEnvironment),
    qformula_semantics environment formula <->
    qaffine_dnf_semantics environment (qformula_to_dnf formula)

qformula_to_dnf_closed :
  forall (formula : QFormula) (bound : nat),
    qformula_closed bound formula = true ->
    qaffine_dnf_closed bound (qformula_to_dnf formula)

qdefinable_finite_cells :
  forall (d : nat) (C : QSet d),
    @QDefinable d C ->
    exists cells : list QAffineConjunction,
      forall x : QVec d,
        C x <->
        exists cell : QAffineConjunction,
          List.In cell cells /\
          qconjunction_semantics (qvec_environment x) cell
```

## Regressions

The example module covers true, false, empty DNF, the empty conjunction,
equality and disequality, negated strict and weak inequalities, dense open
intervals, one-sided totality, nested `forall`/`exists`, the absence of a
greatest rational, nested negation with binder shadowing, two free variables,
zero free variables and dimension zero, and a non-normalized rational value.

## Verification and assumptions

The following canonical command completed with exit status 0 against the
final source:

```text
make audit-t10-c1-qe2
```

It includes the focused build, all regression examples, forbidden-dependency
scans, and:

```text
coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper \
  Mell.Geometry.RationalQENormalForm \
  Mell.Audit.RationalQENormalFormExamples
```

Direct `.vo` regression targets for T10-A0-L, A0-QF, A0-QE, T10-A, T10-B,
C1-HL, C1-QE1, and C1-QE2 also completed with exit status 0 without invoking
their log-writing audit targets.

`Print Assumptions` reported `Closed under the global context` for:

- `qaffine_atom_neg_correct`;
- `qaffine_dnf_and_correct`;
- `qaffine_dnf_neg_correct`;
- `qaffine_dnf_exists_correct`;
- `qformula_to_dnf_correct`;
- `qformula_to_dnf_closed`;
- `qdefinable_finite_cells`.

There is no dependency on classical logic, constructive indefinite
description, UIP/K, `Eq_rect_eq`, functional extensionality, a new axiom, or
an oracle.

## Independent review

The independent read-only review identified one Important contract gap in
the first implementation: positive equality was retained as `QAEq` instead
of becoming two weak inequalities.  An explicit output-shape regression was
added and observed RED, the transformation and correctness/closure proofs
were corrected, and the full suite returned GREEN.  The reviewer then
performed a fresh compilation and kernel check of the final snapshot.  No
Critical, Important, or Minor findings remain; the final disposition is
`APPROVE`.  A separate machine-visible “no `QAEq` occurs” invariant theorem
was suggested as optional and judged nonblocking because the constructor
definition and explicit equality-shape regression already fix the required
normal form.
