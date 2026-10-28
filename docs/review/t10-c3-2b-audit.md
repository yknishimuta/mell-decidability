# T10-C3-2B audit: Center absorbs the closed linearization

Date: 2026-10-21

Baseline: `b9180f4876dda710fe6b16d8a6a37698445f3e86`

Scope: C3-2B only. This unit formalizes Bizière--Leroux--Sutre (2026),
Lemma 4.9. It does not implement the later C3-3 push-in lemma.

## Public results

With `Set Printing Implicit`, the public types are:

```coq
periodic_cone_positive_ray
     : forall (d : nat) (set : ZSet d) (point : QVec d),
       Periodic set ->
       Cone set point ->
       exists (value : ZVec d) (coefficient : Q),
         set value /\
         0 < coefficient /\
         QVecEq point
           (qvec_scale coefficient (zvec_to_qvec value))

center_add_closed_linearization
     : forall (d : nat) (set : ZSet d) (value offset : ZVec d),
       Periodic set ->
       Center set value ->
       ClosedLinearization set offset ->
       Center set (zvec_add value offset)

center_absorbs_closed_linearization
     : forall (d : nat) (set : ZSet d),
       Periodic set ->
       SameSet
         (fun result : ZVec d =>
          exists value offset : ZVec d,
            Center set value /\
            ClosedLinearization set offset /\
            result = zvec_add value offset)
         (Center set)
```

No nonnegativity, asymptotic definability, finite generation, or pointedness
assumption is added.

## Positive ray for a cone point

For periodic `P`, the existing
`periodic_standard_cone_denominator_clearing` changes any `Cone P x` proof
into

```text
x = (1 / denominator) * p,
```

where `p in P` and `denominator` is a positive natural number. Therefore the
coefficient is strictly positive. This also handles `x=0`: the periodic zero
of `P` and denominator one give a genuine positive-coefficient ray instead
of a forbidden zero coefficient.

## Main inclusion

From `Center P v`, `center_characterization` supplies a finite list `ps` in
`P`, a spanning equivalence `VecOf P <-> QSpan ps`, and an aligned strictly
positive vector `lambda` representing `v`.

For `q in ClosedLinearization P`, the proof extracts:

- `q in Difference P`;
- `zvec_to_qvec q in QClosure (Cone P)`.

At the uniform positive `epsilon` supplied by
`qspan_uniform_small_coefficients ps lambda`, closure supplies an
`x in Cone P` with every coordinate within `epsilon` of `q`. Put
`w = q - x`. The difference witnesses show `q in VecOf P`; denominator
clearing shows `x in VecOf P`; hence the spanning equivalence and closure of
`QSpan` under subtraction give `w in QSpan ps`. The closure inequality is
exactly `-epsilon < w_i < epsilon`.

The perturbation theorem yields `delta` with
`-lambda_i < delta_i < lambda_i`, so every `lambda_i + delta_i` is strictly
positive. The positive-ray representation `x = t*p` is prepended to `ps`
with coefficient `t>0`. Because `p in P`, prepending it does not change the
spanned `VecOf P`. Coordinatewise `Qeq` arithmetic then proves

```text
v + q = t*p + sum_i (lambda_i + delta_i) * ps_i.
```

`center_in_difference` and additive closure of `Difference P` give
`v+q in Difference P`; the reverse direction of `center_characterization`
finishes the Center proof.

## Reverse inclusion and equality

`0 in ClosedLinearization P` follows from `difference_zero`, the zero
constructor of `Cone`, and `qclosure_extensive`. Thus every center element is
represented as `v+0`. Together with the main inclusion this proves the exact
set equality, not merely one inclusion.

## Regression boundary

Examples cover dimension zero, the zero monoid, `2N`, all signed integers,
the nonnegative two-dimensional quadrant, the gap monoid, and a low-rank
generated periodic set. Separate examples verify `q=0`, a zero cone
approximant with a strictly positive ray coefficient, and the fact that
`0` is not in `Center(2N)`. Linear dependence, duplicate generators, tiny
positive bounds, and noncanonical rationals remain covered by the immediately
preceding C3-1B and C3-2A regressions used by this proof.

RED was observed before implementation: the audit module failed because
`Mell.Geometry.CenterAbsorption` did not exist.

## Trust boundary

`periodic_cone_positive_ray` is closed under the global context. The two
Center absorption results inherit only `Classical_Prop.classic` from
`center_characterization` and `qspan_uniform_small_coefficients`, ultimately
the existing finite-basis/H-cone results. No ClassicalEpsilon, UIP/K,
`Eq_rect_eq`, functional extensionality, new axiom, admitted result, or
selection oracle is introduced.

Final verification:

- `make CORE_LOG_DIR=/tmp/mell-c3-2b-logs audit-t10-c3-2b`
  (exit 0): focused build, public-type and assumption audit, forbidden
  dependency scans, and `coqchk -silent` for both new modules.
- `make CORE_LOG_DIR=/tmp/mell-c3-2b-regression check-t10-c3-1b
  check-t10-c3-2a` (exit 0): both immediate prerequisite stages.
- `opam exec --switch . -- make -f Makefile.coq -j2` (exit 0): complete Coq
  regression build.
- target-file `git diff --check` and forbidden-token scan (exit 0).

The independent reviewer returned **Ready**, with zero critical, important,
or minor findings. The reviewer independently checked the quantifier order,
both `VecOf` bridges, uniform closure perturbation, strict positivity
(including `x=0`), final `QVecEq`, Difference closure, reverse inclusion,
public assumptions, and both modules with `coqchk -silent`.
