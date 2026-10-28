# T10-D Task 6A audit: linear run order and finite cover

## Scope and source correspondence

This checkpoint formalizes the finite-basis construction at the beginning of
Section 6 of Leroux (2012), before Lemma 6.1.  The source relation is represented
as a base direction plus a finitely generated periodic relation.  Runs are
ordered by the conjunction of the existing Jančar embedding and membership of
their direction increment in that periodic relation.

Lemma 6.1 itself, its union decomposition, Lemma 6.2, and Corollary 6.3 are not
part of this checkpoint.

## Public representation

`LinearRelationData d` contains a base input, base output, and a finite list of
generator pairs.  Coefficients are `NVec (length generators)`.  The total
evaluators `GeneratedInput` and `GeneratedOutput` compute the two generated
components.  `GeneratedPeriodPairBy` records a particular coefficient witness;
`GeneratedPeriodPair` existentially hides it.

`LinearOmegaRun system data rho` is exactly validity of `rho` together with
membership of `(RunSource rho, RunTarget rho)` in the linear relation.

`LinearRunLe data rho sigma` is exactly:

- `JancarRunLe rho sigma`; and
- a single generated period pair equal to the source and target increments.

It is reflexive and transitive.  The negative regression
`minimal_audit_jancar_not_enough` verifies that Jančar comparison alone is not
accepted when the direction increment is absent from the generated period.

## Decorated runs and WQO

A decorated run is a valid-run subtype paired with one coefficient vector.
`DecoratedLinearRunValid` relates that coefficient vector to the run endpoints.
Coefficient representations are not assumed unique; the duplicate/zero
generator regression exhibits two distinct coefficient vectors for the same
generated pair.

`decorated_linear_run_wqo` is obtained from:

- `jancar_run_wqo` on valid VAS runs;
- `nvec_le_almost_full` (Dickson) on the fixed-length coefficient vector;
- `af_product`; and
- restriction to `DecoratedLinearRunValid` using the Prop-level `afs` adapters.

`decorated_linear_run_finite_cover` uses
`restricted_af_finite_cover_classic`.  It is a Prop-level finite existence
result and does not extract a coefficient-selection function.

`linear_omega_finite_cover` projects the finite decorated cover to its run
components.  For each queried Omega-run, a coefficient witness is eliminated
locally in Prop; there is no simultaneous or executable choice over all runs.

## Lemma 6.1 handoff

`linear_run_le_transformer_period_witness` combines the period increment in
`LinearRunLe` with `jancar_run_le_transformer`.  It returns the same input and
output offsets as both:

- a member of the finitely generated period relation; and
- a member of `TransformerAlongRun system rho`.

This is the direct completeness-side input for Task 6B.  Task 6B must still
prove both inclusions of the Lemma 6.1 decomposition and package the finite
union components.

The finite cover proved here is not identified with the literal set of all
minimal runs.  `StrictLinearRunLe` is exposed for later analysis, but quotient
or antisymmetry issues and reduction to literal minimal representatives remain
outside Task 6A.

## Verification and assumptions

Focused source build, focused regression, and `coqchk -silent` succeed through
`make audit-t10-d-task6a`.  A clean, forced rebuild of the complete
`_CoqProject` also succeeds after the final regression additions.

`Print Assumptions` results:

- generated-period algebra, order reflexivity/transitivity, the decorated WQO,
  and the transformer-period witness are closed under the global context;
- `decorated_linear_run_finite_cover` and `linear_omega_finite_cover` depend
  only on `Classical_Prop.classic`, inherited from
  `restricted_af_finite_cover_classic`.

The target-source scan finds no `Admitted`, `admit`, `Abort`, new `Axiom`,
`ClassicalEpsilon`, choice oracle, UIP/K, `Eq_rect_eq`, or functional
extensionality.  An initial vector proof using dependent destruction was
replaced after assumption auditing; the final public results do not inherit
`Eq_rect_eq`.

Boundary regressions cover dimension zero, empty generators, a proved-empty
Omega, a nonempty Omega with nonzero base and duplicate zero actions,
non-unique coefficient representations, Jančar-without-period,
period-without-Jančar, and a nontrivial comparison satisfying both conjuncts.

An independent read-only review returned PASS after checking the refined order,
product WQO, local Prop elimination of coefficient witnesses, transformer
offset alignment, literal-minimal distinction, boundary regressions, and the
forbidden-construction scan.
