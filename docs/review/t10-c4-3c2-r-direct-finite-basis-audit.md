# T10-C4-3C2-R direct finite-basis audit

## Scope and result

This change completes Lemma 6.10 without introducing a general bridge from
infinite sequences to the inductive `afs` predicate.  The implementation is
in `theories/Geometry/FaceStrippingLemma610FiniteBasis.v`; focused executable
regressions and public-type/assumption checks are in
`theories/Audit/FaceStrippingLemma610FiniteBasisExamples.v`.

The completed public theorem is:

```coq
lemma_6_10_maximal_extract_finitary :
  forall d
    (period excluded remaining : ZSet d)
    (face : QSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    MaximalNonemptyExtractFace
      period excluded remaining face ->
    FinitaryQCylindric
      (FacePeriod period face)
      (ExtractFace period face excluded remaining).
```

No C4-3D declaration is introduced.

## R0: explicit finite presentations and decisions

`zgenerated_formula generators value` is a closed Presburger formula.  It
existentially quantifies one integer variable per generator, asserts every
coefficient is nonnegative, and asserts coordinate-wise equality with
`value`.  Its correctness theorem identifies it exactly with
`zvec_generated generators value`, whose coefficients are natural numbers.
Thus coefficients are not widened to arbitrary signed integers.

`zvec_generated_dec_explicit` applies the repository's
`presburger_decide`/`presburger_decide_correct` API to that formula.
`FinitelyPresented generators bases` is the finite union of generator-monoid
translates with bases from the explicit list.  Its membership decision is a
finite search over `bases` using the generated-monoid decision.

The collision excluded by Extract is reduced to

```text
value - base = period_part + (- face_part)
```

with generator list `period_generators ++ map zvec_opp face_generators`.
This is equivalent to the requested Diophantine equation

```text
value + face_part = base + period_part.
```

The public decision procedures take concrete generator and base lists plus
their semantic specifications:

- `extract_face_dec_explicit` decides Extract membership;
- `face_periodic_le_dec_explicit` decides `PeriodicLe` for the explicitly
  generated face period.

The key semantic reduction is `extract_face_cylindric_characterization`:

```coq
ExtractFace period face excluded remaining value <->
remaining value /\
~ (exists increment,
    FacePeriod period face increment /\
    excluded (zvec_add value increment)).
```

It uses zero and closure of `FacePeriod`, plus cylindricity of `remaining`.

### Prop/Set boundary

No API attempts to eliminate an abstract Prop witness of
`FinitelyGeneratedPeriodic` into a Set-level decision procedure.  R0's
decision APIs accept the actual finite lists.  In the final theorem, the
existential generator/base witnesses are destructed only inside the proof of
the Prop-valued `FinitaryQCylindric` conclusion.  Those lists are then passed
to R0.

## R1: direct bad sequence

`monotone_subsequence_implies_finitary` has the contracted type: it assumes
periodicity, cylindricity, decidable set membership, decidable `PeriodicLe`,
and the infinite monotone-subsequence property, and concludes
`FinitaryQCylindric`.

The proof first assumes that no finite cover exists.  For every finite prefix
of set elements, classical propositional reasoning yields another set element
that is not above any prefix element.  Signed integer vectors are countably
encoded using a proved retraction: a tagged sign/magnitude codec handles each
integer and a structural decoder consumes the fixed vector dimension
recursively.  No dependent equality cast or UIP lemma is used.  Since both
membership and order are decidable, escape from a concrete prefix is decidable
on natural-number codes.

`constructive_indefinite_ground_description_nat` then selects a least
escaping code.  Primitive recursion on the prefix constructs an infinite bad
sequence satisfying

```text
i < j -> ~ PeriodicLe period (sequence i) (sequence j).
```

The assumed strictly increasing monotone subsequence supplies a related pair
at indices 0 and 1, contradicting badness.  The resulting finite cover is
turned into the required translate equality using cylindricity.  Every basis
element is stored as a subtype carrying its proof of set membership, so the
final bases belong to the set itself.

This proof uses no `afs`, countable choice, dependent choice, or epsilon
operator.  `constructive_indefinite_ground_description_nat` is constructive
search over a decidable natural predicate.

## R2: Lemma 6.10 integration

The final proof obtains explicit generators for `period` and
`FacePeriod period face`, and explicit bases for `excluded` and `remaining`.
It derives the semantic finite-presentation specifications, constructs the R0
membership/order decisions, and invokes R1 with:

- `extract_face_cylindric`;
- `face_periodic` and `face_periodic_finitely_generated`; and
- the already completed `maximal_extract_monotone_subsequence`.

Consequently the existing translation normalization, common-normal geometry,
face collapse, and two-stage subsequence construction are reused unchanged.
No geometric argument from C4-3C2 is duplicated.

## Focused regressions

The focused audit executes the Presburger decisions for dimension zero,
`2N`, a translated `1 + 2N`, `2N^2`, and a lower-rank first-axis face period.
It checks acceptance and rejection, including Extract membership for the
points 1 and 9 of `1 + 2N`, which are outside `2N`.  The two-dimensional
tests use `Q = 2N^2`, the first-coordinate-axis face period,
`X = (1,3) + Q`, and `Y = (1,1) + Q`.  The executable Extract decision accepts
`(1,1)` and rejects the colliding point `(1,3)`; separate order tests distinguish
an on-axis face difference from an off-axis difference.  Existing C4-3C2
regressions continue to cover generic simultaneous translation, anchor
normalization, and composed strict subsequence indices.

## Assumptions and prohibited constructions

`Print Assumptions` for the R0 decisions, R1 theorem, and final Lemma 6.10
reports only `Classical_Prop.classic`.  The dependency arises from the finite
non-cover contradiction in R1 and inherited finite-face/supporting-normal
selection in `maximal_extract_monotone_subsequence`.

There is no new axiom, `Admitted`, `Abort`, `ClassicalEpsilon`, countable or
dependent choice, UIP/K, `Eq_rect_eq`, functional extensionality, or external
oracle.  The constructive natural search adds no axiom.

## Verification

The final verification records focused compilation, the complete Coq build,
`coqchk -silent`, public type and assumption output, a prohibited-token scan,
target-scoped `git diff --check`, and an independent review.  Exact command
results and the review disposition are recorded in the completion report.
