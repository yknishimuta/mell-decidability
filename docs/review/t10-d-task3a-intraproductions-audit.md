# T10-D Task 3A: intraproductions and Leroux Lemmas 5.5–5.6

Date: 2026-10-23

Baseline: `9f067c732b17ef0adec1653d7bca371b3efae3f8`

Scope: Leroux (2012), Section 5.1 through Lemma 5.6, plus the bounded-coordinate
half of Lemma 5.7.  This unit does not prove the Lemma 5.7 existence direction
and does not define production graphs, Kirchhoff relations, or unconditional
asymptotic definability of capacity transformers.

## 1. Production triples and the three sets

```coq
Record ProductionTriple (d : nat) := {
  GammaInput : NVec d;
  GammaCapacity : NVec d;
  GammaOutput : NVec d
}.

Definition ValidProductionTriple {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) : Prop :=
  CapacityTransformer system (GammaCapacity gamma)
    (GammaInput gamma) (GammaOutput gamma).

Definition OmegaGamma {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (run : VASRun d) : Prop :=
  ValidVASRun system run /\
  exists multiplier : nat,
    RunSource run = nvec_add (GammaCapacity gamma)
      (nvec_scale multiplier (GammaInput gamma)) /\
    RunTarget run = nvec_add (GammaCapacity gamma)
      (nvec_scale multiplier (GammaOutput gamma)).

Definition QGamma {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (configuration : NVec d) : Prop :=
  exists multiplier : nat,
    PlainVASReach system
      (nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaInput gamma))) configuration /\
    PlainVASReach system configuration
      (nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaOutput gamma))).

Definition IntraProduction {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (value : NVec d) : Prop :=
  exists multiplier : nat,
    PlainVASReach system
      (nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaInput gamma)))
      (nvec_add (GammaCapacity gamma) value) /\
    PlainVASReach system
      (nvec_add (GammaCapacity gamma) value)
      (nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaOutput gamma))).
```

The same `multiplier` is shared by the source and target in all three
definitions.  Validity of a triple is actual reachability
`c+x ->* c+y`, not merely well-typed natural vectors.  `QGamma` is defined by
the two reachable segments and deliberately imposes no condition `c <= q`.

The exact run-occurrence bridge is:

```coq
qgamma_iff_occurs_in_omega :
  forall d (system : PlainVAS d) (gamma : ProductionTriple d)
    (configuration : NVec d),
    QGamma system gamma configuration <->
    exists run : VASRun d,
      OmegaGamma system gamma run /\ RunOccurs configuration run.
```

It uses the existing reach/run equivalence in both directions.  The forward
proof concatenates prefix and suffix runs at the common configuration; the
reverse proof splits reachability at an actually occurring configuration.
The source, target, and every intermediate configuration of an Omega run are
therefore members of `QGamma`.  The `n=0` reflexive witnesses prove
`QGamma system gamma (GammaCapacity gamma)`.  The public lemma
`omega_gamma_empty_at_capacity` explicitly supplies the valid empty Omega run
at that capacity, so the zero-multiplier case is also tested at the run level.

## 2. Periodicity of intraproductions

```coq
Definition PeriodicNSet {d} (set : NVec d -> Prop) : Prop :=
  set (nvec_zero d) /\
  forall left right,
    set left -> set right -> set (nvec_add left right).

intraproduction_periodic :
  forall d (system : PlainVAS d) (gamma : ProductionTriple d),
    PeriodicNSet (IntraProduction system gamma).
```

`IntraProduction h <-> QGamma (c+h)` is definitional.  Zero uses multiplier
zero.  Addition applies `capacity_transformer_periodic` to the two prefix
relations and to the two suffix relations, with multiplier `n1+n2` on both
sides.  Natural scalar closure is then a direct induction using zero and
addition.  No claim that `QGamma` itself is periodic is made.

## 3. Leroux Lemma 5.5

```coq
lemma_5_5_qgamma_add_intraproduction :
  forall d (system : PlainVAS d) (gamma : ProductionTriple d)
    (q h : NVec d),
    ValidProductionTriple system gamma ->
    QGamma system gamma q ->
    IntraProduction system gamma h ->
    QGamma system gamma (nvec_add q h).
```

If `q` uses multiplier `n` and `h` uses multiplier `n'`, the proof uses
`n+n'`.  For the prefix it shifts the `h`-prefix by `n*x`, then shifts the
`q`-prefix by `h`; for the suffix it shifts the `q`-suffix by `h`, then shifts
the `h`-suffix by `n*y`.  All four arrows are instances of the proved VAS
monotonicity theorem, so intermediate natural configurations are retained.
The scalar corollary proves `q+k*h` is in `QGamma` for every natural `k`.

## 4. Leroux Lemma 5.6

```coq
lemma_5_6_intraproduction_dominates :
  forall d (system : PlainVAS d) (gamma : ProductionTriple d)
    (q q' : NVec d),
    ValidProductionTriple system gamma ->
    QGamma system gamma q ->
    QGamma system gamma q' ->
    nvec_le q q' ->
    exists h : NVec d,
      IntraProduction system gamma h /\
      nvec_le q' (nvec_add q h).
```

The two memberships keep their independent multipliers `m` and `m'`.
Only after proving `q' = q + delta` from `q <= q'` does the implementation use
the exact natural subtraction `delta = q' - q`.  It chooses precisely

```text
h = delta + m * (x + y),       n = m + m'.
```

The four shifted reachability segments are the construction from Leroux's
proof.  Coordinatewise arithmetic proves every junction and finally
`q+h = q' + m*(x+y)`, hence `q' <= q+h`.  Truncated subtraction is never used
without the preceding componentwise comparison.

## 5. Bounded coordinates

```coq
Definition BoundedGammaCoordinate {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (index : Fin.t d) : Prop :=
  exists bound : nat, forall configuration,
    QGamma system gamma configuration ->
    (Vector.nth configuration index <= bound)%nat.

bounded_coordinate_intraproduction_zero :
  forall d (system : PlainVAS d) (gamma : ProductionTriple d)
    (index : Fin.t d) (h : NVec d),
    BoundedGammaCoordinate system gamma index ->
    IntraProduction system gamma h ->
    Vector.nth h index = 0%nat.
```

`FiniteGammaCoordinateValues` is a finite-list cover of the attained natural
coordinate values.  It is proved equivalent to boundedness by `List.seq` in
one direction and a finite maximum in the other.  For the zero theorem,
`(bound+1)*h` is an intraproduction; Lemma 5.5 applied at `c` puts
`c+(bound+1)*h` in `QGamma`.  A positive coordinate of `h` would exceed the
bound, so natural arithmetic forces that coordinate to zero.

This is only the bounded-to-zero direction of Lemma 5.7.

## 6. Regression coverage

The regression module checks:

- dimension zero;
- an empty action system distinguishes an invalid triple from a valid one;
- a zero-action system has a one-step Omega run whose source and target are
  unchanged;
- `system={+1}`, `c=0`, `x=0`, `y=1`, where every natural configuration is in
  `QGamma` and every natural offset is an intraproduction (including 1, 2,
  and their sum 3);
- a two-dimensional vertical system where the first coordinate is bounded by
  1, the second is unbounded, all intraproductions have first coordinate zero,
  and the concrete offsets `(0,1)` and `(0,2)` occur;
- a concrete application of Lemma 5.6 for `(1,1) <= (1,2)` and its `q=q'`
  case;
- `system={-1,+1}`, `c=1`, `x=y=0`, where configuration 0 is in `QGamma` even
  though it lies below the capacity.

The Omega regressions fix one common multiplier for both endpoints, check both
endpoints through the public occurrence lemmas, and use a concrete two-step
run to check that its strict intermediate configuration is in `QGamma`.

## 7. Verification and assumptions

The initial regression import failed before `Mell.VAS.Intraproductions`
existed (RED).  The focused source and regression build is GREEN.  The full
`_CoqProject` build reports nothing left to rebuild after the focused build;
`coqchk -silent` succeeds for both new modules.  Target-only forbidden-
construction scans and `git diff --check` also succeed.  Independent-review
findings are recorded in the completion report.

The regression prints assumptions for:

- `qgamma_iff_occurs_in_omega`;
- `intraproduction_periodic`;
- `lemma_5_5_qgamma_add_intraproduction`;
- `lemma_5_6_intraproduction_dominates`;
- `finite_gamma_coordinate_values_iff_bounded`;
- `bounded_coordinate_intraproduction_zero`.

The target sources introduce no use of `Classical_Prop.classic`, choice,
functional extensionality, proof irrelevance, or a new axiom.

An independent review checked the shared-multiplier definitions, the run
occurrence bridge, both shifted-segment arguments, the exact-subtraction
precondition in Lemma 5.6, and the bounded-coordinate proof.  Its initial
regression review identified missing explicit zero-action and intermediate-
configuration examples; both were added and recompiled.  The follow-up review
reported no remaining Critical, Important, or Minor findings.

## 8. Task 3B handoff: remaining half of Lemma 5.7

Task 3B must prove, for every valid production triple, an intraproduction
whose zero coordinates are exactly the bounded coordinates:

```coq
exists h,
  IntraProduction system gamma h /\
  forall index,
    BoundedGammaCoordinate system gamma index <->
    Vector.nth h index = 0%nat.
```

The remaining direction is: for every unbounded coordinate `i`, construct an
intraproduction with a strictly positive `i`-th component.  The intended
finite route is to use unboundedness to choose two `QGamma` points with a
strictly increasing `i`-coordinate, use `nvec_le_almost_full`/Dickson to make
the points componentwise comparable, apply
`lemma_5_6_intraproduction_dominates`, and read positivity from domination.
There are only finitely many coordinates; the resulting witnesses can be
combined with `intraproduction_add`.  The already proved bounded-coordinate
theorem ensures that addition cannot create a nonzero bounded coordinate.

Task 3B must audit how the unbounded-coordinate witnesses are extracted from
the relevant infinite sequence.  It must prefer existing Dickson/finite-cover
machinery and must not introduce countable choice, dependent choice, or
`ClassicalEpsilon`.  No production graph or Kirchhoff relation is needed for
this Lemma 5.7 step.
