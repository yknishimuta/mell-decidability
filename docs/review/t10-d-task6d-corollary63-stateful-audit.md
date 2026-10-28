# T10-D Task 6D audit: Corollary 6.3 and finite-control VAS

## Scope and baseline

- Repository: `mell-formalization`
- Branch: `work/mell-formalization`
- Starting HEAD: `c3651f6659951e2e4e81daefbefa8ec961d4490a`
- Scope stops after Corollary 6.3 and the two stateful parent-contract theorems.
- Pre-existing audit logs, `FaceStrippingBasesExamples.v`, and
  `vendor/presburger/` were preserved and excluded from staging.

## Stateless assembly

`SemilinearNRelation R` is the existing `SemiCode` presentation of the packed
pair predicate.  `npair_pack`, `npair_left`, and `npair_right` provide the
proved additive adapter between `NVec (d+d)` and two `NVec d` values.

`semilinear_nrelation_finite_linear_decomposition` maps every finite
`SemiCode` component to a `LinearRelationData`; its generators are split into
input/output pairs.  Both directions are proved through the actual
`weighted_sum`, so empty, zero, and duplicate generator lists require no
special assumptions.

`plain_vas_reach_inter_semilinear` applies Task 6C separately to this finite
list and uses `almost_semilinear_nrelation_finite_union` to reassemble it.

## Projection and Corollary 6.3

For an asymptotically definable periodic relation, source and target
projections are periodic.  The cone/projection equalities use
`periodic_cone_positive_multiple_iff`; they retain the exact `NRelationAsZ`
nonnegativity witnesses and never apply a truncating integer-to-natural map.
The rational projection formula is supplied by `qdefinable_projection`, with
the `Fin.L`/`Fin.R` pair coordinates proved explicitly.

The component projection maps both the base and its period relation.
`corollary_6_3_plain_post_inter_almost_semilinear` and its `pre` counterpart
first intersect reachability with `X × Y`, then apply the target/source
projection respectively.  `Y` constrains only the endpoint.

## Finite-control encoding

No compatible unary finite-control `VAS`, `VASReach`, or stateful
semilinearity API existed at the baseline.  The added public model is:

```coq
Definition SConfig (d q : nat) := (Fin.t q * NVec d)%type.
Definition VAS (d q : nat) := list (VASTransition d q).
```

A transition at list position `i`

```text
p --a--> r
```

is encoded in dimension `d + q + length system` by:

```text
start  = (a, -e_p, +e_i)
finish = (0, +e_r, -e_i).
```

Normal configurations carry one state token and no gate token.  Intermediate
configurations carry no state token and the unique transition gate.  The
inverse proof rejects finish actions at normal configurations and start
actions at gates, and shows that a finish at a gate must use the same list
position.  Hence self-loops also consume and restore the token; they cannot
bypass the state test.

The operational and encoded relations are proved equivalent:

```coq
vas_reach_direct_iff :
  forall d q (system : VAS d q)
    source_state source target_state target,
    VASReach system source_state source target_state target <->
    DirectVASReach system source_state source target_state target.
```

This covers empty transition lists, dimension zero, and state count zero
vacuously (there is no `Fin.t 0` endpoint to quantify).

## Stateful assembly

Stateful semilinearity is represented by a semilinear counter relation for
each finite source/target state pair.  Each pair is lifted to encoded normal
endpoints; the lifted generators have zero state and gate coordinates.
Projection back to the first `d` coordinates is proved with
`ProjectNRelation`, not by assuming injectivity.

For `post*`, `fin_collect` enumerates all `Fin.t q` source states.  Each fixed
state-pair slice is target-projected, and
`almost_semilinear_nset_finite_union` joins the finite list.  Thus both state
tags are retained until the final target slice is formed, including `q=0`.

The final public contracts are exactly:

```coq
vas_reach_relation_inter_semilinear :
  forall d q (system : VAS d q)
    (relation : SConfig d q -> SConfig d q -> Prop),
    StatefulRelationSemilinear relation ->
    StatefulRelationAlmostSemilinear
      (fun source target =>
        relation source target /\
        VASReach system (fst source) (snd source)
          (fst target) (snd target)).

vas_post_inter_semilinear :
  forall d q (system : VAS d q)
    (source_set target_set : SConfig d q -> Prop),
    StatefulSemilinear source_set ->
    StatefulSemilinear target_set ->
    StatefulAlmostSemilinear
      (fun target =>
        target_set target /\
        exists source,
          source_set source /\
          VASReach system (fst source) (snd source)
            (fst target) (snd target)).
```

## Assumption audit

- The finite-control encoding and its bidirectional reachability proof are
  closed under the global context.
- The finite semilinear decomposition is closed under the global context.
- Projection definability and the final almost-semilinearity theorems inherit
  only `Classical_Prop.classic` through the previously accepted Task 6C finite
  basis and rational-definability infrastructure.
- No `ClassicalEpsilon`, choice oracle, UIP/K, `Eq_rect_eq`, functional
  extensionality, new `Axiom`, `Admitted`, `admit`, or `Abort` is used.

## Verification record

The final run recorded:

- `make check-t10-d-task6d`: exit 0.
- `make audit-t10-d-task6d`: exit 0, including the public `Check` output,
  `Print Assumptions`, focused `coqchk`, and both forbidden scans.
- `opam exec --switch . -- make -f Makefile.coq -B -j2`: exit 0; this
  forcibly rebuilt every source in `_CoqProject`.
- final post-rebuild `coqchk -silent` for all Task 6D modules and the audit
  module: exit 0.
- `git diff --check` on the authorized file set: exit 0.

The full rebuild printed an existing `ConstructiveEpsilon` dependency from
`FiniteCoverAssumptions.v`; it is not in the dependency closure printed for
the Task 6D public theorems.  Their only inherited non-closed result is
`Classical_Prop.classic`, as listed above.

## Independent acceptance review

The review checks the mathematical contract, not only compilation:

- packed pairs preserve both endpoints and addition;
- projection preserves the exact nonnegative integer adapter;
- post and pre constrain endpoints rather than all intermediate states;
- finite-control transitions cannot skip their dedicated gate;
- same-index finish is forced by gate nonnegativity;
- state-pair tags remain present through the finite union;
- both final theorem statements have no additional mathematical premise.

No Section 7/T10-E/F/T11 result is claimed here.
