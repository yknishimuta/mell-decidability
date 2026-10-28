# T10-D Task 2A: capacity transformers and the Jančar order

Date: 2026-10-23

Baseline: `e2cdcef98811bf08d52dfe8477cde77c736fbe3f`

Scope: Leroux (2012), Section 5's transformer definitions, the periodic part
of Lemmas 5.1--5.2, and their operational connection to the Section 4 Jančar
order.  Asymptotic definability, relation cones, intraproductions, and
production graphs are not part of this unit.

## 1. Relation and transformer definitions

Composition executes its left operand first.  Equality of relations remains
pointwise; no function extensionality is used.

```coq
Definition NRelation (d : nat) := NVec d -> NVec d -> Prop.

Definition NRelCompose {d} (R S : NRelation d) : NRelation d :=
  fun input output =>
    exists middle, R input middle /\ S middle output.

Definition CapacityTransformer {d} (system : PlainVAS d)
    (capacity : NVec d) : NRelation d :=
  fun input output =>
    PlainVASReach system
      (nvec_add capacity input) (nvec_add capacity output).
```

Thus capacity membership retains all intermediate nonnegativity obligations
through `PlainVASReach`; it is not a displacement equation.  The implementation
also proves reflexivity, monotonicity in the capacity, closure under composing
two copies at the same capacity, associativity/unit laws for relation
composition, and monotonicity/congruence of composition.

For a run whose representation is a source and successive targets, every
configuration is included exactly once:

```coq
Fixpoint TransformerAlongTargets {d} (system : PlainVAS d)
    (current : NVec d) (targets : list (NVec d)) : NRelation d :=
  match targets with
  | [] => CapacityTransformer system current
  | target :: tail =>
      NRelCompose (CapacityTransformer system current)
        (TransformerAlongTargets system target tail)
  end.

Definition TransformerAlongRun {d} (system : PlainVAS d)
    (run : VASRun d) : NRelation d :=
  TransformerAlongTargets system (RunSource run) (RunTargets run).
```

A length-zero run therefore has one capacity factor, at its source.

## 2. Periodicity (Lemmas 5.1--5.2)

```coq
Definition PeriodicNRelation {d} (relation : NRelation d) : Prop :=
  relation (nvec_zero d) (nvec_zero d) /\
  forall x1 y1 x2 y2,
    relation x1 y1 -> relation x2 y2 ->
    relation (nvec_add x1 x2) (nvec_add y1 y2).

capacity_transformer_periodic :
  forall d (system : PlainVAS d) (capacity : NVec d),
    PeriodicNRelation (CapacityTransformer system capacity).

periodic_nrelation_compose :
  forall d (R S : NRelation d),
    PeriodicNRelation R -> PeriodicNRelation S ->
    PeriodicNRelation (NRelCompose R S).

transformer_along_run_periodic :
  forall d (system : PlainVAS d) (run : VASRun d),
    PeriodicNRelation (TransformerAlongRun system run).
```

The addition proof for a capacity transformer shifts the first witness run by
the second input and the second witness run by the first output, then composes
the resulting reaches.  For relation composition, the summed intermediate
point witnesses closure.  A list-level theorem extends this to finite
composition.

This completes Lemma 5.2 and only the periodic-algebra component of Lemma 5.1.
It does not establish asymptotic definability.

## 3. Jančar/transformer bridge

The checked public types are:

```coq
jancar_run_le_transformer :
  forall d (system : PlainVAS d) (rho sigma : VASRun d),
    ValidVASRun system rho ->
    ValidVASRun system sigma ->
    JancarRunLe rho sigma ->
    exists input output,
      RunSource sigma = nvec_add (RunSource rho) input /\
      RunTarget sigma = nvec_add (RunTarget rho) output /\
      TransformerAlongRun system rho input output.

transformer_realized_by_jancar_extension :
  forall d (system : PlainVAS d) (rho : VASRun d) input output,
    ValidVASRun system rho ->
    TransformerAlongRun system rho input output ->
    exists sigma,
      ValidVASRun system sigma /\
      JancarRunLe rho sigma /\
      RunSource sigma = nvec_add (RunSource rho) input /\
      RunTarget sigma = nvec_add (RunTarget rho) output.

transformer_along_run_iff_jancar_extension :
  forall d (system : PlainVAS d) (rho : VASRun d) input output,
    ValidVASRun system rho ->
    (TransformerAlongRun system rho input output <->
      exists sigma,
        ValidVASRun system sigma /\
        JancarRunLe rho sigma /\
        RunSource sigma = nvec_add (RunSource rho) input /\
        RunTarget sigma = nvec_add (RunTarget rho) output).
```

The forward operational proof follows `JancarGapDecomposition`: every gap is
a reach witness for the capacity at the corresponding small-run
configuration.  Conversely, the proof opens each relational-composition
witness, converts each capacity reach to a valid gap run, shifts the matched
small transition by the intermediate offset, and concatenates gap and matched
transition recursively.  The last capacity factor becomes the trailing gap.

The converse is deliberately existential in `sigma`.  It does not claim that
an arbitrary valid run with the prescribed endpoints is a Jančar extension.
The regression `audit_same_endpoints_not_enough_for_jancar` uses
`0 --(+1)--> 1` versus `0 --(+2)--> 2 --(-1)--> 1`: both endpoints agree, but
the larger word contains no matched `+1` action.

## 4. Regression coverage

Focused examples cover dimension zero; empty, zero, duplicate, positive and
negative actions (through the Task 1 system); zero and nonzero capacity;
reflexive and differing offsets; length-zero and nonempty run transformers;
composition through an intermediate offset; and a constructed Jančar
extension.  The invalid word `[-1;+1]` from zero is again rejected as a run
witness even though its displacement is zero.  The capacity relation at
equal endpoints remains reflexive by the empty run, so the regression states
the precise word-sensitive fact rather than the false negation of transformer
membership.

## 5. Task 2B handoff

Task 2B still needs:

- an integer-vector-pair representation for periodic relations and its bridge
  from `NRelation`;
- the nonnegative-rational cone of a relation and its `QDefinable` interface;
- closure of rationally definable relations under relational composition;
- the nontrivial theorem relating cone generation and composition, including
  common-denominator clearing and equality of the intermediate vectors;
- the asymptotic-definability half of Leroux Lemma 5.1 and its induction over
  run capacities.

In particular, no theorem of the form
`Cone (R ○ S) = Cone R ○ Cone S` is assumed here.

## 6. Assumptions and verification

RED was observed before the new modules existed: importing
`Mell.VAS.Transformer` failed.  The focused audit now compiles both modules and
the regression suite, checks the six central public theorems, runs `coqchk`,
and scans the target files for forbidden constructs.

`Print Assumptions` reports `Closed under the global context` for:

- `capacity_transformer_periodic`;
- `periodic_nrelation_compose`;
- `transformer_along_run_periodic`;
- `jancar_run_le_transformer`;
- `transformer_realized_by_jancar_extension`;
- `transformer_along_run_iff_jancar_extension`.

No new axiom, `Admitted`, `Abort`, `ClassicalEpsilon`, choice oracle,
UIP/K, `Eq_rect_eq`, or functional extensionality occurs in the target files.

An independent review approved the implementation with no Critical,
Important, or Minor findings.  It independently recompiled the three Coq
modules, reran `coqchk -silent`, confirmed all six assumption reports are
closed, and checked the composition direction, the existential nature of the
reverse Jančar bridge, the regression boundary, and the Task 2B scope.
