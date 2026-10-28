# Task 11-A — Doubled Relation and Period Geometry Audit

## Scope and source correspondence

This audit covers Bizière–Leroux–Sutre, *Solving the Reachability Problem for
Branching Vector Addition Systems via Semilinear Inductive Invariants*,
arXiv:2607.09558v1, Sections 3–4: Lemmas 4.6, 4.10, 4.11, 3.12, and 3.13.
Task 11-B is outside the scope of this change.

Implementation files:

- `theories/Separator/DoubledRelation.v`
- `theories/Separator/TransformerPeriod.v`
- `theories/Separator/DirectedRuns.v`
- `theories/Audit/SeparatorPeriodGeometryExamples.v`

The public `IBVAS`, `IRun`, `IRunLe`, periodic-set, cone, and closed
linearization definitions were not changed.

## Public results

```coq
Theorem lemma_4_6_special_leaf_inter_semilinear : forall d
    (system : IBVAS d) (H : NRelation d),
    SemilinearNRelation H ->
    AlmostSemilinearNRelation
      (fun input output => H input output /\
        SpecialLeafReach system input output).

Theorem lemma_4_10_special_transformer_asymptotically_definable : forall d
    (system : IBVAS d) base,
    AsymptoticallyDefinableNRelation
      (SpecialTransformer system base).

Theorem lemma_4_11_irun_period_asymptotically_definable : forall d
    (system : IBVAS d) root,
    ValidIRun system root ->
    AsymptoticallyDefinableNSet (IRunPeriod system root).

Theorem lemma_3_12_directed_closed_period_finitely_generated : forall d
    (system : IBVAS d) (directed : DirectedIRun system),
    FinitelyGeneratedPeriodic (DirectedClosedPeriod directed).

Theorem lemma_3_13_directed_closed_period_inclusion : forall d
    (system : IBVAS d) (source target : DirectedIRun system),
    DirectedIRunEdge source target ->
    DirectedConeIncluded source target ->
    forall value,
      DirectedClosedPeriod source value ->
      DirectedClosedPeriod target value.
```

The SCC-facing consequence is
`mutually_reachable_equal_cones_closed_period_equal`.

## Lemma 4.6 and restriction before projection

`DoubledRelation.v` uses dimension `2 + 2*d`, with two marker coordinates
followed by input and output blocks.  Marker-total-one is imposed before the
input/output projection.  `doubled_marker_one_iff` identifies precisely one
distinguished leaf, including when its value equals an ordinary initial
configuration.  Marker-total-zero and marker-total-at-least-two runs are not
accepted by the projected relation.  The one-state `SBVAS` bridge then applies
`bvass_reach_inter_semilinear`.

## Lemmas 4.10 and 4.11

`SpecialTransformer system base input output` is the paper's relation from
`base + input` to `base + output`.  Its additive closure is witnessed by
explicit valid-run constructions; it is not inferred from root monotonicity.

For a valid initialized run `root`, the period set is

```coq
IRunPeriod system root offset :=
  exists extension,
    ValidIRun system extension /\
    IRunLe root extension /\
    irun_target extension = nvec_add (irun_target root) offset.
```

`irun_period_periodic` uses `run_amalgamation`.  The exact structural equation
is `irun_period_structural_decomposition`; its empty-child sum is the singleton
zero set.  Both directions are proved by mutual induction over `IRun`/`IRuns`.
The forward direction decomposes the `IRunLe` embedding into matched children
and surrounding context.  The reverse direction realizes every child offset,
rebuilds the root rule with the original multiplicities, and applies the
special-leaf transformer context.  The cone argument is implemented through
zero-source relations, relation composition, target projection, and the
existing rational-cone closure theorems.

## Directed runs and Lemma 3.12

`DirectedIRun system` stores a valid root run, a finite list of rational cone
generators, and a proof that the generated cone lies in the nonnegative
orthant.  The definitions are:

```coq
DirectedOffset w x :=
  IRunPeriod system (directed_root w) x /\
  DirectedCone w (nvec_to_qvec x).

DirectedPeriod w := NSetAsZ (DirectedOffset w).
DirectedClosedPeriod w := ClosedLinearization (DirectedPeriod w).
```

`directed_period_cone_iff` proves the exact equation
`Cone(P_w) = Cone(P_root) ∩ C_w`.  Its rational-cone integer-section step is
proved by `rational_polyhedral_integer_points_cone`; no rational point is
treated as an integer point.  Periodicity, nonnegativity, and Q-definability
then feed the existing `closed_linearization_finitely_generated` theorem.
`directed_run_targets` gives the exact target-set equation
`target(IRuns(w)) = target(root(w)) + P_w`.

## Directed edges and Lemma 3.13

`IRunOccurrence subrun whole` carries an explicit one-hole `IContext`; equal
subrun values at different positions therefore remain distinguishable.
`irun_occurrence_lift` applies the existing constructive `context_lift`,
preserving validity, `IRunLe`, and the exact root increment.

For `source ↠ target`, `directed_edge_translated_offset_inclusion` constructs
the offset `z` of the target edge witness and proves

```text
z ∈ P_target
z + P_source ⊆ P_target.
```

The source expansion is amalgamated with the occurrence witness, then lifted
through its concrete context.  The same translation cancels in differences,
yielding `P_source-P_source ⊆ P_target-P_target`.

The cone proof deliberately does **not** claim the generally false raw
inclusion `Cone(P_source) ⊆ Cone(P_target)`.  The proof
`translated_period_cone_closure` represents a source-cone point by a positive
integer multiple, uses periodicity to obtain `z + k*p`, and scales it to the
approximant `p/m + z/(m*k)`.  A constructive rational ceiling chooses `k` so
that every coordinate error is below the requested rational radius.  Thus it
proves inclusion only into `QClosure(Cone(P_target))`; idempotence lifts this to
closed-cone inclusion.  This handles the standard counterexample
`P_u = N×{0}`, `P_v = {0} ∪ (N×N_{>=1})`, `z=(0,1)`, where raw cone inclusion
fails but closed-cone inclusion holds.

## Axiom boundary

Observed with `Print Assumptions`:

- `lemma_4_11_irun_period_asymptotically_definable`:
  `Classical_Prop.classic` only (inherited through the existing T10-E finite
  basis/almost-semilinearity dependency).
- `lemma_3_12_directed_closed_period_finitely_generated`:
  `Classical_Prop.classic` only, inherited through Lemma 4.11.
- `irun_occurrence_lift`: closed under the global context.
- `translated_period_cone_closure`: closed under the global context.
- `lemma_3_13_directed_closed_period_inclusion`: closed under the global
  context.

No Axiom, Admitted/admit, Abort, ClassicalEpsilon, choice oracle, UIP/K,
Eq_rect_eq, functional extensionality, or kernel-check disabling option was
introduced.

## Verification and review

The following checks passed on branch `work/mell-formalization`, starting from
`63b241a47081d32a9ad7dc0c7f3495574362e868`:

- focused compilation of all three Separator modules and
  `SeparatorPeriodGeometryExamples.v`;
- focused T06/T09, Task 6D, and Task 6E4 regression targets;
- `make audit-t10-g`;
- forced `make -B -f Makefile.coq -j2` over the complete `_CoqProject`;
- `make -f Makefile.coq validate`;
- `coqchk -silent` on `DoubledRelation`, `TransformerPeriod`, and
  `DirectedRuns`, including their dependency closure;
- public `Check` and `Print Assumptions` commands;
- prohibited-construction and whitespace-error scans.

The full-project `validate` output reports the repository's pre-existing broad
dependency context, while the theorem-local assumption results above isolate
the actual Task 11-A boundary.

Independent review passed without findings.  It separately compiled
`TransformerPeriod.v` and `DirectedRuns.v` and checked the two directions of
the Lemma 4.11 decomposition, the exact cone equation, occurrence-specific
lifting, translated-offset cancellation, the closed-cone approximation, and
the SCC corollary.  The reviewer noted that `IRunOccurrence` uses a one-hole
context witness rather than an exposed numeric path; this still distinguishes
the selected occurrence and preserves all non-hole branches.

## Outstanding obligations

None.  The local commit identifier is reported in the completion report (a
commit cannot contain its own final hash).
