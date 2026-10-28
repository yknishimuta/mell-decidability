# T10-E2: bounded branching (FoSSaCS 2026 Lemma 9) audit

Date: 2026-10-24

Branch: `work/mell-formalization`

Baseline: `585a703596d4217b546c147212a07c9b6d040d85`

## Scope and sources

This task formalizes Lemma 9 of Bizière–Leroux–Sutre, *Bridging the Gap
Between Plain VASS and Branching VASS*, FoSSaCS 2026, Section 4.  It uses the
already verified stateful context-transfer lemma (Task 6E0) and `Extend(B,F)`
(Task 6E1).  It does not construct the bounded-depth VASS section of Lemma 11.

Implementation files:

- `theories/BVASS/BoundedBranching.v`
- `theories/Audit/BoundedBranchingExamples.v`
- `_CoqProject` and the focused `Makefile` targets `check-t10-e2` /
  `audit-t10-e2`

## Definitions

`branching_depth` follows the paper exactly: a leaf has depth zero, a unary
node preserves its child's depth, and a node of arity at least two has one plus
the maximum child depth.  `run_node_count`, from Task 6E0, counts execution-tree
nodes (including leaves), not constructors of the `SRuns` list encoding.

`SameTargetAndSize alpha beta` is the conjunction of equality of the complete
root configuration (state and counters) and equality of `run_node_count`.

`RIndex B basis alpha index` permits an arbitrary valid representative `beta`
with `SameTargetAndSize alpha beta`, and a path-selected subrun of `beta` above
which the indexed basis run lies in `ContextOrder`.  It is deliberately not
restricted to subruns of `alpha` itself.  `RCardinality` is represented by a
NoDup list of basis indices selected in `Prop`; duplicate run values at
different basis indices remain distinct.

## OmissionSelection permutation bridge

`omission_selection_permutation_transport` first reifies each input occurrence
as an annotation containing its state and either `None` (retained) or the full
omitted counter vector.  A permutation is lifted to this annotation list and
then projected back.  Thus omitted configurations—not only states—move with
their occurrences; duplicates and reuse of the same available configuration
are preserved.  The theorem is closed under the global context.

`ChildPartition` scans the actual child-run order.  It retains precisely the
occurrences whose complete root configuration is not in `F`, omits the full
root configuration of the others, preserves multiplicity, and proves:

- a positional `OmissionSelection`;
- a permutation of old configurations with retained plus omitted ones;
- exact counter-sum preservation;
- retained length equals `bad_child_count`;
- validity of all recursively transformed retained runs.

`child_partition_extend_shortening` transports the omission certificate across
the `ValidSRun` child-state permutation, then applies Task 6E1's
`extend_local_root_shortening`.  Its displacement premise is justified by the
full configuration permutation and exact counter sum, including signed rule
actions.

## R decrease and strong induction

The already verified simultaneous sibling replacement changes the two siblings
at once and proves final-parent validity directly, so no possibly invalid
intermediate run is used.  The new unordered reordering lemma moves any selected
bad child to the first occurrence while preserving validity, root configuration,
node count, and bad-child count.  This makes the existing Lemma-8 exclusion
argument applicable to every bad child, not only a child with a later bad
sibling.

`r_cardinality_strict_from_excluded_index` uses NoDup basis-index lists and
`NoDup_incl_length`; it never requires NoDup run values.  Consequently each bad
child of a bad-count-minimal representative with at least two bad children has
strictly smaller R-cardinality.

`bounded_branching_by_r_cardinality` is strong induction on
`run_node_count`.  It replaces a run by a same-target, same-size representative
with minimal root bad-child count, recursively transforms only bad children,
and applies the local Extend shortening theorem.  The depth proof distinguishes:

- zero retained children: an added initial configuration, depth 0;
- one retained child: unary root, no depth increment;
- at least two retained children: one depth increment and strict R-cardinality
  decrease for every retained child.

The finite maximum is bounded from per-child inequalities.  No executable R
membership test, basis generator, or representative selector is introduced.

## Public theorem types

```coq
Theorem finite_basis_bounded_branching_depth : forall d q
    (B : SBVAS d q) basis,
  RunBasis B basis ->
  forall alpha,
    ValidSRun B alpha ->
    exists eta,
      ValidSRun (extend_bvass B (basis_root_configs basis)) eta /\
      root_config eta = root_config alpha /\
      branching_depth eta <= Nat.pred (length basis).
```

```coq
Theorem lemma_9_uniform_bounded_branching : forall d q
    (B : SBVAS d q),
  exists F bound,
    ReachableConfigurations B F /\
    forall alpha,
      ValidSRun B alpha ->
      exists eta,
        ValidSRun (extend_bvass B F) eta /\
        root_config eta = root_config alpha /\
        branching_depth eta <= bound.
```

```coq
Theorem lemma_9_reach_bounded_branching_iff : forall d q
    (B : SBVAS d q),
  exists F bound,
    ReachableConfigurations B F /\
    forall state counters,
      SReach B state counters <->
      exists eta,
        ValidSRun (extend_bvass B F) eta /\
        root_config eta = (state, counters) /\
        branching_depth eta <= bound.
```

The first theorem obtains `< length basis` and converts it to
`<= Nat.pred (length basis)` only after R-cardinality positivity has ruled out
the empty-basis/valid-run case.

## Regression coverage

The audit module checks leaf, unary, binary, and nested branching depths, and
distinguishes node count from branching depth.  It also exercises an adjacent
input permutation in which one state is retained and the other occurrence is
omitted with a nonzero full counter configuration.  General proofs cover empty
dimensions/state spaces vacuously, empty bases through coverage contradiction,
duplicate basis values by index, duplicate child configurations, arbitrary
child permutations, all-retained/all-omitted/mixed partitions, and signed rule
actions through exact `add_displacement` preservation.

## Axiom audit

`Print Assumptions omission_selection_permutation_transport` reports:

```text
Closed under the global context
```

The finite R selection/minimal representative and final Lemma 9 theorems report
only:

```text
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

This is the permitted Prop-level classical principle.  No new axiom,
`ClassicalEpsilon`, choice oracle, UIP/K, functional extensionality, `Admitted`,
`admit`, or `Abort` occurs in the task files.  The repository-wide `coqchk`
summary lists older third-party/project dependencies, but they are absent from
the dependency closure printed for the Task 6E2 public theorems.  The T10-G
concrete finite-cover audit likewise confirms that `context_order_finite_cover`
does not depend on `ClassicalEpsilon.constructive_indefinite_description`.

## Verification record

- Focused source compile: PASS.
- Focused regression compile: PASS.
- `make audit-t10-e2` (checks, assumptions, focused `coqchk`, scans): PASS.
- `make audit-t10-e0`: PASS.
- `make audit-t10-e1`: PASS.
- `make audit-bridges` (T09 bridge regression): PASS.
- `make audit-t10-g`: PASS.
- forced `_CoqProject` build with `make -B -f Makefile.coq -j2`: completed;
  subsequent full incremental invocation reported nothing left to build.
- full `make -f Makefile.coq validate` (`coqchk -silent` over all registered
  `.vo` files): PASS.
- prohibited-construct scans: PASS.
- targeted `git diff --check`: PASS.  The repository-wide check reports only
  pre-existing whitespace in unrelated tracked audit logs, which remain
  unstaged and unchanged by Task 6E2.
- staged diff check: PASS (Task 6E2 files only).
- independent read-only review: PASS, with no Critical or Important findings.
  The reviewer checked the arbitrary-equivalent-representative definition of
  R, full-configuration omission transport, direct simultaneous sibling
  replacement, strict index-cardinality decrease, all three depth cases,
  empty-basis/off-by-one handling, reachability equivalence directions, build
  registration, and the prohibited-construct boundary.  One non-blocking minor
  observation was that the concrete example file is intentionally narrower
  than the generic quantified regression lemmas.

No Task 6E3 VASS-section construction is included.
