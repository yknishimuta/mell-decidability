# Task 11-E audit: Safety Witness, homogeneous SCC, and rank descent

Date: 2026-10-26

Source: Bizière–Leroux–Sutre, *Solving the Reachability Problem for
Branching Vector Addition Systems via Semilinear Inductive Invariants*,
arXiv:2607.09558v1, Sections 3 and 7.

## Scope and files

Task 11-E is implemented in:

- `theories/Separator/Attractor.v`
- `theories/Separator/FiniteGraph.v`
- `theories/Separator/SafetyWitness.v`
- `theories/Separator/RankDecrease.v`
- `theories/Separator/WitnessUpdate.v`
- `theories/Audit/SafetyWitnessExamples.v`

All six modules are registered in `_CoqProject`.  Task 11-F is not included.

## Public contracts

The final theorem has the following complete type:

```coq
Theorem lemma_7_1_safety_witness_rank_descent :
  forall d (system : IBVAS d) (safe : NSet d)
    (witness : SafetyWitness system safe),
    witness_nodes witness <> [] ->
    exists next : SafetyWitness system safe,
      WitnessRankLess (witness_nodes next) (witness_nodes witness).
```

The rank order is defined from the occurrence counts at every cone span
dimension.  It compares the largest differing dimension first:

```coq
Definition WitnessRankLess {d} {system : IBVAS d}
    (next previous : list (DirectedIRun system)) : Prop :=
  high_rank_less d (witness_rank_tuple d next)
    (witness_rank_tuple d previous).

Theorem witness_rank_less_well_founded : forall d (system : IBVAS d),
  well_founded (@WitnessRankLess d system).
```

The Section 7 run lemmas exposed by the implementation are:

```coq
Theorem lemma_7_2_safety_witness_successors : forall d
    (system : IBVAS d) safe (witness : SafetyWitness system safe)
    source source_run output,
  List.In source (witness_nodes witness) ->
  DirectedRunMember source source_run ->
  SpecialLeafReach system (irun_target source_run) output ->
  witness_attractor witness output /
  exists target,
    WitnessSuccessor (witness_nodes witness) source target /\
    exists target_run,
      DirectedRunMember target target_run /\
      irun_target target_run = output /\
      IRunOccurrence source_run target_run.

Theorem lemma_7_3_attractor_contact_propagation : forall d
    (system : IBVAS d) attractor period source target,
  Attractor system attractor ->
  PeriodicNSet period ->
  NSetStable attractor period ->
  DirectedIRunEdge source target ->
  (forall offset, NClosedDirectedPeriod source offset <-> period offset) ->
  (forall offset, NClosedDirectedPeriod target offset <-> period offset) ->
  (exists value,
    attractor value /\ DirectedRootTranslate source period value) ->
  exists value,
    attractor value /\ DirectedRootTranslate target period value.

Theorem lemma_7_4_directed_irun_rebase : forall d
    (system : IBVAS d) node run
    (member : DirectedRunMember node run),
  (forall extension,
    DirectedRunMember (rebase_directed_irun node run member) extension ->
    DirectedRunMember node extension) /\
  (forall value,
    DirectedPeriod (rebase_directed_irun node run member) value ->
    DirectedClosedPeriod node value).

Theorem lemma_7_5_new_node_edge_direction : forall d
    (system : IBVAS d) period excluded remaining faces earlier later
    source target,
  (forall run, DirectedRunMember source run ->
    StrippingSlice period excluded remaining faces earlier
      (nvec_to_zvec (irun_target run))) ->
  (forall run, DirectedRunMember target run ->
    StrippingSlice period excluded remaining faces later
      (nvec_to_zvec (irun_target run))) ->
  (forall i j left right,
    i < j -> j < length faces ->
    StrippingSlice period excluded remaining faces j left ->
    StrippingSlice period excluded remaining faces i right ->
    ~ SpecialLeafRelationZ system left right) ->
  earlier < length faces -> later < length faces ->
  DirectedIRunEdge source target -> earlier <= later.
```

## Safety witness and bottom SCC

`SafetyWitness` stores a semilinear safe set, a semilinear attractor included
in it, an occurrence-indexed finite list of directed initialized runs,
homogeneity within each SCC, and coverage of every valid initialized run
itself.  Coverage is not weakened to coverage of target vectors.

Vertices are `Fin.t (length nodes)`, so duplicate node values remain distinct
occurrences.  `finite_graph_bottom_scc_exists` proves a semantic bottom SCC in
Prop and does not require decidable edges or a computable SCC selector.

Inside a bottom SCC, homogeneity gives a common cone.  Lemma 3.13 is propagated
along graph paths in both directions to obtain `SameSet` equality of the
closed periods.  The representative period is therefore used extensionally;
predicate equality and functional extensionality are not used.

## Safe extension and Lemma 5.1

For a representative `w` of the bottom SCC, the construction uses:

- `I = A union Reach(S)`;
- `Y_Gamma`, the finite union of root translates by the common closed period;
- `T = A union (Y_Gamma intersection Phi)`.

The intersection with `Phi` is retained.  Lemma 7.2 absorbs attractor leaves,
expands reachable side leaves to initialized runs, and bottom-SCC closure keeps
all successor witness nodes inside Gamma.  This proves the first inclusion
needed by `lemma_5_1_bvas_safe_linearization`; the second follows from
`Y_Gamma subset Reach(S) + Q_Gamma`.

The selected safe-linearization offset is packaged together with the
face-stripping facts in `bottom_scc_face_stripping_with_extension`.  Thus the
proof cannot accidentally combine an attractor extension from one offset with
a stripping decomposition from another offset.

The resulting set `R` is not assumed semilinear.  Its intersection `X` with
the finitary cylindric set `Y_Gamma` is finitary cylindric, hence semilinear.
`A' = A union X` is a safe semilinear attractor.  Lemma 7.3 transports contact
around the SCC and establishes the backward-period-cover input
`Y_Gamma subset X - Q_Gamma` without truncated subtraction.

## Face stripping, residual bases, and replacement nodes

Task 11-D supplies the ordered face list, disjoint complete stripping slices,
the empty initial slice, the diagonal relation theorem, and strict dimension
decrease for every noninitial face.

For each noninitial face, `ResidualRunLe` is the conjunction of `IRunLe` and
the corresponding periodic order on targets.  `residual_run_wqo` obtains its
almost-fullness from the product of the initialized-run WPO and the finitary
period-order WPO.

The finite basis is produced by `restricted_af_finite_cover_classic`.  This
theorem performs induction on the almost-full proof and needs only
`Classical_Prop.classic`; it does not invoke `ClassicalEpsilon`, countable
choice, a membership oracle, or an executable basis selector.

Each basis run is paired with the face cone to form a new `DirectedIRun`.
Coverage retains both `IRunLe` and the exact target offset in the face period,
so the original run, rather than only its target, becomes a member of the new
node.

Lemma 7.5 rules out edges from a new node to a retained old node and proves
that face indices do not decrease.  Hence a new SCC contains nodes from one
face index only, while an old-only SCC inherits the original homogeneity.

## Rank descent

`bottom_scc_occurrence_partition` partitions the occurrence enumeration and
returns a `Permutation`; duplicate node values are therefore counted with
their original multiplicity.  Every removed bottom-SCC occurrence has the
representative rank.  Every replacement node has strictly smaller rank by the
proper-face dimension theorem and cone inclusion.  Counts above the removed
rank are unchanged, the removed-rank count strictly decreases, and arbitrary
growth at lower ranks is permitted.  The proof also covers rank zero: no
strictly lower-rank replacement can be added.

## Regression evidence

`SafetyWitnessExamples.v` contains kernel-checked concrete regressions for:

- dimension-zero rank order;
- high-dimension-first lexicographic comparison;
- rank decrease while lower-rank counts and total size increase;
- a one-vertex bottom SCC;
- empty and nonempty finite-vertex boundaries;
- duplicate occurrence preservation through the partition permutation.

The existing Task 11-A--11-D, IRun finite-cover, and bridge audits were rebuilt
as regressions.

## Axiom audit

`Print Assumptions lemma_7_1_safety_witness_rank_descent` reports exactly:

```text
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

The initially detected dependency on
`ClassicalEpsilon.constructive_indefinite_description` was removed by using
the AF-inductive finite-cover theorem above.  The target files contain no
`Axiom`, `Admitted`, `admit`, `Abort`, `ClassicalEpsilon`, `ClassicalChoice`,
choice oracle, UIP/K, `Eq_rect_eq`, functional extensionality, or disabled
kernel checks.

## Verification

- Focused `coqc` and focused `Makefile.coq` build: PASS.
- Task 11-A--11-D, IRun finite-cover, and bridge regressions: PASS.
- Forced complete `_CoqProject` rebuild: PASS.
- `make -f Makefile.coq validate`: PASS.
- Dependency-closure `coqchk -silent`: PASS.
- Prohibited-construct scan: PASS.
- Targeted `git diff --check` and staged diff check: PASS.
- Independent review after the concrete regression additions: PASS.

## Git

Branch: `work/mell-formalization`

Baseline: `1883371c6d1d81b9f99a91d0d9539f28a9c55069`

Final commit and HEAD are recorded in the completion report.  No push was
performed.  There are no unresolved Task 11-E proof obligations.
