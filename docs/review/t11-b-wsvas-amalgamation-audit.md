# Task 11-B — WSVAS amalgamation and BVAS simulation audit

Date: 2026-10-25
Branch: `work/mell-formalization`
Baseline: `8584be77162520a856884332561b2fb3dadabcfa`

## Scope and source correspondence

This change formalizes Sections 5.1–5.2 and Appendix C of Bizière–Leroux–Sutre, arXiv:2607.09558v1.  It does not implement Task 11-C.

- `WSVAS/System.v`: abstract WSVAS transition quasi-order, almost-full/WQO witness, signed action monotonicity, and the exact action diamond.
- `WSVAS/Runs.v`: zero-or-more-transition runs, signed-step validity, source/target/direction, concatenation, shift, and reflexive-transitive reachability.
- `WSVAS/RunOrder.v`: operational gap decomposition, both-endpoint direction order, Higman encoding, Lemma C.1, and Corollary C.2.
- `WSVAS/Amalgamation.v`: Corollary C.3 stitching, Lemma C.4, Lemma 5.2, and Corollary 5.3.
- `WSVAS/WitnessAlphabet.v`: evidence-bearing alphabet, concrete WSVAS, and Lemma 5.6.
- `WSVAS/BVASSimulation.v`: free BVAS runs, occurrence-preserving source words, marked main paths, and Lemma 5.5.

## Abstract WSVAS and run order

`WSVAS d` stores a transition type, a reflexive/transitive relation, an almost-full proof, a map to `ZVec d`, coordinatewise monotonicity, and:

```coq
forall root left right,
  root <= left -> root <= right ->
  exists merged,
    left <= merged /\ right <= merged /\
    delta root + delta merged = delta left + delta right.
```

`WSRun` admits the empty transition list.  `ValidWSRun` checks every signed transition through `step_target`; all intermediate configurations therefore remain natural vectors.  Shifting adds a nonnegative vector to every configuration and leaves the transition sequence unchanged.

`WSRunOrder` is the Appendix C gap decomposition.  Every gap is bounded below at both its source and target.  The public characterization is:

```coq
lemma_c_1_wsrun_order_iff_higman :
  forall system left right,
    WSRunOrder system left right <->
    WSDirectionLe system left right /\
    WSHigmanEmbed system left right.
```

The explicit `WSDirectionLe` conjunct is essential when the encoded transition word is empty.  Corollary C.2 uses Dickson/product/Higman almost-full closure; it does not assume a finite or decidable transition alphabet.

## Exact amalgamation

The public Lemma C.4 is:

```coq
lemma_c_4_wsrun_exact_amalgamation :
  forall system root alpha beta,
    ValidWSRun root -> ValidWSRun alpha -> ValidWSRun beta ->
    WSRunOrder system root alpha ->
    WSRunOrder system root beta ->
    exists merged,
      ValidWSRun merged /\
      WSRunOrder system alpha merged /\
      WSRunOrder system beta merged /\
      nvec_add (ws_source root) (ws_source merged) =
        nvec_add (ws_source alpha) (ws_source beta) /\
      nvec_add (ws_target root) (ws_target merged) =
        nvec_add (ws_target alpha) (ws_target beta).
```

The proof amalgamates every pair of gaps by witnessed nonnegative shifts, uses the WSVAS exact diamond at every matched transition, and stitches the resulting pieces.  The zero-transition case is the base gap amalgamation, not an omitted special case.  No truncated subtraction is used in the theorem statement or construction.

`lemma_5_2_wsvas_runs_wqo_amalgamation` packages Corollary C.2 and Lemma C.4.  Positive scaling is exposed without vector subtraction:

```coq
corollary_5_3_wsvas_run_scaling :
  forall system root run factor,
    ValidWSRun root -> ValidWSRun run ->
    WSRunOrder system root run -> 1 <= factor ->
    exists scaled,
      ValidWSRun scaled /\ WSRunOrder system run scaled /\
      (factor - 1) * src(root) + src(scaled) = factor * src(run) /\
      (factor - 1) * tgt(root) + tgt(scaled) = factor * tgt(run).
```

## Witness alphabet and Lemma 5.6

`WitnessAlphabet S code` is a disjoint sum of:

1. a valid initialized run, ordered by `IRunLe`; and
2. an explicit semilinear-component index with its coefficient vector, ordered only within the same component.

Thus equal values with different run proofs, witness kinds, or component indices remain distinct.  Fixed-length vectors retain side-child positions and multiplicity.  Run witnesses use initialized-run amalgamation; component witnesses add coefficient offsets.  Both `witness_alphabet_wqo` and `witness_alphabet_diamond` are closed under the global context.

The independent review initially found that `BVASSideStep` merely repackaged the concrete WSVAS transition.  This was corrected.  Its final definition is the semantic BVAS relation:

```coq
exists rule_index side_values,
  length side_values = pred (arity rule) /\
  Forall (fun x => Reach S x \/ denote code x) side_values /\
  apply_action rule (source :: side_values) = Some target.
```

The public theorem is:

```coq
lemma_5_6_bvas_wsvas_step_iff :
  forall S code source target,
    BVASSideStep S code source target <->
    WSVASStep (concrete_wsvas S code) source target.
```

Forward completeness constructs an occurrence-preserving vector of witnesses.  Reverse soundness recovers its ordered value list and the exact `apply_action` equation.  Negative actions are accepted only when `apply_action` returns a natural target.  Lemma 5.6 has no invariant-closure hypothesis.

## Source words and Lemma 5.5

`ValidFreeIRun` permits arbitrary leaves but retains the original IBVAS internal rules.  `free_irun_sources` lists leaf configurations in occurrence order.  `SourceShuffle X I word` explicitly splits the word as `prefix ++ special :: suffix`, with one designated `X` occurrence and all other occurrences in `I`; it does not identify the special leaf by value subtraction.

The constructive mutual induction

```coq
marked_free_irun_iff_source_shuffle :
  MarkedFreeIRun S X I run <->
  ValidFreeIRun S run /\ SourceShuffle X I (free_irun_sources run)
```

proves exact equivalence between the list semantics and a structural main path, including equal-valued duplicate leaves and the case where the special value also belongs to `I`.

The public Lemma 5.5 is:

```coq
lemma_5_5_bvas_wsvas_reach_iff :
  forall S code X target,
    ClosedUnderFreeRuns S (SimulationInvariant S code) ->
    ReachFromShuffle S X (SimulationInvariant S code) target <->
    exists source,
      X source /\
      WSVASStepStar (concrete_wsvas S code) source target.
```

Only Lemma 5.5 assumes closure of `I = Reach(S) union denote(code)`: it is used to collapse off-main-path subtrees.  Reverse construction attaches the semantic side configurations as distinct leaf occurrences.

## Verification

- Focused build of all six WSVAS modules and `WSVASExamples.v`: PASS.
- T06/T09 regressions (`RepairExamples`, `BridgeExamples`): PASS.
- T10-A–C regression targets and Task 11-A `SeparatorPeriodGeometryExamples`: PASS.
- Forced full `_CoqProject` rebuild: PASS.
- `make -f Makefile.coq validate` / full dependency-closure `coqchk -silent`: PASS.
- Task 11-B public `Check` and `Print Assumptions`: PASS.
- `lemma_c_4_wsrun_exact_amalgamation`, Corollary 5.3, witness WQO/diamond, Lemmas 5.6 and 5.5, and source-word equivalence: `Closed under the global context`.
- Prohibited-construct scan over Task 11-B sources: PASS.
- `git diff --check` and staged diff check: recorded at commit time.

The full project closure reports pre-existing library/global axioms (including classical and proof-irrelevance facilities in external dependencies).  None is used by the Task 11-B public theorems above, as confirmed by their individual `Print Assumptions` results.

## Independent review

An independent read-only review checked zero runs, endpoint direction, Higman empty words, exact source/target equations, transition diamonds, scaling, witness tags and multiplicity, signed actions, source occurrences, and the placement of the closure hypothesis.  Its initial material Lemma 5.6 contract finding was fixed and re-reviewed.  Final result: PASS, no material findings.

## Changed files

- `_CoqProject`
- `theories/WSVAS/System.v`
- `theories/WSVAS/Runs.v`
- `theories/WSVAS/RunOrder.v`
- `theories/WSVAS/Amalgamation.v`
- `theories/WSVAS/WitnessAlphabet.v`
- `theories/WSVAS/BVASSimulation.v`
- `theories/Audit/WSVASExamples.v`
- `docs/superpowers/plans/2026-10-25-t11-b-wsvas.md`
- `docs/review/t11-b-wsvas-amalgamation-audit.md`

No Task 11-C work is included.  Final commit information is added by the completion report.
