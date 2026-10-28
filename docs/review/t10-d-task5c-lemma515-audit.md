# T10-D Task 5C audit — Leroux Lemma 5.15

## Scope and baseline

- Repository: `mell-formalization`
- Branch: `work/mell-formalization`
- Baseline: `34fd02825ff58d21732620fdcdc09d397b3e4524`
- Scope: Leroux (2012), Lemma 5.15 only. Corollary 5.16 is not proved here.

The implementation keeps the `Lemma57Witness` and the exact `NoDup` edge
list extracted from one `ProductionKirchhoffRelation` witness fixed throughout
the proof. It never identifies an arbitrary graph cycle with a VAS run.

## Public interface

```coq
Definition CapacityTransformerCone {d} (system : PlainVAS d)
    (capacity : NVec d) : QVec d -> QVec d -> Prop :=
  RationalRelationCone
    (NRelationAsZ (CapacityTransformer system capacity)).
```

```coq
Lemma intraproduction_split_runs : forall d system gamma witness,
  IntraProduction system gamma witness ->
  exists multiplier,
    PlainVASReach system
      (nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaInput gamma)))
      (nvec_add (GammaCapacity gamma) witness) /\
    PlainVASReach system
      (nvec_add (GammaCapacity gamma) witness)
      (nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaOutput gamma))).
```

`positive_rational_kirchhoff_uniform_scaling` returns one positive natural
scale, natural endpoint vectors, and a natural edge-weight function.  Its
conclusion simultaneously records the two `QVecEq` clearing equations,
endpoint domination of the intraproduction contribution, natural Kirchhoff
balance, strict domination of the removed edge counts, and the scaled
endpoint-displacement equation.

```coq
Lemma positive_residual_kirchhoff : forall d edges total removed
    input output removed_input removed_output,
  KirchhoffBalanceNat edges total ->
  KirchhoffBalanceNat edges removed ->
  (forall edge, List.In edge edges -> removed edge < total edge) ->
  nvec_le removed_input input ->
  nvec_le removed_output output ->
  nvec_to_zvec output =
    zvec_add (nvec_to_zvec input)
      (KirchhoffDisplacementNat edges total) ->
  nvec_to_zvec removed_output =
    zvec_add (nvec_to_zvec removed_input)
      (KirchhoffDisplacementNat edges removed) ->
  let residual_input := nvec_sub input removed_input in
  let residual_output := nvec_sub output removed_output in
  let residual_weight := fun edge => total edge - removed edge in
  KirchhoffBalanceNat edges residual_weight /\
  (forall edge, List.In edge edges -> 0 < residual_weight edge) /\
  nvec_to_zvec residual_output =
    zvec_add (nvec_to_zvec residual_input)
      (KirchhoffDisplacementNat edges residual_weight).
```

```coq
Theorem production_graph_cycle_realizable_after_pumping : forall d system
    gamma witness trace,
  ValidProductionTriple system gamma ->
  Lemma57Witness system gamma witness ->
  ProductionGraphEdgeTrace system gamma witness
    (ProductionGraphSpecialState gamma witness)
    (ProductionGraphSpecialState gamma witness) trace ->
  exists multiplier run,
    0 < multiplier /\
    ValidVASRun system run /\
    RunSource run = nvec_add (GammaCapacity gamma)
      (nvec_scale multiplier witness) /\
    RunActionWord run = GraphTraceActionWord trace /\
    nvec_to_zvec (RunTarget run) =
      zvec_add
        (nvec_to_zvec (nvec_add (GammaCapacity gamma)
          (nvec_scale multiplier witness)))
        (ActionDisplacement (GraphTraceActionWord trace)).
```

```coq
Lemma pumped_graph_cycle_iterated_run : forall d system base input output
    run coefficient,
  ValidVASRun system run ->
  RunSource run = base ->
  nvec_to_zvec (RunTarget run) =
    zvec_add (nvec_to_zvec base)
      (ActionDisplacement (RunActionWord run)) ->
  nvec_to_zvec output =
    zvec_add (nvec_to_zvec input)
      (ActionDisplacement (RunActionWord run)) ->
  exists iterated,
    ValidVASRun system iterated /\
    RunSource iterated = nvec_add base (nvec_scale coefficient input) /\
    RunTarget iterated = nvec_add base (nvec_scale coefficient output) /\
    RunActionWord iterated =
      RepeatActionWord coefficient (RunActionWord run).
```

```coq
Theorem lemma_5_15_kirchhoff_in_capacity_cone : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d)
    (input output : QVec d),
  ValidProductionTriple system gamma ->
  ProductionKirchhoffRelation system gamma input output ->
  CapacityTransformerCone system (GammaCapacity gamma) input output.
```

## Proof audit

1. The witness intraproduction is split with a common multiplier `n`; its two
   reaches are concatenated and projected to a special-state graph cycle.
2. The rational endpoint and strictly positive rational edge weights are
   cleared with a common scale `k`, then multiplied by a finite `boost` so that
   both endpoint lower bounds and every strict edge bound hold at once.
3. Natural subtraction is used only after the corresponding `nvec_le` or
   strict edge inequality has been proved.  The residual `g` is balanced,
   strictly positive on every exact graph edge, and has displacement `V'-U'`.
4. Task 5A's Euler theorem realizes `g` exactly as a special-state graph
   cycle.  This is still only a graph cycle at this point.
5. Prefix safety is proved separately.  On bounded coordinates the projected
   step equation gives the required credit bound.  On unbounded coordinates
   the Lemma 5.7 witness is positive, and `S (nvec_norm required_credit)` is a
   uniform pumping multiplier.  The resulting run preserves the exact graph
   action word.
6. `pumped_graph_cycle_iterated_run` constructs an actual concatenated run and
   records that its action word is exactly the original word repeated `m`
   times.
7. The two powered intraproduction halves surround that repeated residual
   run, yielding a capacity-transformer witness between `mU` and `mV`.
8. Since `U = k*u` and `V = k*v`, the final positive cone multiplier is
   explicitly `m*k`, not either multiplier alone.

This is precisely the inclusion `R_gamma subseteq Q_{≥0} T_c`; the reverse
inclusion and finite union of Corollary 5.16 are deliberately absent.

## Boundary coverage

- Dimension zero and empty-word credit: explicit regression.
- Exact zero/successor repetition of action words: explicit regression.
- Empty trace, zero displacement, bounded-only, unbounded-only, and mixed
  coordinates: covered by the general prefix-credit theorem without positive
  dimension or nonempty-word assumptions.
- Different rational denominators and simultaneous strict edge bounds:
  covered by the common denominator plus finite boost construction.
- Strict residual positivity and subtraction safety: explicit hypotheses and
  conclusions of `positive_residual_kirchhoff`.
- A graph cycle that is not executable at bare capacity is not lifted there;
  the run starts at `c + m*h`.

## Verification and assumptions

`make audit-t10-d-task5c` performs the focused source/regression build,
complete public `Check` output, `Print Assumptions`, `coqchk -silent`, and the
forbidden-construction scans.

- `positive_rational_kirchhoff_uniform_scaling`: closed.
- `positive_residual_kirchhoff`: closed.
- `production_graph_cycle_realizable_after_pumping`: closed.
- `pumped_graph_cycle_iterated_run`: closed.
- `pumped_graph_cycle_iterated`: closed.
- `lemma_5_15_kirchhoff_in_capacity_cone`: depends only on
  `Classical_Prop.classic`, inherited through the pre-existing exact finite
  graph/witness and Euler infrastructure.

No `Admitted`, `admit`, `Abort`, new `Axiom`, `ClassicalEpsilon`, choice
oracle, UIP/K, `Eq_rect_eq`, or functional extensionality occurs in the Task
5C files.

Independent review result: PASS; no Critical or Important issue.  The review
specifically checked fixed graph witnesses, the `k`/`m` distinction, residual
strict positivity, prefix safety, exact repeated words, endpoint joins, and
the final inclusion direction.

## Task 5D handoff

Corollary 5.16 still requires the converse cone inclusion, application of
Lemma 5.14 to scaled transformer pairs, and a finite classification that keeps
three independent pieces of information: production-graph signature, input
positive-support mask, and output positive-support mask.  Graph-catalog
finiteness alone does not identify all `R_gamma` relations.
