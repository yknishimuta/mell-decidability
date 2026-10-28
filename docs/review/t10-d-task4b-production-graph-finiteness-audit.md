# T10-D Task 4B audit: fixed-capacity production-graph finiteness

Baseline: `397b0c4596f7c85613f37fccadc7aa6fd3e034ad`.

Scope: Leroux (2012), Corollary 5.12 only.  No Kirchhoff relation,
Lemma 5.14/5.15, Corollary 5.16, or later T10 stage is implemented here.

## Representation

`BoundedMask d := Vector.t bool d`.  `MaskOfWitness h` records
`Nat.eqb (h[i]) 0`; for a `Lemma57Witness`, this is true exactly on the
bounded coordinates.  `all_bounded_masks d` recursively enumerates all
`2^d` Boolean vectors, including the unique dimension-zero mask.

`ProjectMask mask q` preserves true-mask coordinates and writes zero at the
others.  The proved identity

    ProjectBounded h q = ProjectMask (MaskOfWitness h) q

connects Task 4A's representation to the Boolean classification.  Thus two
Lemma 5.7 witnesses with the same mask give the same projection.  The common
root used across graphs is

    FixedSpecialState capacity mask := ProjectMask mask capacity.

The public theorem `production_graph_common_special_state` identifies every
Task 4A special state with this root when capacity and mask agree.

## Cross-graph determinism

`ProjectedActionTarget mask source action` computes the unique projected
successor: on selected coordinates it applies the signed VAS action using
`Z.to_nat`, and on other coordinates it is zero.  The truncating conversion
is not used to validate a step.  Instead, an existing
`ProductionGraphTransition` supplies the genuine `PlainVASStep`; the signed
step equation proves:

    projected_step_bounded_coordinate_equation
      target[i] = source[i] + action[i]       (over Z, mask[i] = true)

and both endpoints are zero when `mask[i] = false`.

Consequently:

    projected_step_deterministic_across_graphs :
      transition gamma1 h1 source action target1 ->
      transition gamma2 h2 source action target2 ->
      MaskOfWitness h1 = mask ->
      MaskOfWitness h2 = mask ->
      target1 = target2.

This deliberately requires the common mask.  Duplicate action-list positions
are irrelevant: labels are compared as actual `ZVec` values.

`ProjectedWordTrace` iterates this total successor.  Every graph path with
the matching mask has the computed target, and every common action-word prefix
has the same endpoint in every such graph
(`production_graph_word_prefix_deterministic_across_graphs`).  This is the
formal full-trace uniqueness: its state at every prefix is fixed.

## Simple paths and the uniform bound

`SimpleProductionGraphPath` is an existing Task 4A graph path together with
`NoDup` of its computed projected state trace.  Cycle removal is proved by
structural induction on paths.  If the new source already occurs in the
simplified tail trace, `production_graph_path_trace_suffix` discards the
cycle; otherwise the first edge is retained.

Corollary 5.10 therefore gives a simple path from the common special state to
every graph state.  Corollary 5.11 turns every such NoDup trace into a
`ForwardBad nvec_le` sequence.

The central general theorem is:

    finite_branching_af_bad_paths_bounded :
      af R ->
      forall alphabet next root,
      exists bound,
      forall word,
        Forall (fun a => In a alphabet) word ->
        ForwardBad R (FiniteBranchTrace next root word) ->
        length word <= bound.

Its proof is direct induction over the Prop-valued `af` derivation.  In the
`af_lift` case, the induction hypotheses give one bound per first action;
`finite_list_uniform_bound` takes their finite maximum.  No infinite path is
selected, so this is the finite-branching/König argument in an inductive AF
form and uses neither countable/dependent choice nor `ClassicalEpsilon`.

Instantiating it with Dickson's `nvec_le_almost_full`, the finite VAS action
list, the common special state, and `ProjectedActionTarget` proves:

    fixed_mask_simple_path_uniform_bound :
      forall d system capacity mask,
      exists bound,
      forall gamma witness word target,
        ValidProductionTriple system gamma ->
        GammaCapacity gamma = capacity ->
        Lemma57Witness system gamma witness ->
        MaskOfWitness witness = mask ->
        SimpleProductionGraphPath system gamma witness mask
          (FixedSpecialState capacity mask) target word ->
        length word <= bound.

This proof does not infer a uniform bound from the finiteness of each graph.

## Uniform universes and finite catalog

`words_up_to system bound` enumerates every action word of length at most the
uniform bound.  Word determinism maps these words to a finite common state
universe for one mask.  Finite induction over `all_bounded_masks d` combines
the universes:

    fixed_capacity_production_states_uniform_finite :
      forall d system capacity,
      exists states,
      forall gamma witness state,
        ValidProductionTriple system gamma ->
        GammaCapacity gamma = capacity ->
        Lemma57Witness system gamma witness ->
        ProductionGraphState system gamma witness state ->
        In state states.

The product `states × system × states` is the common finite edge universe:

    fixed_capacity_production_transitions_uniform_finite :
      forall d system capacity,
      exists edges,
      forall gamma witness source action target,
        ValidProductionTriple system gamma ->
        GammaCapacity gamma = capacity ->
        Lemma57Witness system gamma witness ->
        ProductionGraphTransition system gamma witness source action target ->
        In {| source; action; target |} edges.

`ProductionGraphSignature` contains a mask, state list, and transition list.
`GraphSignatureRepresents` requires the correct mask and special state and
pointwise iff characterizations of the actual Task 4A state and transition
predicates.  `list_powerset_select_predicate` selects exact predicate subsets
of the common universes in Prop.  The final theorem is:

    corollary_5_12_production_graph_class_finite :
      forall d system capacity,
      exists graph_catalog : list (ProductionGraphSignature d),
      forall gamma,
        ValidProductionTriple system gamma ->
        GammaCapacity gamma = capacity ->
        exists witness signature,
          Lemma57Witness system gamma witness /\
          In signature graph_catalog /\
          GraphSignatureRepresents signature system gamma witness.

The catalog is allowed to contain signatures that are not realized by a
production triple, exactly as the task contract permits.  It is a mathematical
finite existence result, not an executable graph-enumeration algorithm.
`graph_signature_witness_independent` transports representation between any
two correct Lemma 5.7 witnesses for the same gamma using Task 4A's witness
independence.

## Relation to Leroux Corollary 5.12

The formal proof follows the paper's argument: finitely many bounded-coordinate
sets; a shared projected capacity; deterministic finite branching by action;
simple paths are Dickson-bad; finite branching plus AF bounds their length;
therefore the union of all states and transitions at fixed capacity is finite,
and only finitely many graph subsets exist.

The formalization makes two implicit paper steps explicit:

1. step determinism is proved across different gammas only after fixing the
   mask;
2. graph-class finiteness is obtained from common universes, never from the
   mere individual finiteness established in Task 4A.

## Boundary regressions

`VASProductionGraphFinitenessExamples.v` checks the full public contracts and
formally covers the dimension-zero mask, both one-dimensional masks, an empty
action alphabet, duplicate action values, and the dimension-zero catalog.
The general theorems quantify over zero/nonzero capacity, zero/duplicate/mixed
actions, all-bounded/all-unbounded/mixed masks, and distinct witnesses and
graphs.  Task 4A's existing regression file continues to cover concrete graph
paths, strong connectivity, antichains, and individual graph finiteness.

The larger three-dimensional Examples 5.3/5.8 trace is not duplicated here:
its concrete projected graph belongs to Task 4A, while Task 4B's new obligation
is the uniform class argument above.

## Axiom and dependency audit

Fresh `Print Assumptions` results are recorded by
`audit-t10-d-task4b`.

- `projected_step_deterministic_across_graphs`: closed under the global
  context.
- `finite_branching_af_bad_paths_bounded`: closed under the global context.
- `fixed_mask_simple_path_uniform_bound`: depends only on
  `Classical_Prop.classic`, inherited through Task 4A Corollary 5.11.
- `fixed_capacity_production_states_uniform_finite` and
  `fixed_capacity_production_transitions_uniform_finite`: depend only on
  `Classical_Prop.classic` through the fixed-mask bound and finite Prop-level
  aggregation.
- `graph_signature_witness_independent`: depends only on
  `Classical_Prop.classic`, inherited from the Task 4A witness-independence
  results used to transport exact graph membership.
- `corollary_5_12_production_graph_class_finite`: depends only on
  `Classical_Prop.classic`, from finite Prop-valued subset selection and
  inherited Lemma 5.7/Task 4A results.

No `ClassicalEpsilon`, choice oracle, functional extensionality, UIP/K,
`Eq_rect_eq`, admitted proof, or mathematical axiom is introduced.

## Task 5 handoff

Kirchhoff work may consume a `ProductionGraphSignature` supplied by the final
catalog together with `GraphSignatureRepresents`.  It receives:

- an exact finite state list;
- an exact finite labeled-edge list;
- the correct fixed special state;
- witness-independent semantics;
- the Task 4A strong-connectivity and antichain theorems for the represented
  graph.

Task 5 must still define Kirchhoff functions/relations on this finite
interface, relate them to realizable cycles, and prove Leroux Lemmas 5.14–5.15
and Corollary 5.16.  None of those claims is made by Task 4B.
