# T10-E1: `Extend(B,F)` audit

Date: 2026-10-24

Branch: `work/mell-formalization`

Baseline: `337ffff93328f4f10e3aead8797eb27c0c92c1ae`

## Scope and source correspondence

This task formalizes only `Extend(B,F)` from Bizière–Leroux–Sutre,
*Bridging the Gap Between Plain VASS and Branching VASS*, FoSSaCS 2026,
Section 4, immediately after Lemma 8. Lemma 9's branching-depth argument is
not included.

The paper removes selected child occurrences from a rule and adds their
counter vectors to the signed action. `OmissionSelection` is an ordered,
occurrence-sensitive certificate for exactly that operation. It does not
deduplicate equal states or configurations, and an `F` configuration may be
used at more than one occurrence.

The existing `SRule` requires a nonempty input-state list. Consequently,
proper nonempty residuals become generated `SRule`s; a total omission becomes
an added initial configuration exactly when `zvec_to_nvec` accepts the shifted
signed action. No negative coordinate is truncated.

## Implementation

- `theories/BVASS/Extend.v`
- `theories/Audit/BVASSExtendExamples.v`
- `_CoqProject` registration
- focused Make targets `check-t10-e1` and `audit-t10-e1`

`enumerate_omissions` recursively takes the finite product of one keep choice
and every matching element of `F` at each input occurrence. The theorem
`enumerate_omissions_spec` proves both soundness and completeness.

`extend_bvass` retains all original initials and rules directly and appends all
generated initials and nonempty-residual rules. The membership theorems are:

```coq
extend_rule_membership_spec :
  forall d q (B : SBVAS d q) (available : list (SConfig d q))
    (generated : SRule d q),
  List.In generated (stateful_rules (extend_bvass B available)) <->
  List.In generated (stateful_rules B) \/
  exists original,
    List.In original (stateful_rules B) /\
    ExtendedRuleWitness available original generated

extend_initial_membership_spec :
  forall d q (B : SBVAS d q) (available : list (SConfig d q))
    (generated : SConfig d q),
  List.In generated (initial_configs (extend_bvass B available)) <->
  List.In generated (initial_configs B) \/
  exists original,
    List.In original (stateful_rules B) /\
    ExtendedInitialWitness available original generated
```

## Reach semantics

The forward direction reuses every original run unchanged. The reverse
direction is a mutual induction over `SReach` and `SReachChildren`. For each
generated rule it restores omitted occurrences with the reachability witnesses
for `F`, proves the original input-state permutation including multiplicity,
and uses `add_displacement_shifted_rule` to recover the original signed action.
Generated initials are the all-omitted instance of the same reconstruction.

```coq
extend_bvass_reach_iff :
  forall d q (B : SBVAS d q) (available : list (SConfig d q)),
  ReachableConfigurations B available ->
  forall state counters,
    SReach (extend_bvass B available) state counters <->
    SReach B state counters
```

The reachability premise is essential. The audit contains a BVASS with no
initial configurations and an unreachable unary child placed in `F`; its
extension gains an initial configuration, while `ReachableConfigurations`
is formally refuted.

## Lemma 9 preparation

```coq
extend_local_root_shortening :
  forall d q (B : SBVAS d q) available original retained omitted children result,
  List.In original (stateful_rules B) ->
  OmissionSelection available (input_states original) retained omitted ->
  ValidSRuns (extend_bvass B available) children ->
  Permutation (List.map fst (sruns_configs children)) retained ->
  add_displacement (rule_delta original)
    (List.map snd (sruns_configs children) ++ List.map snd omitted) = Some result ->
  exists shortened,
    ValidSRun (extend_bvass B available) shortened /\
    root_config shortened = (output_state original, result) /\
    RetainedChildrenOccurrence retained children shortened /\
    length retained + length omitted = length (input_states original) /\
    (ReachableConfigurations B available -> SReachChildren B omitted)
```

The retained `SRuns` value is used verbatim in the generated node, so duplicate
children and their occurrences are not collapsed. In the total-omission case
the shortened run is the generated leaf. `basis_root_configs_reachable` maps a
finite list of valid runs to a finite reachable `F` for Task 6E2.

## Regression coverage

The audit checks empty `F`, duplicated entries of `F`, no omission, partial and
total omission, three identical child states (eight positional choices), zero,
positive and negative signed actions, rejection of a negative all-omission
result, dimension zero, state count zero, the unreachable-`F` counterexample,
and a concrete total-omission local shortening.

## Assumptions and verification

`Print Assumptions extend_bvass_reach_iff` and
`Print Assumptions extend_local_root_shortening` both report:

```text
Closed under the global context
```

No new axiom, `Admitted`, `Abort`, `ClassicalEpsilon`, UIP/K, functional
extensionality, or selection oracle is used.

Verification completed before commit:

- focused Task 6E1 build and audit: PASS
- Task 6E0 regression and `coqchk`: PASS
- T09 bridge regression and `coqchk`: PASS
- T10-G concrete dependency audit: PASS; only `Classical_Prop.classic` remains
  in the concrete finite-cover theorems
- Task 6E1 `coqchk -silent`: PASS
- independent review: PASS after removal of an unnecessary
  ProofIrrelevance-dependent helper and expansion of boundary regressions
- forced full `_CoqProject` rebuild (`make -B -f Makefile.coq -j2`): PASS
- final source/cached diff checks and explicit staging audit: PASS

No Task 6E2 branching-depth theorem is implemented here.
