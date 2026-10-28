# T10-E Task 6E3 — bounded-depth BVASS to VASS section audit

## Scope and baseline

- Branch: `work/mell-formalization`
- Baseline HEAD: `24e66261c1d83c561ed87a037512ca414d73aab3`
- Paper correspondence: Bizière–Leroux–Sutre, FoSSaCS 2026, Section 5, Lemma 11.
- Scope stops at Lemma 11. Theorem 12 and Corollary 14 are not implemented here.

## Implemented modules

- `theories/BVASS/VASSSection.v`
  - finite-initial VASS sections;
  - acceptance only at `visible ++ zero(auxiliary)`;
  - empty and initial sections;
  - disjoint binary and finite section union;
  - unary-rule reflexive-transitive closure.
- `theories/BVASS/BoundedVASSSection.v`
  - bounded-depth BVASS semantics;
  - sequential-copy rule-image compiler;
  - collect/transfer phase and signed final rule action;
  - branching-image finite union;
  - transparent recursive bounded-depth compiler;
  - Lemma 11 correctness theorem.
- `theories/Audit/BoundedVASSSectionExamples.v`
  - public API checks and assumption audit.

## VASS section contract

```coq
Record VASSSection (d q : nat) : Type := {
  section_aux_dimension : nat;
  section_state_count : nat;
  section_system : VAS (d + section_aux_dimension) section_state_count;
  section_initial_configs :
    list (Mell.VAS.StatefulVAS.SConfig
      (d + section_aux_dimension) section_state_count);
  section_accept_state : Fin.t q -> Fin.t section_state_count
}.

Definition VASSSectionReach {d q} (W : VASSSection d q)
    (state : Fin.t q) (counters : NVec d) : Prop :=
  exists initial_state initial_counters,
    List.In (initial_state, initial_counters) (section_initial_configs W) /\
    VASReach (section_system W)
      initial_state initial_counters
      (section_accept_state W state)
      (Vector.append counters
        (nvec_zero (section_aux_dimension W))).
```

The auxiliary suffix is constrained to zero before visible-coordinate
projection. It is not hidden by existential projection.

## Rule-image compiler

`compile_rule_image rule W` uses a sequential execution of independent copies
of `W`. Child occurrences are indexed by `Fin.t (rule_child_count rule)`, so
equal states and equal configurations retain their multiplicity. Each copy has
its own complete counter block. Phase transitions only initialize the next
unused block; later phases cannot mutate an earlier copy's internal auxiliary
coordinates.

After all copies have reached the required input states, transfer loops move
one visible unit at a time from each child block into the parent block. They
preserve

```text
parent + sum(child-visible)
```

and never touch child auxiliary coordinates. The final transition applies the
original signed action exactly once. Incomplete visible transfer or nonzero
copy auxiliary data leaves a nonzero auxiliary suffix and is rejected by the
section condition. No zero test and no integer-to-natural truncation is used.

The sequential construction denotes the same rule image as the paper's
asynchronous product: the blocks are disjoint, every child execution is parsed
back from its copy phase, and completeness orders the occurrence-preserving
RuleImage witness according to the rule input list.

Public correctness theorem:

```coq
Theorem compile_rule_image_correct : forall d q (rule : SRule d q)
    (W : VASSSection d q) state counters,
    VASSSectionReach (compile_rule_image rule W) state counters <->
    OrderedRuleImage rule (VASSSectionReach W) state counters.
```

Soundness splits an accepting execution at its first Collect phase, parses one
complete `W` execution for every child occurrence, freezes auxiliary suffixes,
and uses final zero to recover section membership. Completeness embeds each
child execution into its occurrence block, performs all transfers, then applies
the signed rule action.

## Finite union, unary closure, and recursion

The relevant public contracts are:

```coq
Theorem section_finite_union_reach_iff : forall d q sections state counters,
  VASSSectionReach (section_finite_union sections) state counters <->
  exists section, List.In section sections /\
    VASSSectionReach section state counters.

Theorem compile_unary_closure_reach_iff : forall d q (B : SBVAS d q)
    (W : VASSSection d q) state counters,
  VASSSectionReach (compile_unary_closure B W) state counters <->
  UnaryClosure B (VASSSectionReach W) state counters.
```

`compile_bounded_vass_section` is a transparent Gallina `Fixpoint` on `bound`.
At zero it closes the finite initial section under unary rules. At `S b` it
takes the finite union of the original initial section and all branching rule
images of the compiler at `b`, then applies unary closure. Thus initial
configurations remain present at every bound and a branching root adds exactly
one to branching depth.

The semantic decomposition used in the induction is:

```coq
Theorem reach_depth_decomposition : forall d q (B : SBVAS d q)
    bound state counters,
  ReachDepth B bound state counters <->
  UnaryClosure B (DepthSeed B bound) state counters.
```

## Lemma 11

```coq
Theorem bounded_vass_section_correct : forall d q (B : SBVAS d q) bound,
  BoundedSectionCorrect B bound (compile_bounded_vass_section B bound).

Theorem lemma_11_bounded_depth_vass_section :
  forall d q (B : SBVAS d q) bound state counters,
    VASSSectionReach (compile_bounded_vass_section B bound) state counters <->
    exists rho,
      ValidSRun B rho /\
      root_config rho = (state, counters) /\
      branching_depth rho <= bound.
```

The proof is constructive and does not use Task 6E2's noncomputable finite
basis. It is exactly the bounded-depth compiler required by FoSSaCS Lemma 11.

## Regression coverage

The general proofs cover dimension/state count zero, empty or multiple initial
configurations, no rules, arbitrary unary chains at depth zero, arity two and
higher, repeated child states/configurations, arbitrary child counters,
zero/negative rule actions, and bounds zero/successor. The vector block proofs
also cover `d = 0`, where the transfer-loop list is empty. Copy-state
classification, child-block projection, collect-mass preservation, frozen
auxiliary projections, final-zero recovery, and occurrence enumeration rule
out control/counter leakage and partial-transfer acceptance.

## Axiom audit

`Print Assumptions` reports `Closed under the global context` for:

- `compile_rule_image_complete`
- `compile_rule_image_sound`
- `compile_rule_image_correct`
- `rule_copy_prefix_parse`
- `reach_depth_decomposition`
- `bounded_vass_section_correct`
- `lemma_11_bounded_depth_vass_section`

An intermediate audit initially exposed `Eqdep.Eq_rect_eq.eq_rect_eq` from four
uses of `dependent induction`. Those proofs were replaced by ordinary induction
with explicit initial/final control-state equalities, and `Program.Equality`
was removed. The final public dependency closure is axiom-free. The targeted
scan found no `Axiom`, `Admitted`, `admit`, `Abort`, `ClassicalEpsilon`,
`ClassicalChoice`, UIP/K, `Eq_rect_eq`, functional extensionality, or oracle.

## Verification record

All commands exited 0 after the final source revision:

- `make check-t10-e3`
- `make audit-t10-e3` (focused build, public `Check`, assumptions, targeted
  `coqchk -silent`, prohibited-construct scan)
- `make audit-t10-e0 audit-t10-e1 audit-t10-e2 audit-bridges audit-t10-g`
- `opam exec --switch . -- make -f Makefile.coq clean`
- `opam exec --switch . -- make -f Makefile.coq -j2`
- `opam exec --switch . -- make -f Makefile.coq validate`

The forced full `_CoqProject` rebuild succeeded. Full `validate` completed
`coqchk -silent`; its repository-wide context summary lists axioms used by
older, unrelated modules, while the Task 6E3 theorems above are closed.

The whole-worktree `git diff --check` reports pre-existing trailing whitespace
in protected modified audit logs. Target-only and staged checks are used for
this task; those protected logs are neither modified nor staged.

## Independent review

A fresh read-only reviewer returned **PASS** with no major or moderate finding.
It independently checked the final-zero section condition, state/counter block
separation, occurrence multiplicity, copy execution recovery, transfer mass,
negative actions, both directions of RuleImage correctness, recursion
off-by-one behavior, initial preservation, transparency, and prohibited
dependencies. The only non-blocking observation was that the audit module is
contract/assumption oriented rather than a collection of concrete toy systems;
the corresponding edge cases are discharged uniformly by the structural
proofs.

## Remaining obligations

No Task 6E3 proof obligation remains. Task 6E4 must combine Task 6E2's uniform
bound with this compiler to prove Theorem 12, then use Task 6D for Corollary 14;
that work is deliberately outside this change.
