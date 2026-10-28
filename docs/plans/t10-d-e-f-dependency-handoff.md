# T10-D/E/F dependency handoff after T10-C4

Date: 2026-10-23

Baseline audited: `2091260e2dd1f34bd02873093c912cb948b4b10d`

This document records dependencies only.  It does not implement T10-D, E,
or F and does not change their names or ordering.

## 1. Current boundary

T10-C now supplies the rational-cone, lattice, closed-linearization, center,
finite-face, integer H-representation, and complete face-stripping results,
including the same-list directional theorem
`face_stripping_theorem_diagonal`.

T10-G is also available concretely: `context_order_finite_cover` provides a
finite cover of valid stateful runs under the genuine `ContextOrder`.
Downstream T10-E must use this concrete theorem.  The older generic
`almost_full_finite_cover` has a different assumption history and is not a
replacement for the audited context-order theorem.

The existing decision layer remains conditional.  In particular,
`bvas_decide_of_separator` and `bvas_stage_eventual_of_separator` consume a
separator hypothesis; they do not prove the separation theorem.  Neither
BVAS reachability nor MELL provability is therefore unconditionally decided
at this checkpoint.

## 2. Dependency graph

```text
T10-A arithmetic/closure ----+
                              +--> T10-D Leroux VAS theorem --+
T10-C rational geometry -----+                              |
                                                            +--> T10-E BVASS section --+
T09/T10-G context cover ------------------------------------+                          |
                                                                                       +--> T11 separator --> BVAS decision --+
T10-C face stripping ------------------------------------------------------------------+                                      |
                                                                                                                              +--> T12 final MELL decision
T02 logic + T03/T09 BVAS semantics --> T10-F MELL-to-BVAS reduction ----------------------------------------------------------+
```

T10-D is the immediate prerequisite for the final stage of T10-E.  T10-F is
largely independent of D/E mathematically, but its final consequence still
requires an actual BVAS reachability decision theorem rather than the current
conditional driver.  T10-F does not feed the T11 separator proof; it joins
the chain only when the unconditional BVAS decision is composed with the
MELL-to-BVAS reduction in T12.

## 3. T10-D — Leroux VAS theorem

### First theorem/task

Begin the unchanged plan's Task 1: define finite-state unary `VAS`,
`VASRun`, `ValidVASRun`, `VASReach`, and the exact Jančar run order, then prove
the Lemma 4.1 WQO/minimality interface.  The first deliverable is the
RED/GREEN `theories/VAS/Runs.v` plus `theories/Audit/VASStatements.v` unit.

### Already available

- `NVec`, `ZVec`, signed displacement and nonnegativity infrastructure;
- T10-A semilinear products, intersections, unions, and projections;
- C1--C4 rational geometry, especially rational closed-cone finite
  generation, Gordan/lattice results, closed-linearization and center tools;
- Kruskal/Dickson adapters and the existing BVAS run-order experience.

### Missing types and bridges

- `VAS`, `VASRun`, `ValidVASRun`, `VASReach` with finite control states;
- Jančar order and its minimal-run finiteness;
- capacity/run transformers and intraproductions;
- finite production graphs and Kirchhoff functions;
- positive integer realization of rational circulations;
- `AlmostSemilinear` and the finite-control lift;
- final public results `vas_reach_relation_inter_semilinear` and
  `vas_post_inter_semilinear`.

### Major mathematical blocker/risk

Leroux 2012 Corollary 6.3 cannot be cited as an axiom.  The unchanged T10-D
contract requires its Sections 2--6 prerequisites, including minimal-run
decomposition and Kirchhoff soundness/completeness.  This is the largest
near-term proof chain.

### Independent work

Task 1 is independent of T10-E/F and can start immediately.  Transformer and
production-graph work follows it sequentially.

## 4. T10-E — FoSSaCS BVASS section theorem

### First theorem/task

Begin the unchanged Task 1 only after its interfaces are fixed: define
`Extend` and `branching_depth`, reuse the genuine `ContextOrder`, and prove
the Proposition 5/Lemmas 8--9 replacement and bounded-depth transformation
interfaces.

### Already available

- stateful `SBVAS`, `SRun`, `ValidSRun`, `SReach` and state erasure;
- `ContextOrder`, `context_order_wqo`, and
  `context_order_finite_cover` without a choice oracle in the concrete public
  theorem;
- C4's finite face-stripping and diagonal results for later Section 7 use;
- T10-A closure operations.

### Missing types and bridges

- `Extend`, branching depth, and exact same-target replacement;
- `VASSSection`, auxiliary-zero restriction, and bounded-section compiler;
- finite unions of VASS sections;
- `VASSSectionOf`, `bvass_reach_is_vass_section`;
- `StatefulSemilinear`, `StatefulAlmostSemilinear`, and
  `bvass_reach_inter_semilinear`;
- the bridge from proof-level finite context cover to the paper's bounded
  extension, without claiming an executable basis-selection algorithm;
- the final call to T10-D followed by restriction and projection.

### Major mathematical blocker/risk

The theorem must preserve child multiplicities/permutations and must zero all
auxiliary counters before projection.  Its final almost-semilinearity result
is blocked until T10-D is complete.  The concrete
`context_order_finite_cover`, not the generic finite-cover theorem, is the
approved finite-basis input.

### Independent work

The extension/replacement and bounded-depth portion can be developed before
T10-D.  The VASS-section type should be coordinated with T10-D's `VAS` API;
the final theorem cannot finish independently.

## 5. T10-F — MELL many-one reduction

### First theorem/task

Begin the unchanged Task 1: define the finite intuitionistic target calculus
and `kolmogorov`, prove the Fact 8 equivalence, and establish the cut-free
finite-subformula interface in `theories/Reduction/MELLToABVASS.v`.

### Already available

- T02 MELL syntax, `Provable`, cut bridge, and codecs;
- T03/T09 state-free and stateful BVAS semantics;
- `stateful_run_reach_iff` and `erase_states_correct`;
- semilinear/Presburger codecs where needed for audits.

### Missing types and bridges

- finite intuitionistic MELL syntax and cut-free subformula enumeration;
- fork-free BVASS with full zero tests and proof-search equivalence;
- the dimension-increasing first construction eliminating full zero tests;
- orientation into bottom-up stateful reachability;
- `ReachInstance`, `Holds`, `reduce_mell`, `reduce_mell_correct`;
- `reduce_mell_code`, `reduce_mell_code_correct`, and extraction audit.

### Major mathematical blocker/risk

The reduction must be a total Gallina function, not a proof-level choice.
The reverse zero-test simulation must preserve the destination state, frozen
old blocks, split additivity, and zero leaves.  Even after the reduction is
proved, unconditional MELL decidability still requires unconditional BVAS
reachability decidability; the existing separator-based driver is not that
theorem.

### Independent work

Tasks 1--3 are independent of T10-D/E and may be undertaken separately once
their fixed interfaces are respected.  Task 4 consumes existing state erasure
but not the C4 geometry directly.

## 6. Section 7 handoff

`face_stripping_theorem_diagonal` already gives, for its one existential face
list, the exact Lemma 7.5 ordering clause

```text
i < j -> not R(S_j, S_i).
```

No wrapper around the geometric theorem is currently justified.  The next
Section 7 layer must instead define and prove:

1. BVAS reachability as `QDiagonal` for the directed-irun period;
2. attractor safety as `NoBoundaryEdge`;
3. the directed-irun period/`FacePeriod` correspondence;
4. `FinitaryQCylindric`-to-`Semilinear` conversion for new nodes;
5. abstract graph, minimal run sets, and reachability preservation;
6. the rank bridge from `SpanDimension` and proper-face dimension decrease;
7. Lemma 7.5 and then the smaller-rank safety-witness construction of
   Lemma 7.1.

These are unimplemented interfaces, not defects in C4.

## 7. Recommended next minimum task

### Recommendation: T10-D Task 1 — VAS runs and Jančar order

This is the smallest coherent next task and lies on the critical dependency
path to T10-E.  It has a bounded file footprint, fixes the VAS interface that
E's section compiler must consume, and does not require reopening C4.

### Alternative A: T10-E Task 1

Pros: it can immediately exploit the completed `ContextOrder` finite cover
and develops a largely independent bounded-depth argument.

Cons: its later VASS-section construction must target T10-D's not-yet-fixed
`VAS` interface, so beginning here increases coordination and rework risk.

### Alternative B: T10-F Task 1

Pros: it is largely independent and advances the executable reduction.

Cons: it does not unblock T10-E or Section 7, and no unconditional decision
result follows until the missing separation/reachability theorem is proved.

Therefore the next instruction should authorize **only T10-D Task 1** with
the existing plan's public contracts unchanged.
