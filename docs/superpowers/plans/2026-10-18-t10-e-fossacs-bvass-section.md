# T10-E FoSSaCS BVASS Section Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove FoSSaCS 2026 Theorem 12 and Corollary 14 for the repository's stateful BVASS semantics.

**Architecture:** Use T09's genuine context-order finite basis to construct the paper's finite extension and bounded branching-depth representative.  Compile bounded-depth runs to a VASS section with explicit zero restrictions, then combine the exact section equality with T10-D and T10-A to obtain almost semilinearity.

**Tech Stack:** Coq 8.20.1, T09 stateful runs/context insertion, T10-G finite covers, T10-A closures, T10-D VAS theorem.

**Spec:** `docs/review/t10-planning-audit.md`

## Global Constraints

- Preserve `ContextOrder`; do not substitute `StrongSRunLe`, `OrderedDecorEmbed`, or `IRunLe` in Theorem 12.
- A section restricts auxiliary counters to zero before projection.
- The existence of the finite basis and final section is proof-only; do not claim an algorithm computing that basis.

## Review Focus

- Child permutations and duplicate child-state occurrences in `Extend`.
- Same target and exact counter equations in subtree replacement.
- Basis length zero versus the nonempty run universe used in `length basis - 1`.
- Branching depth zero and unary-only systems.
- Zero restriction on every auxiliary VASS counter before projection.

---

### Task 1: Extension and bounded-depth transformation

**Files:**
- Create: `theories/BVASS/VASSSection.v`
- Create: `theories/Audit/BVASSSectionStatements.v`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `ContextOrder`, `context_order_finite_cover`, context-family composition/effect lemmas.
- Produces: `Extend`, `branching_depth`, Proposition 5 interface, Lemma 8 replacement, Lemma 9 bounded-depth transformation.

- [ ] **Step 1: RED.** State Lemmas 8/9 and Theorem 12; record failure before `Extend` exists.
- [ ] **Step 2: Implement `Extend`.** Remove a finite multiset of reachable child configurations, preserving multiplicity and adding their counter sum to the rule delta.
- [ ] **Step 3: Reuse Proposition 5.** Connect existing context-family composition to both order comparisons and exact target-effect equality.
- [ ] **Step 4: Prove Lemma 8.** Preserve source/target states, `x_alpha+x_beta=x_sigma+x_beta'`, and run-size equality.
- [ ] **Step 5: Prove Lemma 9.** Formalize `R(alpha)`, strict decrease at branching nodes, same target, and depth `<= length basis - 1`.
- [ ] **Step 6: GREEN and commit.** Test reordered/duplicate children and commit the extension unit.

### Task 2: Bounded-depth VASS construction (Lemma 11)

**Files:**
- Modify: `theories/BVASS/VASSSection.v`
- Modify: `theories/Audit/BVASSSectionStatements.v`

**Interfaces:**
- Consumes: T10-D `VAS`, stateful BVASS rules.
- Produces: `VASSSection`, `VASSSectionReach`, `bounded_section`, exact Lemma 11 equality.

- [ ] **Step 1: RED.** Show that projection without zeroing auxiliary copies admits a false target.
- [ ] **Step 2: Implement section/finite-union VASS operations.** Prove state and counter-block disjointness.
- [ ] **Step 3: Implement the rule product/transfer construction.** Empty all copied counter blocks before the target state.
- [ ] **Step 4: Induct on branching depth.** Prove both directions of Lemma 11, including depth zero.
- [ ] **Step 5: GREEN and commit.** Run unary/binary/duplicate-state examples and commit.

### Task 3: Theorem 12 and Corollary 14

**Files:**
- Create: `theories/BVASS/AlmostSemilinear.v`
- Modify: `theories/BVASS/VASSSection.v`, `theories/Audit/BVASSSectionStatements.v`, `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: T10-G finite cover with unchanged type, Lemmas 9/11, T10-D forward theorem, T10-A closures.
- Produces: `VASSSectionOf`, `bvass_reach_is_vass_section`, `StatefulSemilinear`, `StatefulAlmostSemilinear`, `bvass_reach_inter_semilinear` exactly as audit §3.

- [ ] **Step 1: Prove Theorem 12.** Obtain a basis existentially, define `F`, `b`, and `Extend`, then compose same-target reachability with Lemma 11.
- [ ] **Step 2: Lift the semilinear restriction.** Intersect the VASS section with the lifted state/counter predicate before projecting.
- [ ] **Step 3: Apply T10-D and project.** Prove Corollary 14 without assuming section equality is decidable.
- [ ] **Step 4: Verify.** Run `make check-t10-e`, `make audit-t10-e`, module `coqchk`, full public `Check`, and `Print Assumptions`.
- [ ] **Step 5: Axiom gate.** Fail the audit if `ClassicalEpsilon.constructive_indefinite_description` occurs in either public theorem.
- [ ] **Step 6: Independent review.** Reviewer compares Definition 4, Proposition 5, Lemmas 8/9/11, Theorem 12, and Corollary 14 and checks R05 separation.
- [ ] **Step 7: Commit.** Commit only E files as `feat(t10-e): prove BVASS VASS-section theorem`.
