# Task 11-F Separator S Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove Theorem 3.3 (`separator_S`) and the finite-code singleton separation theorem from the completed Safety Witness rank-descent development.

**Architecture:** Keep Task 11-E immutable.  Add `Separator/Main.v` for initial/terminal witnesses and well-founded rank induction, then add `Separator/Singleton.v` for singleton-complement semilinearity and `SemiCode` extraction.  `Audit/SeparatorExamples.v` fixes the public contracts and boundary regressions before implementation.

**Tech Stack:** Coq 8.20.1, MathComp, existing Mell IBVAS/Semilinear/SafetyWitness APIs.

**Spec:** User-provided Task 11-F specification in this thread.

## Global Constraints

- Branch `work/mell-formalization`, baseline `82eab5b0c16bbe4b50023e5c5b2f959b5012c876`.
- Preserve Task 11-A--11-E public contracts and all unrelated tracked/untracked work.
- No `Axiom`, `Admitted`, `admit`, `Abort`, `ClassicalEpsilon`, `ClassicalChoice`, choice oracle, UIP/K, `Eq_rect_eq`, functional extensionality, or disabled kernel checks.
- The output is Prop-level existence, not an executable separator selector.
- Do not proceed to Task 12; do not push; stage only explicit Task 11-F files.

## Review Focus

- Dimension zero: the full orthant and singleton complement must work without a positive-coordinate assumption.
- Initial witness coverage must retain the actual initialized run, not merely its target.
- Terminal-witness closure must use both initial inclusion and the attractor condition.
- Rank induction must recurse on node lists without equating proof fields or selecting a successor function.
- `singleton_separator` must extract an actual `SemiCode` and transport both invariant obligations extensionally.

---

### Task 1: Initial Safety Witness

**Files:**
- Create: `theories/Separator/Main.v`
- Create: `theories/Audit/SeparatorExamples.v`

**Interfaces:**
- Consumes: `irun_le_finite_cover`, `DirectedIRun`, `DirectedRunMember`, `SafetyWitness`.
- Produces: `initial_safety_witness_exists`.

- [ ] Write `SeparatorExamples.v` checks for `initial_safety_witness_exists`, including a dimension-zero example.
- [ ] Compile the audit module and confirm RED because the theorem/module is absent.
- [ ] Define the finite full nonnegative orthant generator list and prove its generated-cone characterization.
- [ ] Map the valid-IRun finite cover to homogeneous directed nodes and prove actual-run coverage.
- [ ] Prove `initial_safety_witness_exists` and focused-compile `Main.v`.

### Task 2: Terminal Safety Witness

**Files:**
- Modify: `theories/Separator/Main.v`
- Modify: `theories/Audit/SeparatorExamples.v`

**Interfaces:**
- Consumes: `SafetyWitness`, `attractor_with_initials_inductive`, reach/IRun equivalence.
- Produces: `terminal_safety_witness_invariant`.

- [ ] Add a failing public-contract check and empty-node regression.
- [ ] Prove that empty witness nodes force every valid IRun target into the attractor.
- [ ] Derive initial inclusion using leaf runs, then derive `Closed` from the attractor bridge.
- [ ] Prove and focused-compile `terminal_safety_witness_invariant`.

### Task 3: Well-founded Witness Termination

**Files:**
- Modify: `theories/Separator/Main.v`
- Modify: `theories/Audit/SeparatorExamples.v`

**Interfaces:**
- Consumes: `witness_rank_less_well_founded`, `lemma_7_1_safety_witness_rank_descent`.
- Produces: `every_safety_witness_reaches_terminal`.

- [ ] Add a failing check for terminal-witness existence.
- [ ] Perform well-founded induction on `witness_nodes`; use the current witness for `[]` and Lemma 7.1 otherwise.
- [ ] Focused-compile and audit assumptions.

### Task 4: Theorem 3.3

**Files:**
- Modify: `theories/Separator/Main.v`
- Modify: `theories/Audit/SeparatorExamples.v`

**Interfaces:**
- Consumes: Tasks 1--3.
- Produces: `separator_S` with the exact public contract.

- [ ] Add the exact failing `Check separator_S` contract.
- [ ] Compose the initial witness, terminal witness, and terminal invariant theorem.
- [ ] Focused-compile and run `Print Assumptions separator_S`.

### Task 5: Singleton Complement and Finite Code

**Files:**
- Create: `theories/Separator/Singleton.v`
- Modify: `theories/Audit/SeparatorExamples.v`

**Interfaces:**
- Consumes: `separator_S`, `Semilinear`, `semilinear_complement`, `SemiCode`, `denote`.
- Produces: `singleton_complement_semilinear`, `singleton_separator`.

- [ ] Add failing checks for singleton complement and the exact `singleton_separator` type, including dimension zero.
- [ ] Prove singleton semilinearity with code `[(target, [])]`, then apply complement closure.
- [ ] Apply `separator_S` to `fun x => x <> target`, destruct its semilinear code witness, and transport `InitialIncluded`, `Closed`, and target exclusion.
- [ ] Focused-compile and run `Print Assumptions singleton_separator`.

### Task 6: Registration, Regression, Audit, and Commit

**Files:**
- Modify: `_CoqProject`
- Create: `docs/review/t11-f-separator-S-audit.md`

**Interfaces:**
- Consumes: all Task 11-F modules.
- Produces: registered build, audit evidence, local commit.

- [ ] Register `Main.v`, `Singleton.v`, and `SeparatorExamples.v`; regenerate `Makefile.coq` if required.
- [ ] Run Task 11-F focused build and Task 11-A--11-E, T09, T10-A/G, and invariant-checker regressions.
- [ ] Run forced full rebuild, `make -f Makefile.coq validate`, and dependency-closure `coqchk -silent`.
- [ ] Run public `Check`, `Print Assumptions`, prohibited-construct scan, targeted/staged diff checks.
- [ ] Complete the audit document and obtain a fresh independent review.
- [ ] Explicitly stage only Task 11-F files and create the local commit; do not push.
