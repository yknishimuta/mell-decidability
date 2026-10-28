# T10-F MELL Many-One Reduction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct a transparent Gallina many-one reduction from the repository's ordinary cut-free MELL provability predicate to state-free IBVAS reachability, together with a correct natural-number encoding.

**Architecture:** Reuse YALLA's parametric negative translation and cut-free intuitionistic calculus for the MELL-to-ILZ bridge. Compile the finite subformula closure of the translated goal to a fork-free BVASS with full zero tests, eliminate tests using the dimension-increasing layered construction, orient deductions bottom-up, and reuse T09 state erasure. Package the resulting finite IBVAS and target as a dependent `ReachInstance` and codec.

**Tech Stack:** Coq 8.20.1, YALLA `nn_prop`/`ill_def`, MELL T02 syntax and codecs, BVAS T03 semantics and codecs, BVASS T09 state erasure.

**Spec:** `docs/review/t10-planning-audit.md` plus the Task 6F execution specification dated 2026-10-25.

## Global Constraints

- `reduce_mell` and every transformation it calls are transparent finite Gallina computations.
- Source logic is ordinary commutative propositional MELL: no additives, mix, arbitrary structural rules, lossy transitions, expansive transitions, forks, or coverability.
- Full zero tests are removed by the layered many-one construction, never the oracle/Turing reduction.
- The zero-test transition preserves the declared destination: `(i,q) -> (i+1,q')`.
- No new axiom, admitted proof, choice oracle, UIP/K, functional extensionality, or unchecked reachability decision procedure.
- Existing T02, T03, T09, Task 6D, and Task 6E public contracts remain unchanged.

## Review Focus

- A fresh negative-translation parameter must not change ordinary MELL provability or accidentally admit mix.
- Store normalization and promotion must exactly enforce the `!` support and full-zero condition.
- Frozen old layers must be zero at the simulated test, recovered from exact split conservation and zero leaves.
- Top-down signed unary updates must be negated exactly when oriented bottom-up.
- Instance codecs must preserve dependent dimensions and reject malformed codes without truncation.

---

### Task 1: Exact MELL-to-ILZ bridge and finite subformula closure

**Files:**
- Create: `theories/Reduction/ILZ.v`
- Create: `theories/Audit/MELLReductionExamples.v`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `formula`, `sequent`, `Provable`, `provable_yalla_iff`, YALLA `nn_prop` and cut-free `ill_ll`.
- Produces: `translate_mell`, `ILZProvable`, `mell_ilz_iff`, a duplicate-free finite subformula enumeration and its membership theorem.

- [x] **Step 1: RED.** Add `Check` statements and small executable examples for the desired translation/subformula API; focused compilation must fail on the missing declarations.
- [x] **Step 2: Implement the translation.** Choose a fresh negative-translation atom computed from the source sequent, instantiate YALLA's `trans`, and prove freshness/substitution lemmas.
- [x] **Step 3: Prove `mell_ilz_iff`.** Use `provable_yalla_iff`, `ll_ll_to_ill_trans`, and the reverse substitution/conservativity argument; audit empty sequents, units, exponentials, and absence of mix.
- [x] **Step 4: Implement finite subformula enumeration.** Prove soundness, completeness, duplicate freedom, decidable indexing, and closure under immediate subformulas.
- [x] **Step 5: GREEN.** Compile source and audit examples; run T02 logic/code regression.

### Task 2: Fork-free ILZ proof search as a BVASS with full zero tests

**Files:**
- Create: `theories/Reduction/MELLToABVASS.v`
- Modify: `theories/Audit/MELLReductionExamples.v`, `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: Task 1 translated formula and finite subformula indexing.
- Produces: finite `ZeroTestBVASS`, encoded sequents, `ilz_machine_correct`, `ilz_machine_fork_free`.

- [ ] **Step 1: RED.** State the machine correctness iff, promotion zero-test, store, multiplicity, and fork-free regression checks; verify missing-symbol failures.
- [ ] **Step 2: Define exact machine data and semantics.** Separate unary, split, and full-zero-test rules; define finite states for `!` support, optional RHS, rule intermediates, and the leaf state.
- [ ] **Step 3: Generate finite rules.** Specialize Figure 3 to the translated multiplicative-exponential subformula fragment; generate no additive or fork rule.
- [ ] **Step 4: Prove completeness.** Induct over cut-free ILZ derivations and simulate every reachable rule form.
- [ ] **Step 5: Prove soundness.** Normalize store steps and induct over machine deductions, reconstructing ILZ rules with exact counter multiplicities and promotion contexts.
- [ ] **Step 6: GREEN.** Compile and run identity, tensor, implication, unit, store, promotion, weakening, contraction, empty-RHS, and no-fork examples.

### Task 3: Exact full-zero-test elimination

**Files:**
- Create: `theories/Reduction/ZeroTest.v`
- Modify: `theories/Audit/MELLReductionExamples.v`, `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: Task 2 `ZeroTestBVASS` and fork-free reachability.
- Produces: `remove_zero_tests`, shortening and branch-bound theorems, exact forward/reverse reachability iff, fork-free preservation.

- [ ] **Step 1: RED.** Add the `q <> q'` destination regression and frozen-layer/leaf-zero checks; verify missing-symbol failures.
- [ ] **Step 2: Prove repeated-zero shortening.** Remove repeated `(state,0)` occurrences on a branch and derive at most `state_count - 1` tests for a minimal witness.
- [ ] **Step 3: Implement layered finite data.** Use `state_count * dimension` counters; ordinary rules update only the current layer, splits preserve every block, zero tests advance to their declared target state.
- [ ] **Step 4: Prove forward simulation.** Translate a shortened zero-test deduction to the layered system.
- [ ] **Step 5: Prove reverse simulation.** Establish old-block freezing and exact split conservation; use all-zero leaves to recover every tested block as zero.
- [ ] **Step 6: GREEN.** Compile and test zero, one, repeated tests, split distribution, state count 0/1, dimension 0, and fork-free preservation.

### Task 4: Orientation, state erasure, instance codec, and final reduction

**Files:**
- Create: `theories/Reduction/Orientation.v`
- Create: `theories/Reduction/Main.v`
- Modify: `theories/Audit/MELLReductionExamples.v`, `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: Task 3 ordinary finite-control BVASS, `erase_states`, `erase_states_correct`, and T02/T03 codecs.
- Produces: `ReachInstance`, `Holds`, `reduce_mell`, `reduce_mell_correct`, `encode_reach_instance`, `decode_reach_instance`, `reduce_mell_code`, `reduce_mell_code_correct`, `encoded_reachability`, `reduce_mell_many_one`.

- [ ] **Step 1: RED.** Add exact final public `Check` statements, malformed-code behavior, and representative source sequents; verify focused failure.
- [ ] **Step 2: Prove orientation correctness.** Convert zero-leaf top-down unary/split deductions to bottom-up `SBVAS`, negate unary actions, preserve nonnegativity and child multiplicities.
- [ ] **Step 3: Compose state erasure.** Reuse `erase_states_correct` with the computed root state and zero vector; do not reimplement fresh gates.
- [ ] **Step 4: Define `ReachInstance` and `reduce_mell`.** Compose only transparent functions from Tasks 1–3 and T09.
- [ ] **Step 5: Implement the dependent codec.** Encode dimensions, finite systems, actions, and targets; prove decoder round trips and malformed-code rejection.
- [ ] **Step 6: Prove typed and encoded correctness.** Establish `reduce_mell_correct`, `reduce_mell_code_correct`, and `reduce_mell_many_one` by composing the stage equivalences.
- [ ] **Step 7: GREEN and extraction audit.** Focused compile, T02/T03/T05/T09 regressions, extraction of `reduce_mell_code`, and scan for runtime axioms/oracles.

### Task 5: Whole-project verification, audit, and commit

**Files:**
- Create: `docs/review/t10-f-mell-to-bvas-reduction-audit.md`
- Modify: `Makefile`, `_CoqProject`

**Interfaces:**
- Consumes: all four implementation tasks.
- Produces: reproducible verification record and one local Task 6F commit.

- [ ] **Step 1: Run all public `Check`, `Print Assumptions`, and dependency audits.** Local construction lemmas and final reduction should be closed unless an existing T02 dependency is reported explicitly.
- [ ] **Step 2: Run focused and prerequisite regressions.** Include T02, T03, T05, T09, and all Task 6F examples.
- [ ] **Step 3: Force the full `_CoqProject` rebuild, `validate`, and `coqchk -silent`.** Record commands and exit codes.
- [ ] **Step 4: Scan prohibited constructs and inspect target-only diffs.** Include untracked files before staging and cached diff checks after explicit staging.
- [ ] **Step 5: Obtain a fresh independent review.** Trace Fact 8, Claim 9.1, Lemma 3, orientation, erasure, executable construction, and codec correctness.
- [ ] **Step 6: Commit only Task 6F files.** Do not stage protected logs, `FaceStrippingBasesExamples.v`, `vendor/presburger/`, or unrelated plans; do not push.

## Self-review

- Coverage: all F0–F4 checkpoints, public contracts, extraction, regressions, and audit obligations are assigned.
- Type flow: translated formula and subformula indices feed the zero-test machine; its layered output feeds orientation; the resulting `SBVAS` feeds the existing T09 erasure; codecs package the exact dependent dimension.
- Failure cases: empty/mix-sensitive sequents, illegal promotion, duplicate exponential formulas, `q/q'`, frozen nonzero blocks, sign reversal, and malformed codes all have explicit tests.
- Scope: no Task 11/12 implementation and no second reduction route.
