# T10-F MELL Many-One Reduction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a total Gallina many-one reduction from the repository's standard MELL provability predicate to state-free IBVAS reachability.

**Architecture:** Translate one-sided MELL to a cut-free intuitionistic multiplicative-exponential calculus, encode its finite subformula proof search as a fork-free stateful BVASS with full zero tests, eliminate tests using the dimension-increasing first construction of Lemma 3, orient the system bottom-up, and apply T09 fresh-gate state erasure.  Package the computed system and target as a dependent reachability instance with a codec.

**Tech Stack:** Coq 8.20.1, T02 logic/codecs, T03 BVAS semantics, T09 stateful semantics and erasure.

**Spec:** `docs/review/t10-planning-audit.md`

## Global Constraints

- `reduce_mell` is a Gallina function, not an existential witness or classical choice.
- Use Lemma 3's first many-one construction; never call the dimension-preserving Turing/oracle reduction.
- The source is standard MELL: no additives, fork rules, mix, or bounded exponentials.

## Review Focus

- Empty sequent, units, and promotion with non-`?` context.
- Repeated `!` formulas treated as set state versus linear formulas counted in counters.
- Correct zero-test transition `(i,q) -> (i+1,q')`.
- Split distribution with old blocks forced to zero at all leaves.
- Orientation of signed unary updates and every intermediate nonnegative configuration.

---

### Task 1: Kolmogorov translation and cut/subformula infrastructure

**Files:**
- Create: `theories/Reduction/MELLToABVASS.v`
- Create: `theories/Audit/ReductionStatements.v`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `formula`, `Derivation`, `Provable`, cut bridge from T02.
- Produces: finite intuitionistic MELL syntax/calculus, `kolmogorov`, Fact 8 equivalence, cut-free subformula theorem.

- [ ] **Step 1: RED.** State Fact 8 specialized to the exact T02 syntax and record missing declarations.
- [ ] **Step 2: Define the target calculus/translation.** Cover units, multiplicatives, and exponentials; prove dual/double-negation laws.
- [ ] **Step 3: Prove both directions.** Include the analogue of the paper's equation (6), cut use, exchange, and promotion contexts.
- [ ] **Step 4: Prove finite subformula closure.** Give decidable enumeration and membership completeness.
- [ ] **Step 5: GREEN and commit.** Run logical regressions and commit this unit.

### Task 2: Finite-subformula BVASS with full zero tests

**Files:**
- Modify: `theories/Reduction/MELLToABVASS.v`
- Modify: `theories/Audit/ReductionStatements.v`

**Interfaces:**
- Produces: fork-free `BVASS0` system, sequent/config encoding, Section 4.1.2 soundness/completeness, no-fork theorem.

- [ ] **Step 1: RED.** State the encoded reachability iff and no-fork property.
- [ ] **Step 2: Implement states/counters/rules.** Use support for `!` storage and multiplicities for linear subformulas; include finite intermediate states.
- [ ] **Step 3: Prove completeness by cut-free derivations.** Cover every MELL rule.
- [ ] **Step 4: Normalize store steps and prove soundness by run height.** Recover a legal proof for every system rule group.
- [ ] **Step 5: Prove fork-free.** The absence of additives must imply no fork constructor appears.
- [ ] **Step 6: GREEN and commit.** Test tensor splitting, contraction, weakening, and promotion.

### Task 3: Full-zero-test elimination (Lemma 3, first construction)

**Files:**
- Create: `theories/Reduction/ZeroTest.v`
- Modify: `theories/Audit/ReductionStatements.v`, `_CoqProject`

**Interfaces:**
- Consumes: fork-free BVASS0 reachability.
- Produces: `shorten_repeated_zero_state`, `zero_tests_per_branch_bound`, `remove_zero_tests`, forward/reverse simulation, dimension `|Q|*d`, fork-free preservation.

- [ ] **Step 1: RED.** Formalize a counterexample to the printed `(i+1,q)` destination when the source zero-test target is `q' <> q`.
- [ ] **Step 2: Prove shortening.** Remove repeated same-state zero configurations and derive at most `|Q|-1` tests per branch.
- [ ] **Step 3: Implement layered blocks.** Ordinary rules touch only the current block; a zero test moves `(i,q)` to `(i+1,q')` and freezes the old block.
- [ ] **Step 4: Prove forward simulation.** Embed each phase in its block.
- [ ] **Step 5: Prove reverse simulation.** Use nonnegativity, absence of old-block updates, split additivity, and zero old blocks at every leaf to recover zero at each original test.
- [ ] **Step 6: Prove fork-free preservation and total computability.** No oracle or reachability decision is used.
- [ ] **Step 7: GREEN and commit.** Run destination-state, multiple-test, split, and leaf-zero regressions.

### Task 4: Orientation, state erasure, packaging, and code-level many-one theorem

**Files:**
- Create: `theories/Reduction/Orientation.v`
- Create: `theories/Reduction/Main.v`
- Modify: `theories/Audit/ReductionStatements.v`, `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `stateful_run_reach_iff`, `erase_states_correct`, sequent codecs.
- Produces: `ReachInstance`, `Holds`, `reduce_mell`, `reduce_mell_correct`, instance codec, `reduce_mell_code`, `reduce_mell_code_correct`, `reduce_mell_many_one` with audit §3 types.

- [ ] **Step 1: RED.** Add exact final `Check` commands and record failure.
- [ ] **Step 2: Prove orientation equivalence.** Reverse top-down deductions to bottom-up stateful runs with signed deltas and intermediate nonnegativity intact.
- [ ] **Step 3: Compose fresh-gate erasure.** Apply the existing function/theorem directly and prove dimension/target typing.
- [ ] **Step 4: Define the total reduction and codec.** Do not destruct a proof-level existential to construct an instance.
- [ ] **Step 5: Prove typed and encoded correctness.** Valid sequent encodings map to exactly the encoded typed instance.
- [ ] **Step 6: Verify.** Run `make check-t10-f`, `make audit-t10-f`, module `coqchk`, complete types, and `Print Assumptions`.
- [ ] **Step 7: Extraction audit.** Extract `reduce_mell_code`; reject `AXIOM TO BE REALIZED`, `Obj.magic`, external calls, fixed-width integer overrides, or reachability oracles.
- [ ] **Step 8: Independent review.** Reviewer traces Proposition 7(2), Fact 8, Section 4.1.2, Lemma 3 first construction, orientation, and T09 erasure.
- [ ] **Step 9: Commit.** Commit only F files as `feat(t10-f): add executable MELL many-one reduction`.
