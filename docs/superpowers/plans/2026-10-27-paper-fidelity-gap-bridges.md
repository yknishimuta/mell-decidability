# Paper Fidelity GAP Bridges Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add kernel-checked, paper-strength public bridges for the six fidelity gaps recorded against arXiv:2607.09558v1.

**Architecture:** Reusable tree/list proofs live in two small BVAS helper modules.  A single Audit bridge module exposes the paper-shaped contracts by composing those helpers with existing geometry, WSVAS, attractor, and witness-update theorems; a separate Audit examples module owns boundary regressions.

**Tech Stack:** Coq 8.20.1, OCaml 4.14.2, existing Mell modules and MiniCooper dependency.

**Spec:** `docs/superpowers/specs/2026-10-27-paper-fidelity-gap-bridges-design.md`

**Execution status (2026-10-27):** Tasks 1--7 and the implementation and
verification portions of Task 8 are complete.  All checkboxes below are the
original pre-execution checklist; final independent-review and commit evidence
is recorded in the fidelity audit and local Git history.

## Global Constraints

- Branch `work/mell-formalization`, baseline `2190c6fbfbf523c77224e247884bcae001ddf3bc`.
- Preserve `docs/review/arxiv-2607.09558v1-fidelity-audit.md` and protected untracked `theories/Audit/FaceStrippingBasesExamples.v`.
- Preserve all existing public theorem and definition types.
- Do not introduce `Axiom`, `Admitted`, `ClassicalEpsilon`, `ClassicalChoice`, UIP/K, `Eq_rect_eq`, functional extensionality, or disabled kernel checks.
- Do not import Audit bridges into reduction, decision, or extraction paths.
- Stage only explicitly listed task files; never use `git add -A`; never push, tag, or release.

## Review Focus

- Ordered shuffle must preserve both input subsequence orders; test a noncommutative pair of singleton languages in Task 3.
- Duplicate equal-valued leaves must remain distinct occurrences; test unequal increments in Task 2.
- Mutual run embedding must not equate different child orders or different tree shapes; test negative examples in Task 4.
- Paper-attractor equivalence must allow zero side leaves and arbitrary predicates; test both directions in Task 5.
- Lemma 5.6 must expose no code or closure premise; `Check` its full type in Task 6.

---

### Task 1: Contract and module skeleton

**Files:**
- Create: `theories/Audit/PaperFidelityExamples.v`
- Modify: `_CoqProject`

**Interfaces:**
- Consumes: design contract table.
- Produces: failing `Check` statements for every intended public theorem.

- [ ] Add imports and `Check` statements naming all six missing public contracts.
- [ ] Run focused `coqc`; verify RED because the declarations do not exist.
- [ ] Register planned modules in dependency order in `_CoqProject`.

### Task 2: Simultaneous leaf increments (Fact 3.2)

**Files:**
- Create: `theories/BVAS/RunLeafOperations.v`
- Modify: `theories/Audit/PaperFidelityExamples.v`

**Interfaces:**
- Consumes: `IRun`, `IRuns`, `ValidFreeIRun`, `apply_action_frame_shift`.
- Produces: `fact_3_2_all_leaf_increments` and exact source/target equations.

- [ ] Add failing examples for two equal-valued leaves receiving different increments and dimension zero.
- [ ] Prove mutual structural lifting for runs/forests with an increment list of exactly the source length.
- [ ] Prove validity, pointwise source-word addition, target-sum, and preserved constructors/actions.
- [ ] Compile the helper and focused examples to GREEN.

### Task 3: Ordered-language flattening (Fact 3.6)

**Files:**
- Create: `theories/BVAS/LanguageFlattening.v`
- Modify: `theories/Audit/PaperFidelityExamples.v`

**Interfaces:**
- Consumes: exact free-run source words and structural finite substitution.
- Produces: `Language`, ordered `WordShuffle`, language star/plus/reach, and `fact_3_6_reach_shuffle_flatten`.

- [ ] Add failing checks for the paper contract, empty `K`/`L`, and an order-sensitive shuffle witness.
- [ ] Define ordered interleaving, finite concatenation closure, and reach from an exact source language.
- [ ] Prove finite run substitution preserving outer and inserted leaf order.
- [ ] Prove `Reach(K shuffle Reach(L)^+)` inclusion in `Reach(K shuffle L^+)` without choice or commutativity.
- [ ] Compile focused examples to GREEN.

### Task 4: IRun antisymmetry and Lemma 3.10

**Files:**
- Create: `theories/BVAS/RunOrderAntisymmetry.v`
- Modify: `theories/Audit/PaperFidelityExamples.v`

**Interfaces:**
- Consumes: `IRunEmbed`, `IRunsEmbed`, `IRunLe`, WQO and amalgamation.
- Produces: `irun_le_antisymmetric` and a paper-facing WPO/amalgamation package.

- [ ] Add failing antisymmetry check and negative examples for child reorder and different tree shape.
- [ ] Define mutual node counts and prove embedding never decreases count, strictly increases for `embed_below`.
- [ ] Prove equal-count embeddings are root embeddings and recurse positionwise.
- [ ] Combine mutual target inequalities with embedding equality to prove raw `IRun` equality.
- [ ] Package reflexivity, transitivity, antisymmetry, WQO, and exact amalgamation; compile to GREEN.
- [ ] If and only if a concrete counterexample is kernel-checked, replace this task with the faithful erased representation and relation-preservation contracts from the design.

### Task 5: Remark 2.2 and paper attractors

**Files:**
- Create: `theories/Audit/PaperFidelityBridges.v`
- Modify: `theories/Audit/PaperFidelityExamples.v`

**Interfaces:**
- Consumes: finite cone closure, Fact 3.6, existing `Attractor`, `SafetyWitness`, Lemma 7.1.
- Produces: `remark_2_2_full_iff_closed_linearization_fixed`, `PaperAttractor`, `paper_attractor_iff_attractor`, `PaperSafetyWitness`, and `paper_lemma_7_1_safety_witness_rank_descent`.

- [ ] Add failing full-type checks for all public contracts and counterexample guard for dropping finite generation.
- [ ] Prove finite rational cones are topologically closed and hence `QClosure (Cone P)` equals `Cone P`.
- [ ] Combine this with the existing linearization fixed-point theorem for Remark 2.2.
- [ ] Define `PaperAttractor` using ordered languages and prove both implications, including zero side leaves.
- [ ] Define field-preserving conversions between paper and internal safety witnesses.
- [ ] Apply existing Lemma 7.1 and convert its result back; compile to GREEN.

### Task 6: Paper-shaped Lemma 5.6

**Files:**
- Modify: `theories/Audit/PaperFidelityBridges.v`
- Modify: `theories/Audit/PaperFidelityExamples.v`

**Interfaces:**
- Consumes: `Semilinear`, `concrete_wsvas`, `lemma_5_6_bvas_wsvas_step_iff`.
- Produces: `paper_lemma_5_6_bvas_wsvas_exists` with only `Semilinear A` as its non-system premise.

- [ ] Add a failing `Check` that exposes the complete existential WSVAS contract.
- [ ] Define the set-parameterized side-step relation and prove agreement with the code-specific relation under denotation equivalence.
- [ ] Eliminate the `Semilinear A` witness inside `Prop`, choose the concrete WSVAS, and prove the pointwise iff.
- [ ] Verify no free code, closure, attractor, or decidability premise appears; compile to GREEN.

### Task 7: Fidelity report and focused assumption audit

**Files:**
- Modify: `docs/review/arxiv-2607.09558v1-fidelity-audit.md`
- Create: `docs/review/arxiv-2607.09558v1-fidelity-gap-closure.md`
- Modify: `theories/Audit/PaperFidelityExamples.v`

**Interfaces:**
- Consumes: all six public bridges.
- Produces: exact types, historical GAP-to-result ledger, and `Print Assumptions` evidence.

- [ ] Record complete public types, dependencies, assumptions, and before/after classifications without erasing the historical GAPs.
- [ ] Add `Check`/`Print Assumptions` commands for every new theorem and unchanged `separator_S`/`mell_decide` contracts.
- [ ] Run focused compilation and forbidden-construct scans.

### Task 8: Full verification, independent review, and commit

**Files:**
- Modify only files listed above and generated project metadata if required.

**Interfaces:**
- Consumes: completed bridge modules and report.
- Produces: repository-wide verification evidence and one local commit.

- [ ] Force the full `_CoqProject` rebuild and run `make -f Makefile.coq validate` plus dependency-closure `coqchk -silent`.
- [ ] Run `make check-final`, `make audit-final`, `make extract-final`, and the native runtime gate.
- [ ] Verify extraction dependency closure excludes Audit modules and existing public theorem types/assumptions are unchanged.
- [ ] Run forbidden-token scan, target-only `git diff --check`, and staged diff check.
- [ ] Obtain independent source-to-paper review; correct all Critical/Important findings and re-run affected tests.
- [ ] Explicitly stage only task files and create a local commit; do not push, tag, or release.
