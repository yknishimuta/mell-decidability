# Task 11-E Safety Witness Rank Descent Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize Section 7 of Bizière--Leroux--Sutre through the kernel-checked rank-descent theorem for nonempty safety witnesses.

**Architecture:** Build a small Section 7 API on top of the existing free-run, directed-irun, safe-linearization, finite-basis, and face-stripping modules. Represent witness nodes by a list and graph vertices by list occurrences. Keep SCC and finite-basis choices in `Prop`; keep the witness coverage predicate over whole initialized runs. Define rank relationally from `SpanDimension`, avoiding any extraction of classical dimension witnesses into computation.

**Tech Stack:** Coq, project IBVAS/free-run APIs, Kruskal almost-full library, exact rational cone geometry, `Makefile.coq`, `coqchk`.

**Spec:** User-supplied Task 11-E specification and arXiv:2607.09558v1 Sections 3 and 7.

## Global constraints

- Preserve all Task 11-A--D public contracts.
- `SafetyWitness system Phi` includes the Section 3 ambient requirements that `Phi` is semilinear and contains `Reach system`; this preserves the requested assumption-free Lemma 7.1 type.
- Coverage is over every valid initialized run, not merely its target set.
- SCC vertices are list occurrences; no decidable equality on `DirectedIRun` is assumed.
- Rank compares the span dimension of each node's original directed cone, with highest dimensions dominant.
- No new axioms, admitted obligations, choice oracle, UIP/K, functional extensionality, or disabled kernel checks.

### Task 1: E1 foundations

**Files:**
- Create: `theories/Separator/Attractor.v`
- Create: `theories/Separator/FiniteGraph.v`
- Create: `theories/Separator/SafetyWitness.v`
- Create: `theories/Separator/RankDecrease.v`
- Create: `theories/Audit/SafetyWitnessExamples.v`

- [ ] Add failing public-contract checks in the audit module.
- [ ] Define attractors and prove the inductive-invariant bridges and Lemma 3.7.
- [ ] Define occurrence-indexed finite graphs, reachability, SCCs, and prove a nonempty bottom SCC exists without decidable edges.
- [ ] Define homogeneous safety witnesses with whole-run coverage.
- [ ] Define high-dimension-first rank comparison and prove well-foundedness.
- [ ] Focused compile and assumption audit.

### Task 2: E2 local Section 7 lemmas

**Files:**
- Modify: `theories/Separator/SafetyWitness.v`
- Create: `theories/Separator/WitnessUpdate.v`

- [ ] Prove marked-leaf substitution and Lemma 7.2.
- [ ] Prove Q-cylindric attractor contact propagation (Lemma 7.3).
- [ ] Prove directed-root rebasing and closed-period inclusion (Lemma 7.4).
- [ ] Focused compile and assumption audit.

### Task 3: E3 safe extension

**Files:**
- Modify: `theories/Separator/WitnessUpdate.v`

- [ ] Select a bottom SCC in `Prop` and derive its common cone/closed period.
- [ ] Construct `Y_Gamma`, `I`, and `T`, proving the exact semilinearity and inclusion obligations.
- [ ] Apply Lemma 5.1 and construct `R`, `X`, and the enlarged attractor.
- [ ] Prove contact, backward-period cover, diagonal special-leaf closure, and boundary exclusion.
- [ ] Focused compile and assumption audit.

### Task 4: E4 face stripping and finite bases

**Files:**
- Modify: `theories/Separator/WitnessUpdate.v`

- [ ] Apply Task 11-D's diagonal face-stripping package.
- [ ] Define each restricted run class and its product order.
- [ ] Use the existing countable finite-basis machinery to obtain genuine member bases.
- [ ] Build the face-directed node lists and updated occurrence-tagged witness list.
- [ ] Prove coverage of every residual initialized run.

### Task 5: E5 graph direction and homogeneity

**Files:**
- Modify: `theories/Separator/WitnessUpdate.v`

- [ ] Prove no edge from a new node to a retained old node.
- [ ] Prove face indices cannot decrease along new-node edges (Lemma 7.5).
- [ ] Classify updated SCCs and prove homogeneity.

### Task 6: E6 rank descent and Lemma 7.1

**Files:**
- Modify: `theories/Separator/RankDecrease.v`
- Modify: `theories/Separator/WitnessUpdate.v`

- [ ] Connect face dimensions to the removed SCC's original cone dimension.
- [ ] Prove higher rank coordinates unchanged and the removed coordinate strictly decreases.
- [ ] Assemble the new safety witness and prove `lemma_7_1_safety_witness_rank_descent`.
- [ ] Check exact public types and assumptions.

### Task 7: E7 verification and audit

**Files:**
- Modify: `_CoqProject`
- Modify: `Makefile`
- Complete: `theories/Audit/SafetyWitnessExamples.v`
- Create: `docs/review/t11-e-safety-witness-rank-decrease-audit.md`

- [ ] Run Task 11-E focused build and regressions for Tasks 11-A--D, T09, T10-C, and T10-G.
- [ ] Force a full `_CoqProject` rebuild, run `validate`, and run `coqchk -silent` over the dependency closure.
- [ ] Run public `Check`, `Print Assumptions`, forbidden-construct scans, and targeted/staged whitespace checks.
- [ ] Obtain an independent read-only review focused on run coverage, SCC homogeneity, face direction, and rank arithmetic.
- [ ] Stage only Task 11-E files and create the requested local commit; do not push.
