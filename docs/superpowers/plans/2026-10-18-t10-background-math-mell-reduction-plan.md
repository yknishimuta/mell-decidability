# T10 Background Mathematics and MELL Reduction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the six T10 background-mathematics/reduction work groups without weakening their source theorems, after first removing the avoidable finite-cover choice dependency.

**Architecture:** T10 is split into seven independently reviewed plans: the six approved work groups A--F and prerequisite G for finite-cover axiom reduction. Shared mathematical predicates are fixed by the audit before implementation; A supplies closure interfaces, B/C supply periodic geometry, D supplies the VAS theorem, E composes T09 with D, and F is an independent executable reduction path.

**Tech Stack:** Coq 8.20.1, OCaml 4.14.2-flambda, MathComp/Coq-Polyhedra pins from T01, Coq-Kruskal Prop libraries, existing `Mell` modules and Make/coqchk audit workflow.

**Spec:** `docs/review/t10-planning-audit.md`

## Global Constraints

- Baseline is `510b71ad03a7d2fb12db9cb5f45efa891b6dc77a`.
- Preserve every T01--T09 public theorem, especially `context_order_wqo`, `irun_le_wqo`, and `erase_states_correct`.
- Do not introduce `Admitted`, a mathematical `Axiom`, an oracle, or a definition chosen only to make the target theorem tautological.
- The six contracts are the complete types in `docs/review/t10-planning-audit.md`; changes require a blocker report and approval.
- Do not touch or stage the 18 untracked files under `vendor/presburger/`.
- Each implementation task uses explicit `git add` paths and does not push.

## Review Focus

- Signed periodic sets crossing orthants: T10-B must restrict to `Q_s` before Dickson.
- Rational closure versus real closure, and subgroup `P-P` versus all of `Z^d`: T10-C tests both distinctions.
- Leroux Corollary 6.3 without its production/cycle prerequisites: T10-D rejects citation-only completion.
- Child permutation and duplicate-state multiplicity in BVASS extension/sections: T10-E reuses genuine `ContextOrder`.
- Zero-test destination `q'`, old counter blocks, and leaf zeroes: T10-F has reverse-simulation tests for each.

---

## Plans and dependency order

1. [T10-A arithmetic and set closure](2026-10-18-t10-a-arithmetic-set-closure.md)
2. [T10-G finite-cover axiom reduction](2026-10-18-t10-g-finite-cover-axiom-reduction.md)
3. [T10-B signed periodic order](2026-10-18-t10-b-signed-periodic-order.md)
4. [T10-C cone and lattice geometry](2026-10-18-t10-c-cone-lattice-geometry.md)
5. [T10-D Leroux VAS theorem](2026-10-18-t10-d-leroux-vas.md)
6. [T10-E FoSSaCS BVASS section](2026-10-18-t10-e-fossacs-bvass-section.md)
7. [T10-F MELL many-one reduction](2026-10-18-t10-f-mell-reduction.md)

T10-B and T10-F may run after their common interfaces are fixed.  T10-C
depends on A+B; D depends on A+C's definability interface; E depends on
A+D+G+T09.  F does not depend on D or E.

## Whole-T10 acceptance gate

- [ ] Each individual plan's RED evidence, GREEN suite, `coqchk`, exact public types, assumption log, extraction check where applicable, and independent source review are present.
- [ ] `git diff 510b71ad03a7d2fb12db9cb5f45efa891b6dc77a --name-only` contains only approved T10 implementation/audit files.
- [ ] `Print Assumptions` contains no unproved mathematical theorem.  Any remaining foundational principle is named, typed, and traced in the audit.
- [ ] T10-E does not regain `ClassicalEpsilon.constructive_indefinite_description` through either finite-cover theorem.
- [ ] T10-F extraction contains neither an axiom stub nor an oracle and implements a single total many-one map.
- [ ] Stop after T10 verification; do not begin T11.
