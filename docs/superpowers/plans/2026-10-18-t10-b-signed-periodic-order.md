# T10-B Signed Periodic Order Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove Appendix A's finite-generation/WQO characterization for signed periodic sets with the R11 orthant restriction.

**Architecture:** Define finite generation and the difference preorder on `ZVec`.  Partition by a finite sign pattern, transport each part by sign flip, restrict to `Q_s = f_s(P) ∩ N^d`, and use Dickson only on that subtype.  Reassemble the finite orthants and prove the converse directly from finite generators.

**Tech Stack:** Coq 8.20.1, T06 `Periodic`, `ZVec`, Kruskal `afs`, Dickson/Higman adapters.

**Spec:** `docs/review/t10-planning-audit.md`

## Global Constraints

- The public theorem is the iff in audit §3 T10-B.
- Do not assert coordinate order is a WQO on all of `Z^d`.
- `PeriodicLe P x y` remains `P (y-x)` and is not strengthened with coordinate comparison.

## Review Focus

- Periodic sets containing both positive and negative generators.
- Zero vector and dimension zero.
- Empty orthants and points on sign boundaries.
- Exact equivalence between the product relation on `Q_s` and `PeriodicLe`.
- Both directions of the iff, not only finite generation implies WQO.

---

### Task 1: Signed algebra and finite-generation semantics

**Files:**
- Create: `theories/Order/PeriodicOrder.v`
- Create: `theories/Audit/PeriodicOrderStatements.v`
- Modify: `_CoqProject`, `Makefile`

**Interfaces:**
- Consumes: `Periodic`, `zvec_add`, `zvec_nsmul`.
- Produces: `zvec_sub`, `zvec_generated`, `FinitelyGeneratedPeriodic`, `PeriodicLe`.

- [ ] **Step 1: RED.** Add the final iff theorem with `Abort` replaced by a failing audit `Check`; record the missing declarations.
- [ ] **Step 2: Implement algebra.** Prove subtraction/addition/natural-combination laws extensionally over vectors.
- [ ] **Step 3: Fix finite generation.** Prove generators belong to `P`, zero and closure consequences, and invariance under duplicate/zero generators.
- [ ] **Step 4: GREEN interface tests.** Check `P={0}`, all integer multiples of one generator, and `d=0`.
- [ ] **Step 5: Commit.** Commit only the three B files/config edits.

### Task 2: R11 orthant proof

**Files:**
- Modify: `theories/Order/PeriodicOrder.v`
- Modify: `theories/Audit/PeriodicOrderStatements.v`

**Interfaces:**
- Produces: finite sign patterns, `sign_flip`, `Q_s`, transported order, `qs_product_order_iff_periodic_le`.

- [ ] **Step 1: RED counterexample.** Formalize a signed carrier where ordinary coordinate order is not WQO; this must fail the rejected unrestricted proof premise.
- [ ] **Step 2: Define `Q_s`.** Include both membership in transported `P` and nonnegativity; prove sign flip is involutive.
- [ ] **Step 3: Prove the relation equivalence.** On `Q_s` only, prove product of transported periodic order and Dickson comparison iff the intended periodic difference order.
- [ ] **Step 4: Prove WQO assembly.** Use finite sign-pattern union/product closure and transport back to `P`.
- [ ] **Step 5: Prove finite generation.** Complete the reverse implication without a choice-backed unproved basis theorem.
- [ ] **Step 6: GREEN and audit.** Run `make check-t10-b`, `make audit-t10-b`, and module `coqchk`; capture full type and assumptions.
- [ ] **Step 7: Independent review.** Reviewer traces every Dickson invocation to a `Q_s` subtype and checks the `<=Q_s` equivalence.
- [ ] **Step 8: Commit.** Commit `feat(t10-b): prove signed periodic order theorem` with explicit paths.
