# C4-3C2 Direct Finite Basis Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete Lemma 6.10 by deriving a finite cylindric basis directly from decidable finite presentations and the existing monotone-subsequence theorem.

**Architecture:** Add one focused Coq module after `FaceStrippingLemma610.v`.  R0 exposes decision procedures parameterized by concrete generator/base lists; R1 uses decidable least-code search to build a bad sequence; R2 instantiates both with the existing geometric subsequence theorem.  No general sequence-to-`afs` theorem is introduced.

**Tech Stack:** Coq, project codecs, Presburger/MiniCooper decision API, `constructive_indefinite_description_nat`.

**Spec:** User contract `T10-C4-3C2-R` in the current thread.

## Global Constraints

- Preserve all existing C4-3C2 declarations and public types.
- No Axiom, Admitted, Abort, ClassicalEpsilon, countable/dependent choice, UIP/K, Eq_rect_eq, functional extensionality, or external oracle.
- Stop after Lemma 6.10; do not enter C4-3D.
- Modify and stage only the new connection source, focused audit, review document, plan, and minimal `_CoqProject` entries.

## Review Focus

- Nonnegative natural coefficients must not be widened to arbitrary integers.
- Prop witnesses for finite presentations must only be destructed inside Prop conclusions.
- Extract values outside the original period, especially `1 + 2N`, must remain supported.
- Bad-sequence construction must use decidable least-code search, not hidden choice.
- The final finite bases must themselves belong to Extract.

---

### Task 1: R0 concrete finite-presentation decision procedures

**Files:**
- Create: `theories/Geometry/FaceStrippingLemma610FiniteBasis.v`
- Create: `theories/Audit/FaceStrippingLemma610FiniteBasisExamples.v`
- Modify: `_CoqProject`

**Interfaces:**
- Consumes: explicit generator/base lists and their `SameSet` specifications.
- Produces: decidable generated-monoid membership, finite-union translate membership, Extract membership, and `PeriodicLe` membership.

- [ ] Write `Fail Check` declarations for the concrete decision APIs and compile RED.
- [ ] Audit MiniCooper/Presburger syntax, semantics, and correctness theorems.
- [ ] Implement nonnegative-coefficient membership with an explicit finite list argument.
- [ ] Prove the Extract characterization and finite Diophantine reduction.
- [ ] Compile focused GREEN before continuing.

### Task 2: R1 direct bad-sequence finite-basis theorem

**Files:**
- Modify: `theories/Geometry/FaceStrippingLemma610FiniteBasis.v`
- Modify: `theories/Audit/FaceStrippingLemma610FiniteBasisExamples.v`

**Interfaces:**
- Consumes: decidable set membership, decidable `PeriodicLe`, QCylindricity, and the infinite monotone-subsequence property.
- Produces: `monotone_subsequence_implies_finitary`.

- [ ] Add a failing `Check` for the theorem and compile RED.
- [ ] Prove every finite non-cover has an escaping set member.
- [ ] Encode escaping candidates and build the infinite bad sequence by least-code recursion.
- [ ] Contradict the supplied strictly increasing monotone subsequence.
- [ ] Compile focused GREEN and print assumptions.

### Task 3: R2 Lemma 6.10 integration

**Files:**
- Modify: `theories/Geometry/FaceStrippingLemma610FiniteBasis.v`
- Modify: `theories/Audit/FaceStrippingLemma610FiniteBasisExamples.v`
- Create: `docs/review/t10-c4-3c2-r-direct-finite-basis-audit.md`

**Interfaces:**
- Consumes: R0/R1 plus `maximal_extract_monotone_subsequence`, face-period periodicity and finite generation, and Extract cylindricity.
- Produces: `lemma_6_10_maximal_extract_finitary` with the contracted type.

- [ ] Add the final failing `Check` and compile RED.
- [ ] Destruct finite presentations only within the final Prop proof and construct the two decision procedures.
- [ ] Apply the direct finite-basis theorem without introducing `afs`.
- [ ] Add focused edge regressions, including `2N/(1+2N)` and the proper-face `2N^2` case where feasible from existing fixtures.
- [ ] Run focused build, full regression, coqchk, assumptions scan, prohibited-token scan, diff check, and independent review.
- [ ] Commit only verified target files without pushing.
