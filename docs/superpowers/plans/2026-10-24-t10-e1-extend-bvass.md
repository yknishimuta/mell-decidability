# Task 6E1 Extend(B,F) Implementation Plan

> Scope: implement only FoSSaCS 2026 Section 4 `Extend(B,F)` and the local API needed by Lemma 9. Do not start the branching-depth argument.

## 1. Freeze the executable representation

- Add `theories/BVASS/Extend.v`.
- Represent every input-state occurrence by an ordered choice: keep it, or omit it using one matching configuration from `F`.
- Enumerate choices structurally over the input-state list, preserving positions and multiplicity.
- Compute the remaining state list and the signed action plus the exact sum of omitted counters.
- Emit a normal `SRule` when the remaining list is nonempty; emit an initial configuration only when it is empty and `zvec_to_nvec` succeeds.

## 2. Prove enumeration correctness and completeness

- Define a relational specification for legal omission selections.
- Prove every enumerated selection satisfies it and every legal selection is enumerated.
- Prove generated-rule and generated-initial membership iff the corresponding original rule and legal selection exist.
- Include the all-keep selection, hence every original rule remains present.

## 3. Prove reach preservation

- Prove original runs remain valid in the extension by mutual induction on `ValidSRun`/`ValidSRuns`.
- Prove restoration of an extended run into the original BVASS by mutual induction, using reachability of each selected `F` configuration to restore omitted child occurrences.
- Treat generated initials separately: original initials are direct; all-omitted generated initials reconstruct one original-rule node.
- Derive `extend_bvass_reach_iff` through `stateful_run_reach_iff`.

## 4. Lemma 9 preparation

- Expose the local root-contraction theorem that builds an extended run from retained child runs plus omitted `F` configurations, preserving the root configuration and positional multiplicity.
- Record the retained/omitted length equation.
- Define the basis-root list and prove it consists of reachable configurations when every basis run is valid.

## 5. Regression and verification

- Add `theories/Audit/BVASSExtendExamples.v` with `Check`, boundary computations, the negative-all-omission guard, and assumption output.
- Register both files in `_CoqProject` and add focused `check-t10-e1` / `audit-t10-e1` targets.
- Run focused build, Task 6E0, T09/T10-G audits, forced full build, `coqchk`, forbidden-token scans, and Git whitespace checks.
- Obtain a read-only independent review, write `docs/review/t10-e1-extend-bvass-audit.md`, stage only Task 6E1 files, and commit locally.
