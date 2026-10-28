# AI-Assisted Development

**Project:** Mechanized Decidability of Propositional MELL  
**Record date:** 2026-10-27

## AI use

OpenAI ChatGPT and Codex assisted the development of this Rocq formalization during October 2026. According to the project maintainer's account:

- **Proof design:** The model identified as `astra` was used to develop proof strategies, including the BVAS semilinear separation argument and the MELL-to-BVAS reduction.
- **Implementation:** The model identified as `gpt-5.6-sol` was used to assist with Gallina definitions, proof scripts, and implementation of the decision procedure.
- **Other assistance:** ChatGPT and Codex were also used for debugging, planning checks and reviews, preparing development instructions, and documentation.

These tools assisted the research and development process; their outputs were not treated as verified mathematical results.

## Verification

The project reports successful checking of **269 Coq/Rocq source files** with **Coq 8.20.1**, theorem and assumption audits, `coqchk` verification, OCaml extraction and compilation, and **22 runtime regression tests**. The exact statements, assumptions, and trust boundaries are documented in `theories/Audit/Statements.v` and `docs/review/final-trust-report.md`.

Kernel checking verifies formal proofs relative to their definitions and assumptions. It does not by itself establish that the formal statements faithfully express the intended mathematics. Nor do extraction and runtime tests constitute end-to-end verification of the OCaml toolchain.

## Record limitations and responsibility

The model names `astra` and `gpt-5.6-sol` are recorded as reported by the project maintainer; exact backend snapshot identifiers and complete model-by-model session histories have not been established. The human maintainer remains responsible for the mathematical claims, acceptance of changes, source provenance, and publication. AI tools are neither authors nor independent reviewers and are not part of the trusted proof kernel.
