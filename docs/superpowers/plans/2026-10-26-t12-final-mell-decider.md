# Task 12: Final MELL Decider Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the finite-certificate BVAS search with the proved singleton separator, compose it with the constructive MELL reduction, expose finite-stage/code APIs, and extract a checked OCaml program.

**Architecture:** Keep the existing alternating certificate search unchanged. A small bridge converts `Separator.Singleton.singleton_separator` into `Decision.Stage.singleton_separator`; the total BVAS decision function remains `search_of_eventual` over `bvas_stage`. The MELL layer only projects the dependent `ReachInstance` produced by `reduce_mell`. Extraction targets these transparent wrappers and the already-audited certificate checkers.

**Constraints:** No new oracle, choice axiom, fixed-width integer extraction, public proof parameter, or weakening of finite-fuel `None`. Preserve all unrelated worktree changes and commit only Task 12 files.

**Spec:** The Task 12 continuation specification in the active conversation (performance P0–P3 and extraction-trust T0–T1).

## Global Constraints

- Keep Coq 8.20.1, the pinned YALLA source, and the existing OCaml/opam environment.
- Preserve all public Task 6F and Task 12 theorem types and introduce no new mathematical axiom.
- Apply P1 and measure it before deciding whether P2 or P3 is necessary.
- Treat `None` and timeout as inconclusive, never as NO.
- Retain arbitrary-precision nat/Z extraction and audit every generated `Obj.magic` pattern reachable from public entry points.

## Review Focus

- A zero-test-free direct conversion must preserve unary signs, split multiplicity, leaf states, and nonnegative intermediates in both directions.
- The optimized branch must decide zero-test freedom before constructing the layered machine.
- Performance measurements must separate reduction construction from certificate search under identical 60-second limits.
- Strict decoders must remain the boundary for untrusted values; handwritten casts and extraction oracles are forbidden.
- Runtime PASS requires actual MELL YES and NO answers, not direct certificate checks, `None`, or timeouts.

## Task 1: Close the BVAS decision API

- Add `theories/Decision/BVAS.v`.
- Prove the Task 11-F certificate satisfies `invariant_obligation` and hence `Decision.Stage.singleton_separator`.
- Define transparent `bvas_decide` using `bvas_decide_of_separator`.
- Prove true/false correctness, stage/fuel soundness, eventual hit, and halt/spec lemmas.
- Add failing-then-passing public checks in the Task 12 audit module.

## Task 2: Compose the MELL decision API

- Add `theories/Decision/MELL.v`.
- Define `mell_stage`, `mell_search_fuel`, and `mell_decide` by destructing the single `ReachInstance` returned by `reduce_mell`.
- Prove stage/fuel soundness, halting and agreement with the total decision result.
- Prove `mell_decide_true_iff`, `mell_decide_false_iff`, and `mell_decide_with_cut`.
- Define `decide_code`; prove malformed-code rejection, round-trip exposure, direct/code agreement, and `decide_code_correct`.

## Task 3: Regression and public-statement audit

- Add `theories/Audit/Statements.v` and `theories/Audit/Regression.v`.
- Cover even/odd stage behavior, zero fuel, reachable/unreachable BVAS examples, MELL examples already justified by T02, valid codec round trips, and malformed input rejection.
- Record exact `Check` and `Print Assumptions` output.

## Task 4: Extraction and runtime harness

- Add `theories/Decision/Extract.v` using standard extraction without `ExtrOcamlNatInt`/`ExtrOcamlZInt`.
- Extract `mell_decide`, `decide_code`, `mell_stage`, and `mell_search_fuel` plus dependencies.
- Add a thin OCaml runner that only invokes extracted entry points.
- Add `check-final`, `audit-final`, and `extract-final` Make targets.
- Compile the generated OCaml and run the required tractable YES/NO/codec cases, reporting timeouts separately.

## Task 5: Full verification and trust report

- Run focused builds, all required regressions, forced full rebuild, `validate`, and dependency-closure `coqchk`.
- Scan Coq sources and extracted OCaml for forbidden constructs, unresolved axioms, `Obj.magic`, and unsafe extraction overrides.
- Record tool versions, hashes, assumptions, extraction/compile/runtime evidence, performance limits, and Git state in `docs/review/final-trust-report.md`.
- Obtain an independent review, fix findings, explicitly stage only Task 12 deliverables, and create one local commit without pushing.

## Task 6: P0 performance characterization

- [ ] Record Coq, OCaml, Zarith, bytecode/native, timeout, wall/user time, and RSS for `[One]` and the empty sequent.
- [ ] Measure translation, support/subformula enumeration, FullZero generation, zero-test elimination, orientation/state erasure, and certificate search separately where each stage terminates.
- [ ] Record dimensions and rule/state counts before and after zero-test elimination without printing full machines.
- [ ] Verify whether public computation rebuilds `reduce_mell` at each search stage.

## Task 7: P1 zero-test-free direct conversion

- [ ] Add failing Coq examples specifying the direct conversion for a leaf, unary signed action, split multiplicity, and a machine with no zero-test rules.
- [ ] Define a decidable zero-test-free predicate and a direct bottom-up SBVAS conversion before any layered construction.
- [ ] Prove root-query soundness and completeness against `FullZeroReach`, including all state-membership guards.
- [ ] Define the optimized reduction branch and prove `Holds` equivalence with the reference reduction.
- [ ] Reconnect Task 6F/Task 12 public theorems, extract, compile, and rerun the identical 60-second measurements.

## Task 8: Conditional P2/P3 performance work

- [ ] If P1 leaves reduction construction dominant, write failing pruning tests before implementing root-directed structural pruning and prove root-query equivalence.
- [ ] If reduction terminates but total decision remains slow, instrument certificate enumeration/checking and separate checker cost from discovery cost.
- [ ] Change enumeration only if measurements require it, preserving completeness, fairness, finite-fuel soundness, and eventual success.

## Task 9: T0/T1 extraction trust audit

- [ ] Inventory every generated `Obj.magic`, group identical extraction patterns, map them to Coq declarations, and mark public reachability and external-input exposure.
- [ ] Confirm no handwritten cast, unreviewed extraction override, axiom stub, or mathematical oracle enters the executable closure.
- [ ] Exercise strict codec rejection and arbitrary-precision nat/Z behavior, including signed actions and values beyond fixed-width OCaml integers.
- [ ] Record Coq/OCaml/Zarith trust boundaries without claiming the extracted closure is `Obj.magic`-free.

## Task 10: Runtime gate and final verification

- [ ] Add a reproducible runtime target only after it obtains actual answers for all required MELL YES/NO and retained BVAS/codec cases.
- [ ] Run focused builds, forced full rebuild, validate, dependency-closure coqchk, exact `Check`/`Print Assumptions`, forbidden scans, extraction, OCaml compilation, and runtime tests.
- [ ] Complete the performance audit and final trust report, obtain a fresh independent review, explicitly stage only authorized files, and commit locally without pushing.
