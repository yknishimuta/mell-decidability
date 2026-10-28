# Task QA-1 Decision-Path Audit Design

## Intent

Audit the executable path from `mell_decide` through its verified fast
prechecks and complete certificate-search fallback.  The audit must distinguish
kernel-verified semantics from observed extracted-runtime branch coverage.

## Goals

- Expose the exact current dispatch order without changing `mell_decide`.
- Prove a traced Audit-only dispatcher returns exactly the public result.
- Record branch guards for unit, weight, goal saturation, full saturation, and
  fallback paths.
- Package standalone fallback soundness, eventual success, finite-fuel
  soundness, and agreement with the public result.
- Observe current runtime cases by path and add bounded branch-specific tests.
- Verify the existing extraction target and runner call the same Gallina
  definitions audited here.

## Non-goals

- No new decision algorithm or optimization.
- No change to the public API or proof-system semantics.
- No special cases in `mell_decide` for test inputs.
- No claim that every mathematically verified branch is practically fast.

## Existing executable order

`mell_saturation_decide` first runs `unit_sequent_provableb`.  If it rejects,
`multiplicative_weight_refutes` may return a definitive NO.  Otherwise
`mell_reach_saturation_decide` first accepts a goal-slice saturation YES; every
other goal-slice result continues to full saturation, which can return YES,
NO, or `None`.  Only `None` reaches `mell_decide_reference`, namely
`bvas_decide (reduce_mell Gamma)`.  The finite-stage path follows the same fast
dispatcher before `mell_stage_reference`.

## Approaches considered

1. Refactor `mell_decide` around a new common traced dispatcher.  This would
   make tracing definitional but changes the public implementation and is not
   justified for an audit.
2. Duplicate the dispatcher only in OCaml.  This observes guards but lacks a
   kernel-checked structural correspondence.
3. **Chosen:** define an Audit-only traced dispatcher solely from the existing
   component functions and prove its second projection equals `mell_decide` by
   branch analysis.  Observe the same extracted guard functions in the runner.
   This is minimal and leaves the production dependency graph unchanged.

## Coq additions

`theories/Audit/DecisionPathAudit.v` defines the five paths that actually
exist: unit YES, weight NO, goal-saturation YES, full-saturation answer, and
complete fallback.  It proves result equality, exact guard implications,
overall soundness, standalone fallback soundness and eventual success, and
re-exports finite-fuel/public agreement facts with complete types.

`theories/Audit/DecisionPathExamples.v` fixes representative branch guards and
uses `Check`/`Print Assumptions` for the audit contracts.  The existing
Decision and Reduction modules do not import either Audit module.

## Runtime observation

The handwritten runner gains Audit-only modes that report the extracted unit,
weight, goal-saturation, full-saturation, and fallback guards.  It continues to
call `MELL.mell_decide` for final answers.  A dedicated Make target records
path coverage separately from the existing 22-case result gate.  Bounded MELL
fallback attempts may be reported `UNOBSERVED`; BVAS YES and NO certificate
enumeration must still be observed.

## Trust and verification

No axiom, choice oracle, extraction override, or cast is added.  New proof
dependencies are audited with `Print Assumptions`.  Completion requires focused
and full builds, `validate`, dependency-closure `coqchk`, all final gates,
forbidden-token and extraction-oracle scans, target/staged diff checks, and an
independent review.
