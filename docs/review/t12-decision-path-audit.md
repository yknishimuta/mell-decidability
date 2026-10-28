# Task QA-1: optimized MELL decision-path and complete-fallback audit

Date: 2026-10-27

Baseline: `fceedd1e9d2a06d628e1c8bb30075dcd6037ba3b`

## Scope and conclusion

This audit checks the executable path, not the paper-fidelity correspondence.
The current public dispatcher uses only kernel-checked branches and reaches the
complete certificate search exactly when every fast precheck is inconclusive.
No `None` result is converted to NO.  Mathematical path correspondence is
verified; runtime branch coverage is reported separately below.

## Actual call graph

```text
mell_decide Gamma
  |
  +-- unit_sequent_provableb Gamma = true
  |      -> true                                      [UnitPath]
  |
  +-- multiplicative_weight_refutes Gamma = true
  |      -> false                                     [WeightPath]
  |
  +-- mell_goal_saturation_decide Gamma = Some true
  |      -> true                                      [GoalSaturationPath]
  |
  +-- mell_full_saturation_decide Gamma = Some answer
  |      -> answer                                    [FullSaturationPath]
  |
  `-- mell_full_saturation_decide Gamma = None
         -> mell_decide_reference Gamma               [FallbackPath]
              -> reach_instance_decide (reduce_mell Gamma)
              -> bvas_decide
              -> search_of_eventual bvas_instance_stage
              -> alternating RawRun/SemiCode stages
```

`mell_goal_saturation_decide` is a YES-only slice: its underlying
`goal_saturation_decide` maps every result other than `Some true` to `None`.
`mell_reach_saturation_decide` therefore continues to full saturation for
both `None` and any hypothetical non-true answer.  Full saturation returns NO
only when `saturation_decide` has checked a finite fixed point; fuel exhaustion
alone returns `None`.

`mell_stage` uses exactly the same `mell_saturation_decide` first.  On `None`
it calls `mell_stage_reference`, while `mell_search_fuel` fairly scans these
stages from zero up to the supplied bound.

## Kernel-checked structural trace

`Mell.Audit.DecisionPathAudit` defines:

```coq
Inductive DecisionPath :=
| UnitPath | WeightPath | GoalSaturationPath
| FullSaturationPath | FallbackPath.

traced_mell_decide : sequent -> DecisionPath * bool

traced_mell_decide_result :
  forall Gamma,
    snd (traced_mell_decide Gamma) = mell_decide Gamma.
```

The equality proof unfolds the current production definitions and performs the
same branch analysis.  It is not derived merely from both functions deciding
`Provable`.  Exact guard theorems are public for all five constructors:

```coq
decision_path_unit_guard :
  forall Gamma,
    mell_decision_path Gamma = UnitPath <->
    unit_sequent_provableb Gamma = true.

decision_path_weight_guard :
  forall Gamma,
    mell_decision_path Gamma = WeightPath <->
    unit_sequent_provableb Gamma = false /\
    multiplicative_weight_refutes Gamma = true.

decision_path_goal_saturation_guard :
  forall Gamma,
    mell_decision_path Gamma = GoalSaturationPath <->
    unit_sequent_provableb Gamma = false /\
    multiplicative_weight_refutes Gamma = false /\
    mell_goal_saturation_decide Gamma = Some true.

decision_path_full_saturation_guard :
  forall Gamma,
    mell_decision_path Gamma = FullSaturationPath <->
    unit_sequent_provableb Gamma = false /\
    multiplicative_weight_refutes Gamma = false /\
    mell_goal_saturation_decide Gamma <> Some true /\
    exists answer, mell_full_saturation_decide Gamma = Some answer.

decision_path_fallback_guard :
  forall Gamma,
    mell_decision_path Gamma = FallbackPath <->
    unit_sequent_provableb Gamma = false /\
    multiplicative_weight_refutes Gamma = false /\
    mell_goal_saturation_decide Gamma <> Some true /\
    mell_full_saturation_decide Gamma = None.
```

The Audit module is not imported by Decision, Reduction, or extraction
modules.  The production computation remains unchanged.

## Fast-precheck soundness

| Branch | Executable definition | Result kind | Kernel theorem | Behaviour on inconclusive input |
|---|---|---|---|---|
| positive-unit fragment | `unit_sequent_provableb` | YES only | `unit_sequent_provableb_sound : ... = true -> Provable Gamma` | `false` continues; it is not NO |
| multiplicative weight | `multiplicative_weight_refutes` | NO only | `multiplicative_weight_refutes_sound : ... = true -> ~ Provable Gamma` | `false` continues; satisfying the weight is not YES |
| goal slice | `mell_goal_saturation_decide` | YES only | `mell_goal_saturation_decide_sound` | every non-YES continues |
| full saturation | `mell_full_saturation_decide` | YES or NO | `mell_full_saturation_decide_sound` | rule-limit, zero tests, or no bounded fixed point return `None` |
| combined dispatcher | `mell_saturation_decide` | YES, NO, or `None` | `mell_saturation_decide_sound` | only `None` reaches fallback |

The unit checker accepts a singleton formula recursively built from `One`,
`Tensor`, and `Bang`; every acceptance constructs a derivation in the same
public `Provable` calculus.  Fragment rejection makes no negative claim.

The weight refuter first requires every formula to be multiplicative, so its
invariant proof covers only Atom, CoAtom, One, Bottom, Tensor, and Par.  Bang
and WhyNot make the refuter inapplicable.  A weight unequal to one refutes a
derivation; weight one is deliberately not treated as sufficient.

Finite saturation constructs only actual rule consequences.  Its NO proof
uses equality of two successive finite configuration lists and
`saturation_fixed_point_complete`; failure to find a target at an arbitrary
fuel is not enough.

## Complete fallback

The fallback stage alternates exactly as follows:

- stage `2*k`: decode RawRun `k`, execute `eval_run`, compare its target, and
  return `Some true` only on a valid target-reaching run;
- stage `2*k+1`: decode SemiCode `k`, run `check_invariantP`, and return
  `Some false` only for an initial-containing, rule-closed invariant excluding
  the target;
- every decoding or checking failure returns `None`.

The relevant public Audit contracts are:

```coq
mell_fallback_stage_sound_true :
  forall Gamma stage,
    mell_stage_reference Gamma stage = Some true -> Provable Gamma.

mell_fallback_stage_sound_false :
  forall Gamma stage,
    mell_stage_reference Gamma stage = Some false -> ~ Provable Gamma.

mell_fallback_search_halts :
  forall Gamma,
    exists fuel answer,
      mell_search_fuel_reference Gamma fuel = Some answer.

mell_fallback_decide_true_iff :
  forall Gamma,
    mell_decide_reference Gamma = true <-> Provable Gamma.

mell_fallback_decide_false_iff :
  forall Gamma,
    mell_decide_reference Gamma = false <-> ~ Provable Gamma.
```

YES eventual success follows from `eval_run_complete`, `encode_run`, and the
even-stage decoder theorem.  NO eventual success follows from
`singleton_separator`, `encode_semi`, and the odd-stage decoder theorem.  The
separator is used only to prove termination; extracted `bvas_decide` is
`search_of_eventual bvas_instance_stage` and contains no separator oracle.

`mell_search_fuel_sound_true` and `mell_search_fuel_sound_false` prove that a
successful finite prefix has the advertised meaning.  `None` is characterized
by `search_fuel_none` only as absence of a hit below that fuel.  The existing
`mell_search_fuel_agrees` proves every successful finite answer equals the
public total answer.  The Audit module proves the analogous standalone
fallback facts `mell_fallback_search_fuel_sound_true/false` and
`mell_fallback_search_fuel_agrees`.

## Existing 22-case native gate

All cases use the extracted functions in `docs/review/extraction/final`; the
runner constructs inputs but does not replace answers with expected constants.

| Case | Result | Decision path | Native wall time (s) | Runtime status |
|---|---:|---|---:|---|
| `mell-one` | true | UnitPath | 0.39 | OBSERVED |
| `mell-identity` | true | GoalSaturationPath | 0.01 | OBSERVED |
| `mell-tensor-units` | true | UnitPath | 0.00 | OBSERVED by the dedicated path gate |
| `mell-par-identity` | true | GoalSaturationPath | 0.01 | OBSERVED |
| `mell-bang-one` | true | UnitPath | 0.00 | OBSERVED by the dedicated path gate |
| `mell-empty` | false | WeightPath | 0.00 | OBSERVED |
| `mell-two-ones` | false | WeightPath | 0.00 | OBSERVED |
| `bvas-initial` | true | complete BVAS RawRun/SemiCode search | 0.00 | OBSERVED |
| `bvas-empty` | false | complete BVAS RawRun/SemiCode search | 0.00 | OBSERVED |
| `bvas-unary-plus-two` | true | complete BVAS search | 0.00 | OBSERVED |
| `bvas-binary` | true | complete BVAS search | 0.00 | OBSERVED |
| `bvas-even-odd` | false | complete BVAS search | 0.03 | OBSERVED |
| `bvas-d0-empty` | false | complete BVAS search | 0.00 | OBSERVED |
| `code-invalid` | false | strict decode rejection | 0.00 | OBSERVED |
| `code-direct-agree` | true | decoded result equals direct result; its Tensor/One direct input is UnitPath | 0.01 | Result OBSERVED; input path OBSERVED separately |
| `codec-invalid-vector-length` | true | strict codec predicate | 0.00 | OBSERVED |
| `codec-invalid-integer-tag` | true | strict codec predicate | 0.00 | OBSERVED |
| `codec-invalid-positive-zero` | true | strict codec predicate | 0.00 | OBSERVED |
| `codec-invalid-arity-zero` | true | strict codec predicate | 0.01 | OBSERVED |
| `codec-invalid-reach-instance` | true | strict codec predicate | 0.00 | OBSERVED |
| `bigint-arithmetic` | true | arithmetic regression, no MELL decision | 0.00 | OBSERVED |
| `signed-action-negative` | true | action regression, no MELL decision | 0.00 | OBSERVED |

The timing pass used the same native executable and `/usr/bin/time -p`, one
fresh process per case.  Values rounded to 0.00 seconds are below that tool's
centisecond display resolution; they are not claimed to take literally zero
time.

## Additional path coverage

The dedicated `check-decision-paths` target observes:

- UnitPath: `[One]`, `[Tensor (One, One)]`, and `[Bang One]`;
- WeightPath: `[]` and `[One; One]`;
- GoalSaturationPath: atom identity and its Par form;
- FallbackPath guard: mismatched atoms `[Atom 0; CoAtom 1]`;
- complete BVAS fallback YES: an initial target;
- complete BVAS fallback NO: an empty-initial system.

A bounded small-formula scan additionally classified Par mismatch, Tensor
mismatch, and identity plus an unmatched atom as FallbackPath, while Bottom
plus One examples used GoalSaturationPath.  It found no public MELL example
using FullSaturationPath.  The full-saturation branch is therefore VERIFIED by
the general guard and soundness theorems but UNOBSERVED through public MELL
runtime in this audit.  Standalone saturation YES and fixed-point NO are
VERIFIED by kernel-computed `FiniteSaturationExamples`; they were not counted
as extracted-native branch observations.

The mismatched-atom public fallback computation was run for 11 seconds without
a result and was interrupted.  It is recorded as timeout/UNOBSERVED, never as
NO.  Its FallbackPath guard was observed independently.  BVAS fallback YES and
NO both terminated in the native path gate.

## Coq-to-OCaml correspondence

`theories/Decision/Extract.v` directly names `mell_decide`, `mell_stage`, and
`mell_search_fuel`.  Generated `MELL.ml` preserves the inspected match on
`mell_saturation_decide`; `BVASOfSeparator.ml` calls `search_of_eventual`, and
`Search.ml` implements unbounded decidable search over `bvas_stage`.
`final_runner.ml` calls `MELL.mell_decide` and `BVAS.bvas_decide` directly.

The path reporter calls the same extracted component functions in the proved
priority order.  The structural correspondence itself remains the Coq theorem
`traced_mell_decide_result`; the OCaml helper is observational instrumentation,
not a second decider.

No `Extract Constant`, axiom stub, handwritten `Obj.magic`, or new oracle was
added.  Existing standard-extraction casts and Zarith-backed arbitrary-
precision integers retain the trust boundaries documented in
`final-trust-report.md`.

## Verification-gate correction

QA-1 found that the shell `run_case` helper previously returned failure for a
bad case but the surrounding brace group could continue, allowing a later
successful case to determine the final shell status.  This was reproduced with
an unknown path mode.  Both `check-runtime-mell` and `check-decision-paths` now
exit immediately when the runner fails or an expected value differs.  This is
a verification-gate correction; no Gallina computation or theorem changed.

## Assumptions and final classification

The fast local soundness lemmas are closed where their existing dependencies
are constructive.  The total fallback and traced total result inherit only
the already documented `Classical_Prop.classic` through separator existence.
No new mathematical premise appears in a theorem type.

- Mathematical decision-path audit: PASS.
- Runtime fast-path coverage: Unit, Weight, GoalSaturation, and Fallback guard
  OBSERVED; FullSaturation via public MELL is UNOBSERVED.
- Complete BVAS fallback: YES and NO OBSERVED.
- Public MELL fallback final answer: UNOBSERVED within the bounded run.

## Verification results

The final fresh verification used Coq 8.20.1, OCaml 4.14.2, and Zarith 1.14.

- focused compilation of `DecisionPathAudit.v` and
  `DecisionPathExamples.v`: PASS;
- forced full `_CoqProject` rebuild with `make -B -f Makefile.coq -j2`: PASS;
- `make -f Makefile.coq validate`, including the full dependency-closure
  `coqchk -silent`: PASS;
- `make check-final`: PASS (as a prerequisite of the later final gates);
- `make audit-final`: PASS, including public `Check`, `Print Assumptions`, and
  forbidden-construct scans;
- `make extract-final`: PASS; extracted OCaml compiled successfully;
- fail-fast `make check-runtime-mell`: PASS for all 22 established cases;
- `make check-decision-paths`: PASS for all dedicated path observations;
- reverse-import scan: PASS; no Decision or Reduction module imports the new
  Audit modules;
- extraction scan: no `AXIOM TO BE REALIZED`, no new `Extract Constant`, and
  no handwritten cast or oracle.  The existing standard extraction output
  still contains ten `Obj.magic` occurrences on nine lines, as recorded in
  the project trust audit;
- `git diff --check`: PASS.

The full `validate` context summary mentions axioms used elsewhere in the
dependency closure; this is not the assumptions report for these public
theorems.  The targeted `Print Assumptions` results for the QA-1 total/fallback
theorems list only the pre-existing `Classical_Prop.classic`, while the local
fast-check facts printed in the Audit regression are closed under the global
context where expected.

## Independent review

An independent reviewer inspected the Coq definitions and theorem statements,
the extraction entry points, runner instrumentation, Make gates, reverse
dependencies, and this report.  The first pass identified three reporting and
coverage gaps: two existing UnitPath inputs lacked direct native path modes,
standalone Coq saturation examples were described as native observations, and
several new Audit theorems lacked explicit `Check`/`Print Assumptions` lines.
All three were corrected and re-verified.  The independent re-review result is
PASS with no remaining findings.
