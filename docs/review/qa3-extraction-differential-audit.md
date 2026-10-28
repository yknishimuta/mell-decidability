# QA-3 Gallina/OCaml extraction differential audit

Date: 2026-10-27
Baseline: `9aa3c86e61d1dff766857c4217debe61e018b0cc` on
`work/mell-formalization`

## Scope and method

This is a finite differential test, not a proof of Coq extraction, OCaml, or
Zarith.  Each executed fixture has an independently stated closed Gallina
equation in `Mell.Audit.ExtractionDifferentialExamples`.  The kernel checks
those equations.  A hand-written, non-generated runner then reconstructs the
same named input against a freshly generated extraction closure and compares
its textual result with the explicit TSV expectation.

`make check-extraction-differential` performs, in order:

1. the existing final focused build;
2. deletion and fresh generation of the ignored OCaml extraction closure;
3. the existing extraction policy and exact `Obj.magic` count checks;
4. bytecode compilation of the generated closure;
5. focused compilation of the Gallina fixture module;
6. native compilation of the same fresh closure plus the audit runner;
7. exact-name, exact-count, timeout-aware comparison of every TSV case.

The runner contains no decision procedure.  It only constructs concrete data,
calls the extracted functions, and renders their results.  It is not imported
by any Gallina computation module.

## Function correspondence

| Gallina declaration | Extracted OCaml declaration | Inputs/results exercised | Called by |
|---|---|---|---|
| `Mell.Logic.Code.encode_sequent`, `decode_sequent` | `Code0.encode_sequent`, `Code0.decode_sequent` | `sequent`, `nat`, `option sequent` | codec audit, `decide_code` |
| `Mell.Reduction.Main.encode_reach_instance`, `decode_reach_instance` | encoder body reconstructed from `Cantor.to_nat`, `Main.encode_ibvas`, `Code1.encode_nvec`; decoder `Main.decode_reach_instance` | dimension 0 valid and malformed instances | reach codec audit |
| `Mell.BVAS.Code.encode_run`, `decode_run` | `Code.tree_encode`, `Code1.decode_run` | binary `RawRun` | certificate enumeration |
| `Mell.Semilinear.Code.encode_semi`, `decode_semi` | `(Code2.semi_codec d).encode`, `Code2.decode_semi` | normal and dimension-0 `SemiCode` | invariant enumeration |
| `Mell.BVAS.Certificates.eval_run` | `Certificates.eval_run` | valid/invalid raw trees | even BVAS stages |
| `Mell.Decision.Invariant.check_invariantP` | `Invariant.check_invariantP` | accepted and three rejection modes | odd BVAS stages |
| `Mell.Presburger.Decide.presburger_decide` | `Decide.presburger_decide` | existential, universal, nested, divisibility | invariant checker |
| `unit_sequent_provableb` | `UnitFragment.unit_sequent_provableb` | yes/no/`!1` | optimized MELL dispatch |
| `multiplicative_weight_refutes` | `MultiplicativeWeight.multiplicative_weight_refutes` | refutation/applicability boundary | optimized MELL dispatch |
| `mell_goal_saturation_decide` | `MELL.mell_goal_saturation_decide` | `Some true`, `None` | optimized MELL dispatch |
| `mell_full_saturation_decide` | `MELL.mell_full_saturation_decide` | `Some true`, `Some false` | optimized MELL dispatch |
| `bvas_stage` | `Stage.bvas_stage` | even/odd, `Some true/false/None` | complete certificate search |
| `mell_stage`, `mell_search_fuel` | `MELL.mell_stage`, `MELL.mell_search_fuel` | finite stage/fuel | public finite search |
| `mell_decide`, `decide_code` | `MELL.mell_decide`, `MELL.decide_code` | public YES/NO and invalid code | public entry points |

`theories/Decision/Extract.v` remains the extraction root.  It names the four
public functions plus strict-decoder support.  OCaml dependency closure brings
in exactly the helper functions listed above.  The native audit runner is
compiled from that newly generated closure; no checked-in generated OCaml is
used.

## Fixture results

The executed manifest contains **53 fixtures**.  Result classification:

- **MATCH: 53**
- **MISMATCH: 0**
- **UNEXECUTED: 2**
- **NOT APPLICABLE: 1**

The 53 MATCH cases cover:

| Area | Cases | Result |
|---|---:|---|
| sequent/reach/run/semi/vector codecs | 10 | MATCH |
| RawRun evaluation | 7 | MATCH |
| SemiCode invariant checking | 4 | MATCH |
| Presburger decision | 6 | MATCH |
| unit/weight/goal/full saturation front ends | 9 | MATCH |
| BVAS/MELL stage and finite fuel | 8 | MATCH |
| arbitrary-precision nat/Z and signed action | 6 | MATCH |
| public `mell_decide`/`decide_code` | 3 | MATCH |

The exact input, expected text, and stable fixture names are in
`differential-cases.tsv` and `differential-case-names.txt`.  The gate reported
`runtime gate: 53/53 cases passed` after fresh extraction.

### Unexecuted cases

Two Gallina equations are kernel checked but are not counted as MATCH:

1. `decode_sequent (encode_sequent [Atom (2^80)])`: the native extracted
   decoder overflows the OCaml stack because `list_decode` uses a recursion
   fuel derived from the (very large) Gödel code.  The arbitrary-precision
   value itself is separately exercised by the direct `nat_codec` round trip
   and nat/Z arithmetic cases.
2. a duplicate two-component `SemiCode` round trip: the larger Cantor/list
   code causes the same extracted decoder stack limitation.  Duplicate data
   are still exercised by the sequent codec and duplicate-child RawRun.

Both observations are resource failures, not differing returned values.  They
are therefore UNEXECUTED, not MATCH or MISMATCH.  They remain callable runner
modes for diagnosis but are intentionally absent from the passing manifest.

### Not applicable

There is no malformed natural-number code rejected by `decode_run`: the
generic finite-tree codec is total on natural numbers.  Invalid proof
certificates are instead rejected by `eval_run` (bad action index, arity,
initial index, and negative intermediate configuration).  “Invalid RawRun
decoder code” is thus NOT APPLICABLE rather than an omitted rejection test.

## Integer and Presburger boundary

The extraction uses Coq 8.20.1's `ExtrOcamlNatBigInt` and
`ExtrOcamlZBigInt`, OCaml 4.14.2, and Zarith 1.14.  No fixed-width `int`
conversion is used for fixture data.  The tests include `2^80`, addition,
truncated natural subtraction, positive and negative `Z`, Euclidean division
`-7 / 3 = -3`, modulo `-7 mod 3 = 2`, and a signed BVAS update.

Presburger fixtures cover true/false existential and universal formulas, a
nested universal/existential formula, negative constants, and a divisibility
instance represented by an existential scaled equality.  They test the
Boolean decision result, not merely formula construction.

## Extraction trust boundary

Fresh extraction contains the previously audited **10** textual
`Obj.magic` occurrences generated by Coq's standard extraction of dependent
or erased types.  `scripts/check-extraction-output.sh` fails unless that exact
count remains stable and also rejects `AXIOM TO BE REALIZED`.  QA-3 adds no
custom `Extract Constant`, `Extract Inductive`, OCaml cast, axiom stub, or
mathematical oracle.  The runner accepts only its closed fixture names and
constructs values with the extracted constructors; it is not a general
untrusted decoder boundary.

The remaining trusted computing base includes Coq's extraction implementation,
the OCaml 4.14.2 compiler/runtime, Zarith 1.14 and GMP, plus the already
recorded standard-extraction casts.  The finite comparisons do not prove any
of those implementations correct.

## Gallina assumptions

The representative fixture declarations printed by the module are all
`Closed under the global context`.  No new axiom or choice principle is used.
The public mathematical theorems are unchanged; their existing
`Classical_Prop.classic` dependency is unaffected by these closed computation
examples.

## Verification record

- Focused Gallina fixture build: PASS.
- Fresh extraction policy scan: PASS; no custom override.
- Unrealized-axiom scan: PASS.
- Audited standard `Obj.magic` count: PASS (10).
- Extracted bytecode and native compilation: PASS.
- Differential fixture gate: PASS (53/53 MATCH cases).
- Full build, validate, dependency-closure `coqchk`, existing final/runtime/
  decision-path gates, source-policy scans: PASS.
- QA-2 isolated negative tests after the scope/Make changes: PASS; all 18
  injected faults were detected.
- Independent review found one initial fixture-construction discrepancy: the
  malformed ReachInstance runner encoded its empty dimension-1 system with
  `d = 0`, while Gallina used `d = 1`.  The runner was corrected to `d = 1`
  and the fresh 53-case gate passed again.
- Independent review after that correction: PASS.  The reviewer directly
  rechecked the named-input correspondence, manifest/name equality, fresh
  extraction ordering, public-definition stability, trust-boundary scans,
  protected files, and the final 53/53 log.

## Final assessment

The finite Gallina/OCaml differential scope is **PASS**.  This evidence
increases confidence that the actual extracted public path preserves the
tested computations.  It does not establish extraction correctness in general
or a practical time bound for the total decision procedure.
