# Final trust report (Task 12, current status)

Date: 2026-10-27

Status: **implementation, forced full build, kernel validation, extraction,
and required native runtime gates PASS; independent review is recorded
below.**

## Toolchain and baseline

- Git branch: `work/mell-formalization`
- Baseline HEAD: `29a672ab5a38c144c57f6d53e6f46b667236c89c`
- Coq: 8.20.1
- OCaml: 4.14.2
- Arithmetic runtime: Zarith arbitrary precision (`ExtrOcamlNatBigInt`,
  `ExtrOcamlZBigInt`)
- Zarith: 1.14
- YALLA: 2.0.6
- YALLA and vendored dependencies were not upgraded or patched.

## Public contracts checked

```coq
mell_decide : sequent -> bool
mell_decide_true_iff :
  forall Gamma, mell_decide Gamma = true <-> Provable Gamma
mell_decide_false_iff :
  forall Gamma, mell_decide Gamma = false <-> ~ Provable Gamma
mell_decide_with_cut :
  forall Gamma, mell_decide Gamma = true <-> ProvableWithCut Gamma
mell_stage : sequent -> nat -> option bool
mell_search_fuel : sequent -> nat -> option bool
mell_search_halts :
  forall Gamma, exists fuel answer,
    mell_search_fuel Gamma fuel = Some answer
decide_code : nat -> bool
decide_code_correct :
  forall code, decide_code code = true <->
    exists Gamma, decode_sequent code = Some Gamma /\ Provable Gamma
```

The Task 6F contracts `reduce_mell_correct`,
`reduce_mell_code_correct`, and `reduce_mell_many_one` retain their published
types.  The focused Task 12 statement audit reports only:

```text
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

for the final mathematical theorems.  No new axiom, admitted proof, choice
oracle, UIP/K, functional extensionality, or disabled kernel check was added.

The global `coqchk` context summary also lists axioms used elsewhere by Coq's
standard library and fixed third-party dependencies (including relational
choice, dependent choice, functional extensionality, and Eqdep).  They do not
occur in `Print Assumptions` for the final public theorems above.  This report
therefore distinguishes dependency-closure inventory from theorem-level
logical dependence.

## Extraction and OCaml audit

- `make -f Makefile.coq validate`: PASS
- forced `_CoqProject` rebuild (`make -f Makefile.coq -B -j2`): PASS
- full dependency-closure `coqchk -silent`: PASS
- `make check-final`: PASS
- `make audit-final`: PASS
- `make extract-final`: PASS
- `Separate Extraction reduce_mell`: PASS
- final four-function extraction: PASS
- generated closure: 67 `.ml` modules (plus interfaces)
- OCaml bytecode compilation: PASS
- `AXIOM TO BE REALIZED`: none
- fixed-width integer mapping: none
- runtime certificate path: alternating run-certificate and semilinear
  invariant checking remains present in `Stage`, `Invariant`, `Search`, and
  the Presburger dependency.

Coq reports `extraction-opaque-accessed` for five fixed YALLA
`Permutation_Type` lemmas while compiling the extraction driver.  The
standard extractor reads those opaque bodies because the runtime formula
translation uses YALLA's finite-multiset representation.  No declaration is
replaced by a stub, and the resulting modules compile and pass the native
tests; nevertheless opacity bypass by the standard extractor is recorded as
part of the extraction trust boundary rather than treated as a kernel theorem.

The optimized runtime also contains three proof-producing prechecks:

- a recursively checked positive-unit singleton fragment, whose successful
  result constructs a cut-free derivation using one, tensor, and promotion;
- zero-test-free stateful saturation, with exact fixed-point NO answers and
  bounded root-slice YES answers;
- a multiplicative-fragment sequent-weight refuter.

If neither precheck decides, execution uses the original total certificate
search.  These prechecks do not replace the termination proof or remove any
certificate from the fallback enumeration.

### `Obj.magic` ledger

The generated closure contains 10 occurrences; none is handwritten.

| Generated file | Count | Coq origin and reason | Public-path status |
|---|---:|---|---|
| `Vector.ml` | 2 | dependent elimination in `Vector.case0`/`caseS'`; erased length indices | reachable through `Vector.map2`; inputs originate from typed constructors or strict decoders |
| `BOrders.ml` | 3 | erased carrier of YALLA's singleton `BOrder` record and injected comparison | reachable through YALLA finite-multiset sorting |
| `fmformulas.ml` | 2 | erased formula carrier in `border_formula` and `FinMultiset` packaging | reachable from runtime MELL-to-ILZ context conversion |
| `yalla_ax.ml` | 3 | extracted atom/natural-number representation isomorphisms | representation adapter reachable from formula conversion |

There is no custom extraction override for these declarations, no generated
file was edited, and no arbitrary OCaml value is admitted through the public
runner.  Untrusted numeric input enters through `decide_code`, whose strict
decoder constructs typed Coq data or returns `None`.  This audit does not
claim the extracted closure is `Obj.magic`-free and treats the standard Coq
extractor plus these representation casts as part of the trusted runtime
boundary.

`ExtrOcamlNatBigInt` and `ExtrOcamlZBigInt` map Coq naturals and integers to
Zarith/GMP arbitrary-precision values.  Fixed-width OCaml `int` extraction is
not used.  A native regression checks signed arithmetic at `2^80`; a separate
negative-action regression exercises the extracted BVAS update path.  Zarith,
GMP, OCaml, and the extraction mappings are explicit trusted runtime
dependencies.

The standard extracted `Z.of_nat` path is structurally recursive through
`Pos.of_succ_nat`; applying a signed BVAS action directly to a `2^80` natural
therefore overflowed the OCaml stack in a diagnostic run.  This is a runtime
performance limitation, not a fixed-width overflow or a changed arithmetic
result.  The production small-regression matrix does not exercise such an
astronomical unary conversion; the limitation is retained here rather than
hidden or misreported as a successful action test.

Representative SHA-256 values:

```text
c123f10501073a7f4d69823ee9ef24eaf9cf185fc482dacbea99ca5dbb6dbf8b  ILZRuntime.v
f6d805b0a42a1c29ae1a05a0de212049f9df61b05744b08d0d9542865890e51b  MELLToABVASSRuntime.v
f501da529b16e80d10592ab8a818b2f9e0e142bb44674308e8291bf60c87fc42  ZeroTestFree.v
456af67f7a8d6b0f40d65fc11010be136c2ad5272b1128a7617bcbf16ec09eab  FiniteSaturation.v
e90d0bdc8230ae0cb170f42d6bc9d0dbdf0f8cb334f5b4393744d6ef7cf47fff  MultiplicativeWeight.v
6f74bbae9e165d3597b9c2f58de84994cce2d3cc0c1054ac34a5ad19622e4b96  UnitFragment.v
2591cb9434d75b9e8737bbe947bac61962bc8a6fdfd99bc3179b13ffadcce2ec  extracted MELL.ml
eef37a85a718f88992e90cf46ae3f2468ced6ae85ec93dd0181a11692e58c232  extracted Main.ml
```

## Runtime results

| Test | Result |
|---|---|
| BVAS initial configuration | `true` |
| BVAS empty initial set | `false` |
| invalid sequent code 16 | `false` |
| MELL `[One]` | `true` (0.72 s) |
| MELL atom/dual identity | `true` (0.02 s) |
| MELL tensor units | `true` (0.31 s) |
| MELL par identity | `true` (0.02 s) |
| MELL `Bang One` | `true` |
| MELL empty sequent | `false` (0.01 s) |
| MELL `[One; One]` | `false` (0.01 s) |
| BVAS unary `+2` | `true` |
| BVAS binary sum | `true` |
| BVAS even-only / odd target | `false` |
| BVAS dimension-0 empty system | `false` |
| direct / encoded MELL result | equal |
| malformed vector/integer/action/reach-instance codes | rejected |
| signed arithmetic at `2^80` | `true` |
| negative signed BVAS action | `true` |

No required runtime case timed out.  The runner still distinguishes `None`
from `false`; timeouts are not reported as NO.  The kernel theorem proving
totality remains distinct from a resource bound for extracted execution.

## Performance repair

The original `[One]` reduction timed out because generic zero-test layering
expanded a test-free machine to 64,516 states.  The proved direct conversion
reduces it in 0.20 seconds.  Subsequent measurements isolated Gödel-code
enumeration as the remaining bottleneck; the verified positive-unit checker,
finite saturation, and multiplicative weight invariant resolve the required
small examples while retaining the complete fallback.  See
`t12-runtime-performance-audit.md`.

## Independent review

The independent read-only reviewer first found the missing exponential
runtime case, incomplete codec/BVAS gate, and two ledger errors.  After the
general `UnitFragment` proof constructor and the expanded 22-case native gate
were added, the reviewer confirmed the implementation, kernel checks, and
native gate.  The remaining documentation discrepancies (closure count,
per-file cast counts, and hashes) were corrected from the generated artifacts.
The final independent-review result is PASS with no unresolved finding.
