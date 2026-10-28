# Task 12 extraction dependency repair

Date: 2026-10-26

## Failure and direct cause

With Coq 8.20.1, `Separate Extraction reduce_mell` originally failed with:

```text
The informative inductive type prod has a Prop instance
in ILZ.YM.mell2ll_map_wn_inv.
Extraction cannot handle this situation yet.
```

The failure was reproduced with `reduce_mell` alone.  The executable
translation used definitions hosted in `Yalla.mell_mset`; modular extraction
therefore inspected proof declarations from that module, including the
Prop-instantiated product above.  The failing declaration is not used by the
runtime algorithm.  This was a module-level dependency (case C), rather than
an execution-time call to `mell2ll_map_wn_inv`.

## Repair

The executable dependency graph was split into:

- `Reduction/ILZRuntime.v`: direct MELL-to-linear-formula translation,
  freshness, ILZ goal construction, decidable formula equality, and finite
  subformula enumeration.  It imports `Yalla.fmformulas` and `Yalla.nn_def`,
  but not `Yalla.mell_mset`.
- `Reduction/MELLToABVASSRuntime.v`: finite support/state/rule enumeration and
  the full-zero-test machine compiler.
- `Reduction/FullZeroSystem.v`: the shared finite full-zero-test machine data.

`Reduction/ILZ.v` remains the proof-side YALLA bridge.  It proves:

```coq
classical_linear_sequent_reference :
  forall Gamma,
    classical_linear_sequent Gamma =
    map Yalla.mell_mset.mell2ll (elts (to_yalla_sequent Gamma))
```

The runtime and reference machine compilers are definitionally equal, exposed
as:

```coq
compile_ilz_machine_runtime_eq :
  forall goal,
    Mell.Reduction.MELLToABVASSRuntime.compile_ilz_machine goal =
    compile_ilz_machine goal
```

Consequently no new local ILZ datatype was needed.  Public `reduce_mell` now
uses `translate_mell_runtime` and the runtime compiler directly; the existing
YALLA correctness proof remains proof-only.

## Verification performed

- `ILZ.v`, `MELLToABVASS.v`, `MELLToABVASSCompleteness.v`, `ZeroTest.v`, and
  `Main.v` compiled after the split.
- `Separate Extraction reduce_mell` succeeded.
- Extraction of `mell_decide`, `decide_code`, `mell_stage`, and
  `mell_search_fuel` succeeded.
- The generated 67-module OCaml closure compiled with OCaml 4.14.2.
- No `AXIOM TO BE REALIZED` occurs in the generated code.

The extraction driver uses Coq's standard `ExtrOcamlNatBigInt` and
`ExtrOcamlZBigInt` mappings.  These map both numeric types to Zarith arbitrary
precision integers; the forbidden fixed-width `ExtrOcamlNatInt` and
`ExtrOcamlZInt` mappings are not used.

The extracted closure contains 10 standard-extractor `Obj.magic` occurrences:
3 in `BOrders.ml`, 2 in `fmformulas.ml`, 3 in `yalla_ax.ml`, and 2 in
`Vector.ml`.  They are individually classified in the final trust report.
No cast was handwritten, no generated OCaml was patched, and no `Extract
Constant` or axiom stub was added.  The vector casts are on public execution
paths and rely on the Coq vector-length invariant; the YALLA finite-multiset
and atom representation casts are generated representation adapters used by
the runtime translation.  This report therefore does not claim that the
closure is `Obj.magic`-free or that Coq's extraction implementation is proved
by the kernel.

## Runtime repair

The unconditional zero-test layering was replaced, under a proved empty-test
guard, by `direct_bottom_up`.  Verified stateful saturation and a
positive-unit proof constructor plus a multiplicative-fragment weight refuter
now provide bounded fast answers before the unchanged complete search.
Required extracted MELL YES/NO examples, including `[Bang One]`, now finish
without timeout or runtime error; detailed timings and machine sizes are in
`t12-runtime-performance-audit.md`.
