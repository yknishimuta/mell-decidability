# Task QA-3 Extraction Differential Design

## Intent

Compare concrete computations accepted by the Coq kernel with executions of
the corresponding functions freshly extracted by Coq 8.20.1 and compiled by
OCaml 4.14.2 with Zarith 1.14.  This is finite differential evidence, not a
formal proof of the extractor, compiler, or Zarith.

## Chosen approach

Three approaches were considered.  Extending the public extraction interface
with audit-only wrapper functions would make input sharing easy, but would
change the production extraction surface.  Generating OCaml expectations from
Coq output would reduce transcription, but would make the two sides share the
same result-producing pipeline.  The chosen conservative design keeps the
existing extraction declaration unchanged: a new Audit module proves explicit
closed Gallina equations, a hand-written runner reconstructs the same named
inputs and calls the existing extracted modules, and a checked TSV manifest
holds the independent expected rendering.

## Components

- `theories/Audit/ExtractionDifferentialExamples.v` defines named concrete
  fixtures and proves their Boolean/option/codec results by kernel reduction.
- `docs/review/extraction/differential_runner.ml` calls only freshly generated
  OCaml modules from the existing `Separate Extraction` closure.
- `docs/review/extraction/differential-cases.tsv` maps fixture names to explicit
  expected strings.  A separate required-name file prevents omission or
  replacement of mandatory fixtures.
- `make check-extraction-differential` builds the Coq examples, forces fresh
  extraction, compiles the runner, and compares every result with the manifest.

## Coverage

Fixtures cover sequent, ReachInstance, RawRun, and SemiCode codecs; valid and
invalid run evaluation; accepted and rejected invariant candidates;
Presburger quantifier/negation/integer cases; unit, weight, goal saturation,
full saturation, stage and fuel results; arbitrary-precision nat/Z operations;
signed vector updates; public decision functions and invalid code rejection.
Unsupported result branches are recorded as not applicable, and computations
that cannot finish within the bounded fixture suite are recorded as
unexecuted, never as matches.

## Invariants and trust boundary

No mathematical source, public theorem, decision definition, reduction,
extraction mapping, or generated OCaml file is edited.  The runner accepts
only enumerated fixture names.  Extraction output is deleted and regenerated
before compilation.  The existing exact audit of ten standard-extraction
`Obj.magic` occurrences and the prohibition on custom extraction directives
remain in force.  The result establishes only agreement on the recorded
finite inputs.
