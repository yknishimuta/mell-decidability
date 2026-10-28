# Task QA-2: verification-gate negative tests

Date: 2026-10-27

Baseline: `87ecb68038a2a1eba2af1a3e206ab4eff59ef3cb`

## Scope and method

This audit tests whether the verification infrastructure rejects faults.  It
does not change a Gallina definition, theorem, MELL reduction, decision
algorithm, or extraction mapping.

`make audit-verification-gates` creates a dedicated local clone below the
system temporary directory, links the repository's pinned opam switch, and
overlays only the QA-2 verification harness under test.  Every mathematical
source comes from the cloned HEAD.  Each case runs a good baseline, applies one
fault inside the clone, requires a nonzero result, restores the fixture without
`git reset` or `git clean`, and requires the same gate to pass again.  The
temporary clone is removed on exit.  The main worktree and its protected
untracked files are never mutated.

## Corrections made to the gates

1. `check-verification-scope.sh` compares all tracked `.v` files with all
   `_CoqProject` entries.  It explicitly requires `PaperFidelityBridges`,
   `PaperFidelityExamples`, `DecisionPathAudit`, and `DecisionPathExamples`.
   Its artifact mode requires a normal `.vo` for every registered source and
   rejects `.vos` as a substitute.
2. `check-coq-source-policy.sh` rejects `Axiom`, `Admitted`, `admit`, and
   `Abort` declarations across every Git-tracked `.v`, including modules that
   are not dependencies of the final decision theorem.  This complements,
   rather than replaces, `Print Assumptions` for the public theorem closure.
   `check-assumption-allowlist.sh` also parses the actual public
   `Print Assumptions` transcript and accepts only `Classical_Prop.classic`.
3. Runtime expectations and their independently checked mandatory name sets
   are stored in explicit manifests.  The common
   runner requires exactly 22 public runtime cases and 11 decision-path cases.
   A missing row can no longer yield a misleading successful aggregate.
4. Every runtime case has a configurable wall-clock alarm, defaulting to 60
   seconds.  A timeout is reported as `TIMEOUT` and fails with status 142;
   abnormal termination preserves a nonzero status; the literal result
   `None` cannot equal the expected `false`.
5. `extract-final` deletes ignored generated `.ml`/`.mli` files and the
   extraction `.vo` before rebuilding.  Old OCaml output therefore cannot
   satisfy the target after a changed or broken Coq extraction source.
6. Extraction policy rejects new `Extract Constant`/`Extract Inductive`
   directives.  Output audit rejects `AXIOM TO BE REALIZED` and enforces the
   already reviewed total of ten standard-extraction `Obj.magic` occurrences.
7. The existing Makefile already sets Bash `-eu -o pipefail`.  The injected
   Coq error confirms that the `coqc | tee` path exits nonzero in practice.

## Fault-injection results

All baseline and recovery runs exited 0.  The table records the injected
fault's exit code and the decisive diagnostic.

| # | Gate | Injected fault | Fault exit | Detection evidence |
|---:|---|---|---:|---|
| 1 | source scope | removed `PaperFidelityBridges.v` from `_CoqProject` | 1 | `tracked but not registered` |
| 2 | source scope | added a tracked orphan `QA2Orphan.v` | 1 | orphan listed as unregistered |
| 3 | Coq build | appended `Check (0 : bool)` | 2 | Coq reports nat/bool type error; `check-final` fails through `tee` |
| 4 | artifact scope | removed `DecisionPathAudit.vo` | 1 | `.vos is not complete evidence` |
| 5 | artifact scope | replaced the same `.vo` by `.vos` | 1 | `.vos` explicitly rejected |
| 6 | axiom audit | public audit theorem imports an axiom from a separately compiled, untracked test module | 2 | Coq accepts and prints the dependency; assumptions allowlist rejects `qa2_forbidden_used` although the tracked-source scan cannot see its declaration |
| 7 | source policy | unused `qa2_forbidden_unused` in that non-final module | 2 | Coq accepts; repository-wide forbidden-declaration scan rejects it |
| 8 | runtime YES | changed `mell-one` expected value to false | 1 | actual true differs from expected false |
| 9 | runtime NO | changed `mell-empty` expected value to true | 1 | actual false differs from expected true |
| 10 | runtime completeness | removed one mandatory runtime row | 1 | `expected 22 cases, executed 21` |
| 11 | runtime identity | replaced a mandatory row with a duplicate while retaining 22 rows | 1 | duplicate/name-set mismatch rejected |
| 12 | runtime process | fixture runner exits 7 | 7 | `RUNTIME_ERROR(7)` |
| 13 | runtime timeout | fixture runner exceeds a one-second limit | 142 | `TIMEOUT` |
| 14 | result classification | fixture runner prints `None` where false is expected | 1 | `None` is a mismatch, not NO |
| 15 | extraction source | inserted an unapproved `Extract Constant` | 1 | directive and source location printed |
| 16 | extraction output | inserted `AXIOM TO BE REALIZED` | 1 | unrealized axiom printed and rejected |
| 17 | extraction trust | inserted an eleventh `Obj.magic` | 1 | audited count changes from 10 to 11 |
| 18 | extraction freshness | left a stale sentinel and broke `Extract.v` | 2 | stale files are deleted; fresh extraction fails at the Coq error instead of compiling old OCaml |

Result: **18/18 injected faults detected**, with baseline PASS and post-restore
PASS for every case.

## Completeness and coqchk boundary

At the baseline there are 268 Git-tracked Coq sources and exactly 268
`_CoqProject` source entries.  The full Makefile-generated `validate` target
passes all registered `.vo` files to `coqchk -silent`; the structural checker
prevents a tracked source from disappearing from that closure.  Artifact mode
ensures the evidence is `.vo`, not proof-skipping `.vos`.

`coqchk` establishes kernel consistency of compiled objects; it intentionally
does not enforce the project's axiom allowlist.  That policy remains a
separate `Print Assumptions` and forbidden-source audit.  The used-axiom test
demonstrates this distinction explicitly.

## Runtime and extraction boundary

The negative runtime fixture tests only the common fail-closed harness.  The
normal final gates separately compile the actual extracted runner and execute
all 22 result cases and 11 decision-path cases.  `None`, timeout, and process
failure remain distinct from false.

The exact count of ten existing `Obj.magic` occurrences is not a claim that
the extraction is cast-free.  It prevents an unreviewed additional cast while
retaining the trust boundary recorded in `final-trust-report.md`.  A deliberate
future extraction change that legitimately changes this count must update the
trust audit and this explicit expectation together.

## Remaining limitations

- The negative suite uses the platform's Perl implementation for per-case
  alarms and therefore records Perl plus the OCaml toolchain as operational
  test dependencies.
- Files ignored by Git and absent from `_CoqProject` are intentionally outside
  the formal source closure; this includes protected local caches.
- A source-level forbidden-token scan is a policy check, not a substitute for
  reviewing `Print Assumptions`.  Both are retained.
- The negative suite is intentionally opt-in because it performs a full build
  and repeated audit/extraction cycles in its temporary clone.

## Final verification

The following fresh checks passed on 2026-10-27:

- isolated negative suite: 18/18 injected faults detected; every baseline and
  post-restore check passed;
- source/artifact scope: 268 tracked sources exactly matched 268
  `_CoqProject` entries, and every entry had a normal `.vo`;
- forced full `Makefile.coq` rebuild: exit 0;
- `make -f Makefile.coq validate`: exit 0, including the complete registered
  `coqchk -silent` closure;
- `make check-final` and `make audit-final`: exit 0; the reported public
  theorem dependency remained `Classical_Prop.classic` only;
- `make extract-final`: fresh extraction, policy/output audit, and OCaml
  compilation passed; no unrealized axiom and exactly ten reviewed
  standard-extraction `Obj.magic` occurrences;
- `make check-runtime-mell`: 22/22 cases passed;
- `make check-decision-paths`: 11/11 cases passed.

The forbidden scans, final diff checks, and independent review are recorded
after review completion and before the local QA-2 commit.  The independent
review initially found three real omissions: the absence of a parsed
`Print Assumptions` allowlist, incomplete repository-wide unused-axiom
detection, and count-only runtime manifest validation.  All three were fixed;
the reviewer then re-ran the relevant read-only checks and returned PASS with
no substantive findings.  The final forced rebuild and `validate`/`coqchk`
rerun after those corrections both exited 0.
