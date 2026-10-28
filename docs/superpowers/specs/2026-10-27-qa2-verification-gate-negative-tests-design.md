# Task QA-2 Verification-Gate Negative-Test Design

## Intent

Demonstrate that the repository's verification gates reject representative
faults instead of merely passing the current good tree.  Fault injection is
confined to a disposable clone of the current HEAD; the mathematical sources,
public APIs, reduction, and decision procedure remain unchanged.

## Goals

- Check that a Coq type error survives shell pipelines as a nonzero result.
- Distinguish kernel acceptance of an axiom-dependent theorem from rejection
  by the repository's policy audit, and reject an unused `Axiom` as well.
- Keep tracked Coq sources, `_CoqProject`, compiled `.vo` artifacts, and the
  full `validate`/`coqchk` closure aligned.
- Reject wrong YES/NO expectations, omitted runtime cases, abnormal exits, and
  per-case timeouts.
- Regenerate extraction outputs from scratch before compiling or running them,
  and reject unapproved extraction directives and unrealized axioms.
- Record exact exit codes and diagnostic excerpts for every injected fault.

## Non-goals

- No new mathematical theorem, decision branch, optimization, or extraction
  mapping.
- No mutation of the user's main working tree during fault injection.
- No claim that `coqchk` alone enforces the project's axiom policy.
- No requirement to run the expensive negative suite as part of every build.

## Approaches considered

1. Inject faults directly into the working tree and restore them.  Rejected:
   this risks protected untracked work and violates the requested isolation.
2. Maintain separate permanently broken fixtures.  Rejected: broken Coq and
   OCaml files are easy to compile accidentally and create audit ambiguity.
3. **Chosen:** a driver creates a local temporary clone, overlays only the
   verification harness being tested, applies one reversible mutation at a
   time, records PASS/FAIL/PASS, and deletes the clone on exit.  This preserves
   source fidelity while keeping every negative test reproducible.

## Gate structure

`scripts/check-verification-scope.sh` compares every tracked `.v` source with
the `_CoqProject` manifest, requires the four public Audit bridge/example
modules, and optionally requires a normal `.vo` for every registered source
while rejecting `.vos`-only evidence.

`scripts/check-coq-source-policy.sh` scans every Git-tracked `.v` source for
forbidden axiom declarations and proof escapes.  This closes the policy gap
left by a final-theorem-only assumptions audit without confusing that policy
check with `coqchk`'s kernel-consistency role.

`scripts/audit-verification-gates.sh` owns the disposable clone and the fault
matrix.  It uses the repository's pinned local opam switch through a symlink,
never fetches dependencies, and restores a pristine fixture between faults.
The script reports each case as `DETECTED` only after a baseline pass, an
expected nonzero fault result, and a recovery pass.

The Makefile exposes the structural checker separately and the full negative
suite as `make audit-verification-gates`.  Runtime cases gain an exact count
and a per-case alarm.  Extraction deletes ignored generated `.ml`/`.mli` and
the extraction `.vo` before rebuilding, so stale OCaml cannot satisfy the
gate.

## Fault matrix

The matrix covers: Coq type error; imported used forbidden axiom; unused
forbidden axiom; omitted `_CoqProject` source; orphan tracked-like source;
missing `.vo`; `.vos` substituted for `.vo`; flipped YES; flipped NO; omitted
runtime case; same-count replacement by a duplicate case; abnormal runner
exit; runner timeout; `None` presented where NO is expected; unapproved
`Extract Constant`; generated `AXIOM TO BE REALIZED`; an extra `Obj.magic`;
and a stale extraction sentinel.  Runtime injections use a shortened timeout
but the same native gate logic.  The driver also asserts the exact matrix size
so deleting a test cannot turn 18/18 into a misleading 17/17.

## Trust and safety

The driver validates that its temporary path is below the system temporary
directory before cleanup.  It never stages, commits, resets, or cleans the
main repository.  Existing standard-extraction `Obj.magic` occurrences remain
the documented trust boundary; the new checks target only new overrides,
stubs, and stale artifacts.
