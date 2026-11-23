# MELL Audit Remediation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Correct paper/provenance overclaims and make the final proof-safety audit fail closed on unauthorized assumptions and unsafe kernel exceptions.

**Architecture:** Keep the mathematical sources unchanged. Add one standard-Python audit program with explicit subcommands for `Print Assumptions`, `coqchk -o`, and Coq source safety directives; retain the existing shell entry points as thin compatibility wrappers, connect every check to `audit-final`, and extend the disposable-clone fault-injection suite so failures are proved to arise from the intended audit rule.

**Tech Stack:** Coq 8.20.1, Bash, Python 3 standard library (`argparse`, `pathlib`, `unittest`), GNU Make, Git disposable clones.

**Spec:** `codex_mell_audit_fix_instructions_20261123.md`

## Global Constraints

- Start from `9f97cc77ca89c2077bf9a2aba50320016f5c102c` on dedicated branch `audit/mell-remediation-20261123`.
- Do not change existing mathematical definitions or proofs under `theories/` unless a verified blocker requires an independent audit bridge.
- Allow each audited theorem only an empty global context or exact dependency `Classical_Prop.classic`.
- Fail closed on missing, empty, truncated, mismatched, or unknown audit output.
- Scan all project-managed tracked `.v` files while excluding external `vendor/` sources consistently with the project audit boundary.
- Do not add dependencies, push, merge, weaken audit scope, or introduce unconditional exceptions.

## Review Focus

- A valid Coq identifier containing apostrophes must be parsed and rejected when unauthorized.
- A multiline assumption type must remain attached to its dependency and must not be mistaken for a second dependency.
- A transcript with the right number of blocks but the wrong theorem identity/order must fail.
- Coq comments, nested comments, and string literals mentioning unsafe commands must not trigger the source policy.
- `coqchk -o` output must fail if any required section is missing, renamed, truncated, or contains a non-`<none>` entry.

---

### Task 1: Characterize the existing false PASS

**Files:**
- Test: temporary fixtures under `/tmp` only
- Read: `scripts/check-assumption-allowlist.sh`, `scripts/check-coq-source-policy.sh`, `Makefile`, `theories/Audit/Statements.v`

**Interfaces:**
- Consumes: current `audit-final` log and the eight `Print Assumptions` commands in `Statements.v`.
- Produces: captured reproduction logs and a root-cause statement used by Tasks 2–4.

- [x] Reproduce the apostrophe-bearing `Parameter forbidden' : False` false PASS against the individual allowlist and full `audit-final` in a disposable clone.
- [x] Reproduce the `nonterminating is assumed to be guarded.` false PASS and inspect actual Coq/coqchk output formats.
- [x] Confirm the root causes: permissive line regex, no block identity/completeness contract, absent full-object coqchk validation, and partial raw-text source scan.

### Task 2: Fail-closed assumptions parser

**Files:**
- Create: `scripts/check_coq_audit.py`
- Create: `tests/test_check_coq_audit.py`
- Modify: `scripts/check-assumption-allowlist.sh`
- Modify: `theories/Audit/Statements.v`

**Interfaces:**
- Consumes: `assumptions AUDIT_LOG EXPECTED_MANIFEST`, exact allowed name `Classical_Prop.classic`, explicit begin/end markers emitted by `Statements.v`.
- Produces: exit 0 only when every expected theorem has exactly one complete block and every dependency is allowed; diagnostics name the theorem and offending line/dependency.

- [x] Write fixture tests for closed terms, classic-only, apostrophe identifiers, qualified identifiers, multiline types, guard assumptions, missing/empty/truncated logs, missing/duplicate/wrong markers, and unknown dependency syntax.
- [x] Run `python3 -m unittest tests.test_check_coq_audit` and verify failures occur because the parser does not yet exist.
- [x] Implement the smallest marker-aware parser and exact allowlist needed for those tests.
- [x] Add stable audit markers around each `Print Assumptions` command and the expected theorem manifest.
- [x] Run unit tests and the normal real transcript; require PASS with eight matched theorem blocks.

### Task 3: Coq source safety scanner

**Files:**
- Modify: `scripts/check_coq_audit.py`
- Modify: `scripts/check-coq-source-policy.sh`
- Test: `tests/test_check_coq_audit.py`

**Interfaces:**
- Consumes: `source-policy` plus tracked project `.v` paths supplied by Git, excluding `vendor/`.
- Produces: rejection of proof escapes, top-level `Axiom`/`Parameter`, and unsafe settings outside comments/strings, without rejecting `Module Type` signature parameters.

- [x] Add failing tests for global `Parameter`, `Axiom`, `Admitted`, `admit`, `Abort`, four unsafe settings, nested comments/strings, and a legitimate `Module Type` parameter.
- [x] Implement lexical stripping and conservative command classification; unknown scanner state fails closed.
- [x] Run unit tests and the repository-wide tracked-source scan.

### Task 4: Structured coqchk safety audit and Make integration

**Files:**
- Modify: `scripts/check_coq_audit.py`
- Modify: `Makefile`
- Test: `tests/test_check_coq_audit.py`

**Interfaces:**
- Consumes: `coqchk` output file created with `coqchk -silent -o PATH` and three exact required headings: type-in-type, unsafe (co)fixpoints, and positivity assumed.
- Produces: exit 0 only when all headings occur exactly once and each section is `<none>`; `audit-final` executes unit tests, assumptions audit, source audit, and coqchk safety audit.

- [x] Add failing fixtures for all-empty valid output, each unsafe section populated, missing/duplicate sections, and malformed/truncated output.
- [x] Implement the parser and run unit tests green.
- [x] Add a full registered-object `coqchk` invocation and parser call to `audit-final`; preserve pipefail and logs.
- [x] Run focused `audit-final` on the unchanged project and require PASS.

### Task 5: Disposable negative integration suite

**Files:**
- Modify: `scripts/audit-verification-gates.sh`
- Modify: `docs/review/verification-gate-negative-tests.md`

**Interfaces:**
- Consumes: disposable local clone, overlaid audit files, pinned `_opam`, and per-case expected diagnostic substrings.
- Produces: baseline/fault/recovery status plus evidence that apostrophe and guard faults fail both the individual gate and `make OPAMEXEC= audit-final` for the intended reason.

- [x] Add a diagnostic-aware `run_phase` helper that rejects failure for the wrong reason.
- [x] Add individual fixture cases for valid outputs, unauthorized axiom/parameter, apostrophe parameter, guard assumption, log integrity failures, unknown format, coqchk unsafe output, and source unsafe settings.
- [x] Add compiled disposable-clone integration cases for apostrophe and unsafe fixpoint faults, ensuring sources are registered and compiled before audit rejection.
- [x] Run the negative suite and require every baseline/recovery PASS and every injected fault DETECTED with its expected diagnostic.

### Task 6: Paper fidelity and provenance corrections

**Files:**
- Modify: `docs/review/arxiv-2607.09558v1-fidelity-audit.md`
- Modify: `docs/mathematical-provenance.md`
- Modify only if the same claim occurs: `README.md`, related review documents

**Interfaces:**
- Consumes: S1 arXiv:2607.09558v1, S2 FoSSaCS 2026 paper, S4 Lazić–Schmitz author PDF, and public Coq theorem types/call sites.
- Produces: corrected D01–D06 and conservative classifications for F01–F03 plus Lemma 4.3, Corollary C.3, and S2 Lemma 6.

- [x] Verify each source page and each linked public Coq declaration/call site.
- [x] Correct the six mandatory factual errors and preserve the known statement/proof repair ledger.
- [x] Replace overbroad EXACT/EQUIVALENT labels with `necessary nonnegative specialization`, `sufficient special case`, or `sufficient existential alternative` where applicable.
- [x] Search all tracked prose for repeated stale claims and make only necessary consistency edits.

### Task 7: Final verification, remediation record, and commit

**Files:**
- Create: `docs/review/audit-remediation-20261123.md`
- Modify: this plan's checkboxes as completed

**Interfaces:**
- Consumes: all prior tasks and fresh logs from the current branch.
- Produces: reproducible audit record, clean targeted diff, and one local commit.

- [x] Run `coq_makefile -f _CoqProject -o Makefile.coq` and `make -f Makefile.coq -j2` (plus a forced `-B` full rebuild).
- [x] Run `make -f Makefile.coq validate` and parse the resulting coqchk safety report.
- [x] Run `make OPAMEXEC= audit-final`, `bash scripts/check-verification-scope.sh --require-vo`, and the three required runtime/differential targets.
- [x] Run the complete negative suite and confirm apostrophe/guard integration failures contain the intended audit diagnostics.
- [x] Write the remediation record with before/evidence/after/result sections and exact exit codes.
- [x] Inspect `git diff --check`, final diff, tracked/untracked status, and changed-file scope; preserve the user-provided instruction file as untracked.
- [x] Commit only authorized deliverables locally and record the commit ID; do not push or merge.
