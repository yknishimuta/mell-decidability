# Audit remediation record — 2026-11-23

## Scope and baseline

- Repository baseline: `9f97cc77ca89c2077bf9a2aba50320016f5c102c`
- Working branch: `audit/mell-remediation-20261123`
- Pinned prover used for verification: Coq 8.20.1 from the repository `_opam`
- The pre-existing user instruction file
  `codex_mell_audit_fix_instructions_20261123.md` remained untracked and was
  not modified or committed.
- No mathematical definition or proof was changed.  The only `.v` change adds
  audit transcript markers around existing `Print Assumptions` commands in
  `theories/Audit/Statements.v`.

## Source-fidelity and provenance corrections

The previous tables overstated or misidentified several correspondences.
The fixed primary sources are BLS arXiv:2607.09558v1, the FoSSaCS 2026 paper,
and Lazić–Schmitz 2015, as registered in
[`docs/mathematical-provenance.md`](../mathematical-provenance.md).

The corrected tables now record:

- BLS Remark 3.4 (p. 7) concerns semilinearity of reachability in dimensions
  `d <= 5`; it is unformalized and is not the general search procedure.
- Appendix A already defines `Q_s = f_s(P) intersection N^d`.  R11 makes the
  transported-periodic-order/componentwise-order argument explicit; it does
  not add a missing orthant restriction.
- Remark 3.11 (p. 9) warns that all runs with unfixed initial values are not
  WQO because distinct one-leaf values form an antichain.
- Lemma 4.6 already applies marker-total-one before projection in the paper.
  `DoubledRestriction H` additionally carries arbitrary semilinear `H` through
  the construction.
- Fact B.4 maps directly to `Mell.BVAS.Amalgamation.context_embed`;
  `context_lift` is the separate validity-preserving replacement theorem.
- Lazić–Schmitz Proposition 7(2) includes the ordinary LL/MELL route.  This
  repository is not labelled an exact formalization because translation
  packaging differs and the polynomial-space analysis is not formalized.
- BLS Lemma 4.5 is exposed as the downstream-needed nonnegative `NRelation`
  specialization, not the paper's full signed statement.
- BLS Lemma 5.5 is exposed for
  `SimulationInvariant S code = Reach(S) union denote(code)`.  The calls in
  `SafeLinearization.v` establish the needed extensional equality and closure;
  the public theorem is not an arbitrary-`I` version.
- FoSSaCS Proposition 5 is an existential merged-run alternative sufficient
  for Lemma 8; its public type does not equate the witness with the paper's
  specified pointwise concatenation.
- The tables also distinguish the signed/nonnegative Lemma 4.3 interfaces,
  one-stitch versus finite iteration for Corollary C.3, and the single checked
  implication rather than the full FoSSaCS Lemma 6 biconditional.

Existing source-proof corrections remain protected and separately described:
the same-action correction for Fact B.3, the strict-coefficient equality for
Lemma 4.5, difference normalization for Lemma 6.10, and corrected `extract`
argument order before Lemma 6.11.

## Proof-safety gate remediation

### Previous false PASS

The old assumptions scan recognized only colon-terminated names made from
alphanumerics, `_`, and `.`, so it ignored a legal Coq apostrophe identifier
such as `forbidden'`.  It also ignored the colon-free message
`nonterminating is assumed to be guarded.`.  The audit transcript had no
machine-checked theorem identity/count framing, and `audit-final` checked the
`coqchk` exit status but did not inspect its safety-exception sections.

Both supplied probes were reproduced before the change: their registered and
compiled `audit-final` runs exited 0.

### New behavior

`scripts/check_coq_audit.py` is a fail-closed standard-Python checker with
three subcommands:

1. `assumptions` requires exactly the manifest-listed marker blocks, accepts
   only the exact dependency `Classical_Prop.classic` (or a closed term),
   handles apostrophes and continuation lines, and rejects missing, empty,
   truncated, duplicate, reordered, or unknown output.
2. `source-policy` lexes nested Coq comments and strings, then rejects global
   `Axiom`/`Parameter`, proof escapes, and unsafe checking directives.  A
   `Parameter` inside `Module Type` remains valid.
3. `coqchk` requires one context summary and requires all of type-in-type,
   unsafe `(co)fixpoints`, and assumed positivity to be present and `<none>`.

The source-policy auxiliary scan covers all 265 Git-tracked project-managed
`.v` files and intentionally excludes `vendor/**`.  The 269-source build,
dependency, and kernel checks still include the registered vendor sources.

`audit-final` now runs the 29 parser/scanner unit tests, marker-aware assumption
checking, the source policy, extraction policy, full `coqchk`, and the
fail-closed `coqchk` summary parser.

## Verification results

All commands below were executed on this branch on 2026-11-23.  Exit codes are
the observed process exit codes, not inferred from old logs.

| Command | Exit | Result |
|---|---:|---|
| `PATH="$PWD/_opam/bin:$PATH" coq_makefile -f _CoqProject -o Makefile.coq` | 0 | Makefile regenerated. |
| `PATH="$PWD/_opam/bin:$PATH" make -B -f Makefile.coq -j2` | 0 | Forced full rebuild of all registered sources. |
| `PATH="$PWD/_opam/bin:$PATH" make -f Makefile.coq validate` | 0 | Kernel validation passed. |
| `PATH="$PWD/_opam/bin:$PATH" make OPAMEXEC= audit-final` | 0 | 29 unit tests, 8 marked theorem blocks, source/extraction policy, and kernel safety parser passed. |
| `bash scripts/check-verification-scope.sh --require-vo` | 0 | 269 tracked sources match `_CoqProject`; every source has a normal `.vo`. |
| `PATH="$PWD/_opam/bin:$PATH" make OPAMEXEC= check-runtime-mell check-decision-paths check-extraction-differential` | 0 | Runtime 22/22, decision paths 11/11, differential 53/53. |
| `PATH="$PWD/_opam/bin:$PATH" bash scripts/audit-verification-gates.sh` | 0 | 36/36 injected faults detected, with successful baseline and recovery checks. |

The final `coqchk` context summary reports all three required exception
sections as `<none>`:

- constants/inductives relying on type-in-type;
- constants/inductives relying on unsafe `(co)fixpoints`;
- inductives whose positivity is assumed.

The eight audited public theorem blocks each depend only on the exact printed
name `Classical_Prop.classic`.

## Negative-test reason checks

The complete negative suite checks both individual parsers and disposable
registered/compiled repository copies.  In particular:

- the apostrophe probe reached `audit-final` after successful registration and
  compilation, then failed with exit 2 because
  `forged_claim: unauthorized assumption: forbidden'`;
- the unsafe-fixpoint probe reached `audit-final` after successful registration
  and compilation, then failed with exit 2 because
  `inherited_false: unrecognized dependency output: nonterminating is assumed to be guarded.`;
- a synthetic `coqchk` unsafe-fixpoint section failed with the named constant;
- an unused global axiom was accepted by the kernel but rejected by the source
  policy, demonstrating that the failure is not merely a compilation error;
- empty, missing, truncated, missing-theorem, unknown-format, type-in-type,
  positivity, universe-checking, and manifest/scope faults all failed closed;
- valid `Module Type` parameters and normal closed/classical transcripts pass.

Detailed cases and their intended diagnostics are maintained in
[`verification-gate-negative-tests.md`](verification-gate-negative-tests.md).

## Remaining limitations

- The assumption transcript parser intentionally accepts only the output forms
  covered by its explicit grammar.  A future incompatible Coq output format
  will fail closed and require a reviewed parser update.
- The source-policy scan excludes reproduced external `vendor/**` source by
  policy; vendor objects remain in the full build and `coqchk` closure.
- The documentation now records, rather than fills, the deliberate
  formalization-scope gaps: the full signed Lemma 4.5, arbitrary-`I` Lemma 5.5,
  specified pointwise Proposition 5 construction, full FoSSaCS Lemma 6
  biconditional, and polynomial-space complexity analysis are not exported.
