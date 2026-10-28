# T10-E0 stateful amalgamation audit

## Scope and source

- Baseline: branch `work/mell-formalization`, HEAD
  `0f57832b7b23a17ab737b5ce8acf0a76d8444cca`.
- Source: Bizière--Leroux--Sutre, *Bridging the Gap Between Plain VASS and
  Branching VASS*, FoSSaCS 2026, LNCS 16503, pp. 65--87.  The formalized
  contracts correspond to Definition 4/Proposition 5 and Lemma 8.
- This task does not implement Extend, Lemma 9, the bounded-depth compiler,
  Theorem 12, or Corollary 14.

## Representation and invariants

`run_node_count` counts one node for a leaf and one node plus the counts of
the children for an internal run.  The `SRuns` cons/nil encoding is not
counted.  The counter conserved by the exact equations is
`snd (root_config rho)`, not a sum of counters over all nodes.

`SRunPath` is occurrence-sensitive: its child constructor retains the
`before` and `after` child lists.  Thus equal duplicate children remain
distinct.  `replace_subrun_at` changes only the designated occurrence and
adds the nonnegative delta to its strict ancestors.

The local two-stage theorem `amalgamate_context_extensions` uses translated
context plugging through two exact subrun replacements.  It assumes only the
hereditary/root inequalities supplied by `ContextOrder`; it does not require
each local context effect to be nonnegative.

## Mutual induction

`inserted_family_amalgamation_mut` is a mutual theorem over
`SContextFamily` and `SContextFamilies`.

- The run case recursively amalgamates corresponding child families,
  rebuilds the common root rule, proves the exact root-counter and node-count
  core equations, and supplies every premise of
  `amalgamate_context_extensions`.
- The runs case uses `PositionalContextOrders`.  Its cons case combines the
  head and tail witnesses without quotienting, sorting, or deduplicating, so
  child order, occurrence, and multiplicity are retained.
- Hereditary positivity is projected to children and used to derive the
  necessary cumulative inequalities.  No stronger local-effect hypothesis
  is introduced.

## Public results

`stateful_context_order_amalgamation` has the exact conclusion

```text
exists gamma,
  ValidSRun B gamma /\
  ContextOrder B alpha gamma /\
  ContextOrder B beta gamma /\
  c(sigma) + c(gamma) = c(alpha) + c(beta) /\
  N(sigma) + N(gamma) = N(alpha) + N(beta).
```

The actual family insertion results may be unordered-isomorphic to `alpha`
and `beta`.  `srun_isomorphic_sym_stateful`, validity transport, identity
families, and `context_order_trans` perform this transport.  Root counters
and paper node counts are rewritten only with proved isomorphism invariance.

`stateful_context_transfer_lemma_8` takes an explicit
`path : SRunPath beta nu`.  Exact amalgamation produces `nu'`; root monotonicity
of `sigma <= alpha` yields a nonnegative `delta`; cancellation in the exact
counter square gives `c(nu') = c(nu) + delta`.  The existing exact replacement
theorem then constructs `beta'` and proves

```text
c(alpha) + c(beta) = c(sigma) + c(beta')
N(alpha) + N(beta) = N(sigma) + N(beta').
```

The signs are therefore “new subrun minus old subrun”, and both root states
are preserved in the theorem statement.

## Verification

Environment: Coq 8.20.1, OCaml 4.14.2, local opam switch.

- Focused source and audit build: PASS (`make audit-t10-e0`).
- T09 bridge regression: PASS, run directly without overwriting protected
  historical audit logs.
- T10-G concrete finite-cover audit: PASS.  The concrete theorems retain only
  the documented `Classical_Prop.classic` dependency; no
  `ClassicalEpsilon.constructive_indefinite_description` is reintroduced.
- Forced complete `_CoqProject` build: PASS
  (`make -B -f Makefile.coq -j2 all`).
- Kernel check: PASS for `Mell.BVASS.StatefulAmalgamation` and
  `Mell.Audit.StatefulAmalgamationExamples`.
- `Print Assumptions`: `subrun_replacement_exact`,
  `amalgamate_context_extensions`, `inserted_family_amalgamation`,
  `stateful_context_order_amalgamation`, and
  `stateful_context_transfer_lemma_8` are all closed under the global context.
- Forbidden scan: no new Axiom, `Admitted`, `admit`, `Abort`,
  `ClassicalEpsilon`, choice oracle, UIP/K, `Eq_rect_eq`, or functional
  extensionality.
- Target-only `git diff --check`: PASS.  A repository-wide check still reports
  trailing whitespace in protected pre-existing audit-log diffs; those files
  were not edited or staged by Task 6E0.

The universal proofs cover leaves, empty child lists, multiple/duplicate
children, unordered isomorphism, arbitrary signed rule actions, nonzero root
counters, and dimensions/states where inhabitants exist.  The `q = 0` case
is vacuous because `Fin.t 0` has no state configuration.

## Independent review

Independent read-only review: PASS for the mutual induction, both order
directions, exact equations, unordered-isomorphism transport, and the
occurrence-specific Lemma 8 construction.  The reviewer noted that the audit
module records public types and assumptions rather than duplicating the
universal proofs with a large suite of concrete run fixtures; this is not a
contract weakness and no blocker remains.
