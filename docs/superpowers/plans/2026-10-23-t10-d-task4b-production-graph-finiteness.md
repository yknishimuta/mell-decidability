# T10-D Task 4B implementation plan

> Spec: the user-supplied T10-D Task 4B contract in this session.

## Scope and baseline

- Work only on Corollary 5.12 and its finite-branching support lemmas.
- Preserve all Task 4A public definitions and theorem types.
- Baseline: `397b0c4596f7c85613f37fccadc7aa6fd3e034ad`.
- Work in the current checkout: the pre-existing dirty files are protected audit
  logs and vendor material explicitly excluded from staging.  A second worktree
  would not improve isolation because the task series deliberately continues in
  this checkout and only an explicit target-file add is permitted.

## Checkpoints

1. Add a RED audit file checking the requested public API.
2. Define Boolean masks, enumerate all masks, and connect mask projection to
   `ProjectBounded` and the common special state.
3. Prove cross-graph projected-step determinism for a fixed mask and lift it to
   deterministic action-word traces.
4. Define simple production-graph paths, remove cycles from arbitrary paths,
   and prove that their state traces are `nvec_le` bad sequences.
5. Prove a reusable finite-branching AF bad-path bound from `af_bar_good`; then
   obtain the fixed-mask uniform simple-path bound without any choice axiom.
6. Enumerate bounded action words to obtain uniform state universes; combine the
   finitely many masks and form the uniform edge universe.
7. Define graph signatures, finite powersets, exact representation, and prove
   `corollary_5_12_production_graph_class_finite`.
8. Add boundary regressions and the audit document; run focused and full
   verification, `coqchk`, assumptions/dependency scans, diff checks, and an
   independent review.  Commit only Task 4B files.

## Proof invariants

- Cross-graph determinism always carries equality of masks.
- Every uniform path begins at the fixed capacity/mask special state.
- The action alphabet is the finite `PlainVAS` list; duplicate actions are
  compared by vector value.
- Boundedness comes from the inductive AF/bar proof plus finite branching, not
  from individual graph finiteness.
- Catalog construction is Prop-level finite existence; it is not claimed to be
  an executable graph generator.
