# T10-E Task 6E4 — Theorem 12 and Corollary 14 audit

## Scope and baseline

- Branch: `work/mell-formalization`
- Baseline HEAD: `2113593c97175d16cef6244956e6f2d977599b18`
- Paper correspondence: Bizière–Leroux–Sutre, FoSSaCS 2026,
  Theorem 12 and Corollary 14.
- Scope stops at Task 6E4. Task 6F is not included.

## Theorem 12

The public section equivalence is:

```coq
Definition VASSSectionOf {d q} (B : SBVAS d q)
    (W : VASSSection d q) : Prop :=
  forall state counters,
    SReach B state counters <-> VASSSectionReach W state counters.

Theorem bvass_reach_is_vass_section :
  forall d q (B : SBVAS d q),
    exists W : VASSSection d q,
      VASSSectionOf B W.
```

`lemma_9_reach_bounded_branching_iff` supplies an existential finite list `F`
and bound.  The witness is the transparent, computable bounded-depth compiler

```text
compile_bounded_vass_section (extend_bvass B F) bound.
```

`lemma_11_bounded_depth_vass_section` identifies this section with the bounded
run predicate, while Lemma 9 already identifies that predicate with the
original reachability set.  The proof uses `F` and `bound` only inside `Prop`;
it does not claim a computable selector for the finite basis or for the final
section.

## Section restriction and Corollary 14

For a section `W`, `SectionInitialSet W` is its finite list of internal initial
configurations.  `finite_nvec_set_semilinear` proves each finite state slice
semilinear without a choice principle.

For each original state `s`, the internal target predicate is:

```coq
Definition SectionTargetSet ... := fun config =>
  fst config = section_accept_state W s /\
  exists counters,
    R (s, counters) /\
    snd config = section_target_vector W counters.
```

Since `section_target_vector W counters` is exactly
`counters ++ zero(auxiliary)`, this simultaneously enforces the selected
accept state, the original semilinear constraint, and the entire zero suffix.
The target predicate is proved semilinear by mapping each semilinear component
through the exact left embedding.

`vas_post_inter_semilinear` is then applied to the internal VAS with the finite
initial predicate and this restricted target predicate.  Only afterwards is
the result projected to the first `d` coordinates.  The new constructive
adapters

```coq
project_nset_cone
asymptotically_definable_nset_coordinate_projection
almost_semilinear_nset_coordinate_projection
```

prove this set-valued coordinate projection using natural witnesses, periodic
cone projection, and rational definability projection.  No negative integer is
converted by truncation.  The stateful definition is already a family indexed
by each finite state, so the result is reconstructed state-by-state; `q = 0`
is vacuous.

The section-level and final public theorems are:

```coq
Theorem vass_section_inter_semilinear : forall d q
    (W : VASSSection d q) (R : SConfig d q -> Prop),
  StatefulSemilinear R ->
  StatefulAlmostSemilinear (fun config =>
    R config /\ VASSSectionReach W (fst config) (snd config)).

Theorem bvass_reach_inter_semilinear :
  forall d q (B : SBVAS d q) (R : SConfig d q -> Prop),
    StatefulSemilinear R ->
    StatefulAlmostSemilinear (fun config =>
      R config /\ SReach B (fst config) (snd config)).
```

The last step is extensional transport along `VASSSectionOf B W`.

## Regression coverage

The universally quantified proofs cover dimensions and state counts zero,
empty/multiple initial lists, empty rule sets, unary and branching systems,
duplicate child states, empty/single/multiple bases, empty and universal target
constraints, multiple original states, zero auxiliary dimension, empty finite
unions, and projected zero generators.  In particular, an internal target with
a nonzero auxiliary coordinate cannot satisfy `SectionTargetSet`, even when
its visible prefix agrees: the exact equality with `section_target_vector`
rejects it before projection.

## Axiom audit

The following new structural adapters report `Closed under the global
context`:

- `project_nset_cone`;
- `almost_semilinear_nset_coordinate_projection`;
- `section_initial_set_semilinear`;
- `section_target_set_semilinear`.

The two final results report only `Classical_Prop.classic`.  For Theorem 12 it
is inherited through Task 6E2's finite ContextOrder basis.  For Corollary 14 it
is inherited both through Theorem 12 and Task 6D's VAS almost-semilinearity.
No `ClassicalEpsilon`, choice oracle, UIP/K, `Eq_rect_eq`, functional
extensionality, or new mathematical axiom is present.

## Verification record

All commands exited 0 after the final source revision:

- `make check-t10-e4`;
- `make audit-t10-e4` (public `Check`, `Print Assumptions`, dependency print,
  targeted prohibited-construct scan, and targeted `coqchk -silent`);
- `make audit-t10-d-task6d audit-t10-e0 audit-t10-e1 audit-t10-e2
  audit-t10-e3 audit-bridges audit-t10-g`;
- `opam exec --switch . -- make -f Makefile.coq clean`;
- `opam exec --switch . -- make -f Makefile.coq -j2`;
- `opam exec --switch . -- make -f Makefile.coq validate`.

The last two commands are a forced full `_CoqProject` rebuild followed by the
full dependency-closure `coqchk -silent`.  The repository-wide context summary
still lists axioms from older unrelated modules; the Task 6E4 public closure is
the separate targeted result recorded above.  The whole worktree contains
protected pre-existing modified audit logs, so target-only and staged
`diff --check` are used; those logs are neither edited nor staged by this task.

## Independent review

A fresh read-only reviewer returned **PASS**, with no Critical or Important
finding.  It independently checked the directions of the Lemma 9/Lemma 11
composition, Prop-only use of the finite basis witnesses, exact finite initial
set, accept-state and zero-suffix target restriction, projection order,
periodic-cone projection, state reconstruction including `q = 0`, public
contracts, and prohibited dependencies.  Its only Minor observation was to
replace this section's temporary verification placeholder after the final
build; that update is incorporated here.

## Remaining obligations

No Task 6E4 proof obligation remains. Task 6F is deliberately not started.
