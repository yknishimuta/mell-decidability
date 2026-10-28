# Task 11-C safe-linearization audit

## Scope and source

This audit records the Task 11-C formalization of Section 5 of
Bizière–Leroux–Sutre, *Solving the Reachability Problem for Branching Vector
Addition Systems via Semilinear Inductive Invariants*, arXiv:2607.09558v1.
The implemented results are Lemma 5.7 (one-source reduction), Lemma 5.4
(WSVAS safe linearization), and Lemma 5.1 (BVAS safe linearization). Task 11-D
is outside this change.

## Public theorem contracts

```coq
Theorem lemma_5_7_one_source_reduction : forall d (S : IBVAS d)
    (I P X : NVec d -> Prop),
  ClosedUnderFreeRuns S I ->
  PeriodicNSet P ->
  NSetStable X P ->
  (forall target, ReachFromShuffle S X I target ->
    NSetMinkowskiN I P target) ->
  forall target,
    ReachFromShuffle S X I target <->
    ReachFromNonemptyShuffle S X I target.
```

```coq
Theorem semilinear_ray_almost_full : forall d (set : NSet d),
  Semilinear set -> @afs (NVec d) set (RayLe set).
```

```coq
Theorem lemma_5_4_wsvas_safe_linearization :
  forall (base : NVec d) (period target : NVec d -> Prop),
  PeriodicNSet period ->
  AsymptoticallyDefinableNSet period ->
  Semilinear target ->
  ReachWSVASFromSet system (NSetTranslate base period) target ->
  exists offset,
    period offset /\
    ReachWSVASFromSet system
      (NSetTranslate (nvec_add base offset)
        (ClosedLinearizationN period)) target.
```

Here `d` and `system : WSVAS d` are section parameters.

```coq
Theorem lemma_5_1_bvas_safe_linearization : forall d (S : IBVAS d)
    (A target period : NVec d -> Prop) (base : NVec d),
  IBVASInductiveInvariant S (fun value => A value \/ Reach S value) ->
  Semilinear A ->
  Semilinear target ->
  PeriodicNSet period ->
  AsymptoticallyDefinableNSet period ->
  (forall value,
    ReachFromShuffle S (NSetTranslate base period)
      (fun x => A x \/ Reach S x) value -> target value) ->
  (forall value, target value ->
    NSetMinkowskiN (fun x => A x \/ Reach S x)
      (ClosedLinearizationN period) value) ->
  exists offset,
    period offset /\
    forall value,
      ReachFromNonemptyShuffle S
        (NSetTranslate (nvec_add base offset)
          (ClosedLinearizationN period))
        (fun x => A x \/ Reach S x) value ->
      target value.
```

## Lemma 5.7

The proof works on Task 11-B free initialized runs rather than initialized
runs. `SourceMultiShuffle` preserves each leaf occurrence, including equal
values. A marked child is retained, other children are compressed using the
free-run closure of `I`, and all residual periods are added to the marked
leaf. `NSetStable X P` keeps that leaf in `X`; the root rule, signed action,
child multiplicities, child-counter sum, and final target remain exact. The
leaf case is explicit and does not require membership in the IBVAS initial
list.

## Semilinear ray relation

`RayLe S x y` carries an explicit nonnegative direction and requires every
natural multiple along the ray to remain in `S`. It is not declared
transitive. For each semilinear component, its finitely generated period
order supplies comparable witnesses; the finite component sum then gives
almost-fullness. The complement specialization uses the existing semilinear
complement theorem.

## Lemma 5.4

The proof uses the existing closed-linearization push-in theorem and the
finite-generation/WQO result for `ClosedLinearizationN P`. Run order,
closed-period order, and the complement ray relation are combined only as
almost-full relations. Counterexample witnesses are consumed by
`af_af_rec_total`; no function choosing a run for every natural number and
no countable-choice principle is introduced.

For the selected comparable indices, Task 11-B run scaling supplies exact
source and target equations. The source equation is rewritten to
`base + (y + r*x)`, and push-in puts `y + r*x` back in `P`. The target equation
is precisely the complement ray, contradicting the original safety
hypothesis. The push-in anchor and the final returned offset (`n` times that
anchor) remain distinct.

## Lemma 5.1

The semilinear witness for `A` is eliminated only inside `Prop`. Its code is
used to instantiate the Task 11-B concrete WSVAS; no executable selector for
semilinear representations is claimed. Extensional equivalence between
`A union Reach(S)` and `SimulationInvariant` transports the inductive
invariant/free-run closure and the existing Lemma 5.5 simulation theorem.
Lemma 5.4 yields the translated closed-linear source. The existing Lemma 5.7
then applies because the closed linearization is periodic, the translated
source is stable under it, and the assumed target bound gives the required
`I + Q` containment.

## Axiom and trust-boundary audit

`Print Assumptions` was run for all three public lemmas and for the ray
almost-full lemma. Each public Task 11-C theorem depends only on the existing
`Classical_Prop.classic`. No `Axiom`, `Admitted`, `admit`, `Abort`,
`ClassicalEpsilon`, `ClassicalChoice`, countable-choice oracle, UIP/K,
`Eq_rect_eq`, or functional extensionality was added.

## Verification

- Focused `coqc` compilation of all five Task 11-C modules: PASS.
- Focused `Makefile.coq` targets, including the audit module: PASS.
- Task 11-A, Task 11-B, T06/T09, and T10-C regression targets: PASS.
- Forced complete `_CoqProject` rebuild (`make -f Makefile.coq -B -j2`): PASS.
- `make -f Makefile.coq validate`, including dependency-closure
  `coqchk -silent`: PASS.
- Public `Check` and `Print Assumptions`: PASS.
- Task-source forbidden-construction scan: PASS.
- Task-scoped and staged whitespace checks: PASS.

The repository contains protected pre-existing modified and untracked audit
artifacts. They were neither changed for this task nor staged. A global
unstaged `git diff --check` consequently still reports pre-existing trailing
whitespace in protected log files; the Task 11-C diff itself is clean.

## Independent review

An independent read-only review checked occurrence preservation in Lemma
5.7, the distinction between almost-fullness and WQO in Lemma 5.4, the
absence of a new choice principle, both exact run-scaling equations, and the
simulation/invariant connection in Lemma 5.1. Its initial Important finding
(the audit module contained declarations but no boundary examples) was
resolved by adding kernel-checked empty-word, duplicate-occurrence,
zero-period, ray, and dimension-zero regressions. The final disposition was
PASS, with no Critical or Important findings. It noted only duplicated local
bridge helpers as a non-blocking maintenance issue; these were left intact to
avoid unnecessary changes to already checked proofs.

## Git information and obligations

- Branch: `work/mell-formalization`
- Baseline: `54c6278f9f9c545fcdb54fa83f69234d8d67bc9a`
- Result commit: recorded by Git history and the completion report
- Unresolved Task 11-C proof obligations: none
- Push performed: no
