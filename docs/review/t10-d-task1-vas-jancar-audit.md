# T10-D Task 1: VAS semantics and Jančar order audit

Date: 2026-10-23

Baseline: `bdf599ce91fcab5995759ad2ad319f9395fa3a61`

Scope: Leroux (2012), Sections 3--4 only.  Transformer relations,
production graphs, almost-semilinearity, and the finite-control lift are not
implemented in this unit.

## 1. Source/API audit

The source used was the official EasyChair PDF of Leroux, *Vector Addition
Systems Reachability Problem (A Simpler Solution)*.  Section 3 defines a VAS
as a finite subset of `Z^d`, a configuration as an element of `N^d`, and a
run as a nonempty configuration word whose consecutive differences are
actions.  The Coq record stores that same word without duplicating its first
configuration: a source plus its successive target configurations.  Action
labels are derived from consecutive configurations, so every `VASRun` is
connected by construction.  Consequently an empty target list is exactly the
paper's one-configuration, length-zero run.

The pre-existing final T10-D contracts are finite-control contracts:

```coq
vas_reach_relation_inter_semilinear :
  forall d q (V : VAS d q)
    (R : SConfig d q -> SConfig d q -> Prop), ...

vas_post_inter_semilinear :
  forall d q (V : VAS d q)
    (X Y : SConfig d q -> Prop), ...
```

No such `VAS d q` type existed at the baseline.  This task therefore follows
the current task contract and introduces only the paper-faithful stateless
core.  A later unit must preserve control states by specializing the
stateless theorem to each of the finitely many source/target state pairs and
taking their finite union.  State erasure is not assumed.

## 2. Run semantics

The exact central definitions are:

```coq
Definition PlainVAS (d : nat) := list (ZVec d).

Definition PlainVASStep {d} (system : PlainVAS d)
    (source : NVec d) (action : ZVec d) (target : NVec d) : Prop :=
  List.In action system /\
  action = StepAction source target.

Record VASRun (d : nat) := {
  RunSource : NVec d;
  RunTargets : list (NVec d)
}.

Definition ValidVASRun {d} (system : PlainVAS d) (run : VASRun d) : Prop :=
  ValidVASTargets system (RunSource run) (RunTargets run).

plain_vas_step_iff :
  forall d (system : PlainVAS d) source action target,
    PlainVASStep system source action target <->
    List.In action system /\
    nvec_to_zvec target = zvec_add (nvec_to_zvec source) action.

Inductive PlainVASReach {d} (system : PlainVAS d) :
    NVec d -> NVec d -> Prop :=
| plain_vas_reach_refl : forall source,
    PlainVASReach system source source
| plain_vas_reach_step : forall source middle target,
    List.In (StepAction source middle) system ->
    PlainVASReach system middle target ->
    PlainVASReach system source target.
```

All step arithmetic is performed after embedding configurations into `Z^d`.
There is no truncated natural subtraction.  The public reach/run theorem and
monotonicity theorem have the following checked types:

```coq
vas_reach_run_iff :
  forall d (system : PlainVAS d) (source target : NVec d),
    PlainVASReach system source target <->
    exists run : VASRun d,
      ValidVASRun system run /\
      RunSource run = source /\
      RunTarget run = target.

vas_reach_monotone :
  forall d (system : PlainVAS d) (source target offset : NVec d),
    PlainVASReach system source target ->
    PlainVASReach system
      (nvec_add source offset) (nvec_add target offset).
```

Supporting results cover empty runs, reachability transitivity, connected
run concatenation, action displacement, target/displacement soundness,
determinism for a fixed source and action word, shifted-run validity,
unchanged action words, and shifted endpoints.  The converse of displacement
soundness is deliberately absent.  The regression
`audit_invalid_cancel_not_valid` says that there is no valid run with source
zero and word `[-1;+1]`: its total displacement is zero, but its first
intermediate configuration would have to be negative.

This is exactly Lemma 3.1's translation argument: `ShiftVASRun` adds one
`NVec` offset to every stored configuration and preserves every action.

## 3. Jančar order and Higman characterization

The direct relation is the paper's gap decomposition.  Its recursive match
constructor stores an explicit prefix `gap`, a nonnegative `offset`, the
matched original action, and the remaining decomposition.  The final
constructor stores the trailing gap:

```coq
Inductive JancarGapDecomposition {d} :
    NVec d -> list (ActionConfiguration d) ->
    NVec d -> list (ActionConfiguration d) -> Prop :=
| jancar_gap_final : forall small_current big_current gap final_offset,
    TraceTarget big_current gap = nvec_add small_current final_offset ->
    JancarGapDecomposition small_current [] big_current gap
| jancar_gap_match : forall small_current action small_target small_tail
    big_current gap offset big_tail,
    TraceTarget big_current gap = nvec_add small_current offset ->
    JancarGapDecomposition small_target small_tail
      (nvec_add small_target offset) big_tail ->
    JancarGapDecomposition small_current
      ((action, small_target) :: small_tail) big_current
      (gap ++ (action, nvec_add small_target offset) :: big_tail).

Definition JancarRunLe {d} (left right : VASRun d) : Prop :=
  exists initial_offset,
    RunSource right = nvec_add (RunSource left) initial_offset /\
    JancarGapDecomposition (RunSource left) (RunAnnotatedWord left)
      (RunSource right) (RunAnnotatedWord right).
```

Because a `VASRun` is connected by construction, every explicit `gap` is an
actual connected subrun.  At a match, the larger trace contains exactly the
same action value at configuration `small_target + offset`.  Thus inserted
transitions and matched original transitions are structurally distinct, as in
Leroux's definition.  `nvec_le_offset_witness` recovers each nonnegative
offset from componentwise comparison in the reverse characterization.

The annotated alphabet and public characterization are:

```coq
Definition ActionConfigurationLe {d} :
    ActionConfiguration d -> ActionConfiguration d -> Prop :=
  fun left right =>
    fst left = fst right /\ nvec_le (snd left) (snd right).

Definition RunAnnotatedWord {d} (run : VASRun d) := RunSteps run.

Definition RunDirectionLe {d} (left right : VASRun d) : Prop :=
  nvec_le (RunSource left) (RunSource right) /\
  nvec_le (RunTarget left) (RunTarget right).

Definition HigmanRunEmbed {d} := list_embed (@ActionConfigurationLe d).

jancar_run_le_iff_higman :
  forall d (left right : VASRun d),
    JancarRunLe left right <->
    RunDirectionLe left right /\
    HigmanRunEmbed
      (RunAnnotatedWord left) (RunAnnotatedWord right).
```

The forward proof turns every operational match into a Higman match and
extracts the final offset.  The reverse proof decomposes a Higman embedding at
its first match; connectedness and equality of the action labels force the
prefix gap to end at the required shifted source.  Thus the displayed theorem
is a proved characterization rather than a second definition.

Actions are compared by their actual `ZVec` values.  Duplicate positions in
the finite system list are used only as an internal WQO code and do not make
the public order stricter.  Reflexivity and transitivity are separately
proved.  Source/target comparison is not inferred from the word embedding;
the empty-word and direction regressions demonstrate why it is independent.

## 4. Lemma 4.1 / WQO proof

The final checked type is:

```coq
jancar_run_wqo :
  forall d (system : PlainVAS d),
    afs (ValidVASRun system) (@JancarRunLe d).
```

The proof uses:

1. `nvec_le_almost_full` (Dickson on `N^d`);
2. `af_idx` for equality on the finite list of action positions;
3. `af_product` for action-position/configuration pairs and for source/target;
4. `af_list_embed` (Higman's lemma) for annotated words;
5. `af_rel_morph`/`af_sub_rel_afs` to erase the internal finite action index.

Every valid run is recursively decorated by actual action-position witnesses
obtained from its step-validity membership proofs.  The morphism theorem then
maps an encoded embedding back to equality of actual action values.  This is
why repeated equal actions remain interchangeable, while the proof still has
a genuinely finite action alphabet.  No sequence-selection or choice
principle is used.

## 5. Regression coverage

The focused regression checks:

- dimension zero and a nonempty zero-dimensional action word;
- an empty finite action word and reflexive reachability;
- `0 --(+1)--> 1`;
- invalid `0 --[-1;+1]--> 0` versus valid `1 --[-1;+1]--> 1`;
- shifting a valid negative/positive run without changing its action word;
- zero actions inserted as Jančar gap transitions;
- empty-word embedding;
- action-label mismatch;
- failure of the source and target direction comparisons;
- duplicate actual action values in the system list;
- Jančar reflexivity (with transitivity supplied by the public theorem).

The implementation also supports empty action systems: only empty runs are
valid, and the WQO theorem remains applicable.  Positive and negative actions
coexist in `audit_vas`.

## 6. Task 2 handoff

Section 5 defines the capacity transformer `T_c` by existence of a run from
`c+x` to `c+y`, and the transformer along `rho=c_0...c_k` as the composition
`T_{c_0} o ... o T_{c_k}`.  Task 2 must introduce these definitions and prove
Lemmas 5.1--5.2 before stating any Jančar-monotonicity bridge.

In particular, this audit does **not** guess or publish an inclusion direction
for

```text
rho <=_J rho' -> Transformer(rho) ? Transformer(rho').
```

The required direction and any intervening composition factors must be
derived from the Section 4 gap decomposition after the transformer API is
fixed.  Later finite-control lifting must additionally retain source and
target states, split by their finite state pair, apply the stateless theorem
within each pair, and reassemble the finite union.

## 7. Assumptions and verification

The RED check preceded the new modules: importing `Mell.VAS.Runs` failed
because no physical path/module existed.  GREEN then covered the focused
build and all examples before the full project regression.

`Print Assumptions` reports `Closed under the global context` for:

- `vas_reach_run_iff`;
- `vas_reach_monotone`;
- `jancar_run_le_iff_higman`;
- `jancar_run_wqo`.

The task-specific audit runs focused compilation, the examples above,
`coqchk -silent`, and scans the target files for `Axiom`, `Admitted`, `Abort`,
`ClassicalEpsilon`, UIP/K, `Eq_rect_eq`, functional extensionality,
constructive indefinite description, and external oracles.  All checks pass.

An independent re-review additionally rebuilt `Runs.v`, `JancarOrder.v`, and
`VASJancarExamples.v` in dependency order, reran targeted `coqchk -silent`,
and approved the operational gap definition, the two-way Higman bridge, the
finite-action WQO encoding, regression coverage, and Task 2 scope boundary.
