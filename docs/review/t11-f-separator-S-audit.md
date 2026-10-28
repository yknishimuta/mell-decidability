# Task 11-F audit: Separator S and singleton separation

## Scope and source correspondence

This change completes Bizière--Leroux--Sutre, arXiv:2607.09558v1,
Theorem 3.3 from the rank-descent theorem proved in Task 11-E.  It then
specializes the theorem to the complement of one configuration and exposes an
actual finite `SemiCode`.  It does not construct an executable separator
selector and does not enter Task 12.

The implementation is in `theories/Separator/Main.v` and
`theories/Separator/Singleton.v`; public checks and dimension-zero boundary
regressions are in `theories/Audit/SeparatorExamples.v`.

## Initial Safety Witness

The initialized-run cover used here has the following existing contract:

```coq
irun_le_finite_cover :
  forall d (system : IBVAS d),
    exists basis : list { run : IRun d | ValidIRun system run },
      forall run : { run : IRun d | ValidIRun system run },
        exists base,
          In base basis /\ IRunLe (proj1_sig base) (proj1_sig run)
```

`full_orthant_generators d` recursively builds the standard rational unit
vectors.  `full_orthant_contains_nvec` proves that every embedded natural
vector is in the generated cone, including `d = 0`.  The independently
reviewed strengthening

```coq
full_orthant_generated_iff_nonnegative :
  forall d point,
    qcone_generated (full_orthant_generators d) point <->
    forall index, 0 <= point index
```

also gives the complete characterization for arbitrary rational vectors.
Each finite-cover run is
paired with this same cone.  Consequently all initial nodes are homogeneous.

Coverage is coverage of the actual initialized run: `IRunLe` supplies the
exact root equation `target(run) = target(base) + offset`; the natural offset
is embedded into the full orthant and used to build
`DirectedRunMember (full_orthant_node base) run`.  Target-only coverage is not
used.

The resulting public theorem is:

```coq
initial_safety_witness_exists :
  forall d (system : IBVAS d) (safe : NSet d),
    Semilinear safe ->
    (forall value, Reach system value -> safe value) ->
    exists witness : SafetyWitness system safe,
      SameSet (witness_attractor witness) (fun _ => False)
```

## Terminal witness and rank induction

For an empty node list, the coverage disjunction cannot select a node.  A
leaf initialized run therefore places every initial vector in the attractor.
The existing `attractor_with_initials_inductive` bridge then proves rule
closure; it uses both the attractor condition and the newly established
initial inclusion.

```coq
terminal_safety_witness_invariant :
  forall d (system : IBVAS d) (safe : NSet d)
      (witness : SafetyWitness system safe),
    witness_nodes witness = [] ->
    Semilinear (witness_attractor witness) /\
    InitialIncluded system (witness_attractor witness) /\
    Closed system (witness_attractor witness) /\
    (forall value, witness_attractor witness value -> safe value)
```

`every_safety_witness_reaches_terminal` uses
`witness_rank_less_well_founded`.  Its induction predicate quantifies over all
witnesses with a fixed node list, so neither attractors nor dependent proof
fields are equated.  In the nonempty case it invokes only
`lemma_7_1_safety_witness_rank_descent` and recurses on the strictly smaller
node list.

```coq
every_safety_witness_reaches_terminal :
  forall d (system : IBVAS d) (safe : NSet d)
      (witness : SafetyWitness system safe),
    exists terminal : SafetyWitness system safe,
      witness_nodes terminal = []
```

This is Prop-level well-founded induction, not a Gallina update algorithm and
not an invocation of Theorem 3.3.

## Theorem 3.3

The initial witness, terminal-witness existence, and terminal invariant are
composed without additional assumptions:

```coq
separator_S :
  forall d (system : IBVAS d) (Phi : NSet d),
    Semilinear Phi ->
    (forall value, Reach system value -> Phi value) ->
    exists J : NSet d,
      Semilinear J /\
      InitialIncluded system J /\
      Closed system J /\
      (forall value, J value -> Phi value)
```

The proof dependency is acyclic: finite IRun cover -> initial witness -> Task
11-E rank descent -> terminal witness -> separator.  Neither singleton
separation nor a decision procedure occurs in this chain.

## Singleton complement and finite certificate

The existing explicit singleton code `[(target, [])]` is used through
`singleton_nset_semilinear`; `semilinear_complement` then proves:

```coq
singleton_complement_semilinear :
  forall d (target : NVec d),
    Semilinear (fun value => value <> target)
```

This statement includes `d = 0`; in that dimension the complement of the
unique empty vector is the empty semilinear set.

Applying `separator_S` to that complement yields a semilinear `J`.  Its
existential `SemiCode` witness is eliminated only inside Prop.  The equivalence
`J value <-> denote code value` transports initial inclusion from left to
right, transports every child from `denote code` back to `J` before applying
`Closed`, transports the parent forward again, and proves target exclusion.

```coq
singleton_separator :
  forall d (system : IBVAS d) target,
    ~ Reach system target ->
    exists code : SemiCode d,
      InitialIncluded system (denote code) /\
      Closed system (denote code) /\
      ~ denote code target
```

No unconditional function `IBVAS d -> NVec d -> SemiCode d` is claimed.

## Kernel and assumption audit

Focused `coqc` succeeded for `Main.v`, `Singleton.v`, and
`SeparatorExamples.v`.  Public `Check` commands reproduce the types above.
`Print Assumptions` reports:

- `terminal_safety_witness_invariant`: closed under the global context;
- `initial_safety_witness_exists`,
  `every_safety_witness_reaches_terminal`, `separator_S`,
  `singleton_complement_semilinear`, and `singleton_separator`: only
  `Classical_Prop.classic`.

The classical dependency is inherited from the existing finite-cover,
rank-descent, and semilinear-complement developments.  No new mathematical
axiom or selection oracle is introduced.  A targeted scan found no `Axiom`,
`Admitted`, `admit`, `Abort`, `ClassicalEpsilon`, `ClassicalChoice`, UIP/K,
`Eq_rect_eq`, or functional extensionality in the Task 11-F sources.

## Verification

- Task 11-F focused build: PASS.
- Task 11-A--11-E audit regressions: PASS.
- T09 initialized-run finite-cover audit: PASS.
- T10-A semilinear closure and T10-G finite-cover audits: PASS.
- T08 invariant audit: PASS.
- Forced clean `_CoqProject` rebuild: PASS.
- `make -f Makefile.coq validate`: PASS; this ran `coqchk -silent` on the full
  dependency closure, including all three new `.vo` files.
- Targeted prohibited-construct scan: PASS.
- Targeted `git diff --check`: PASS.
- Independent review: initial review found two Important completeness gaps
  (the full-orthant iff and two explicit boundary regressions).  Both were
  implemented and kernel-checked.  The independent re-review returned PASS
  with no remaining Critical, Important, or Minor findings.

The full-project `coqchk` context also lists historical axioms from unrelated
dependencies.  The theorem-level `Print Assumptions` results above are the
relevant trust boundary and contain only the already accepted propositional
excluded middle.

## Git and unresolved obligations

- Branch: `work/mell-formalization`.
- Starting HEAD: `82eab5b0c16bbe4b50023e5c5b2f959b5012c876`.
- Final Task 11-F commit: the local commit containing this audit; its exact
  hash is reported in the final Task 11-F completion report.
- Push: not performed.
- Unresolved proof obligations: none.
