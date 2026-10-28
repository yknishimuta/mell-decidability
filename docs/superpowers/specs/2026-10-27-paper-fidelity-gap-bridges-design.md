# Paper Fidelity GAP Bridges Design

## Intent

Close the six explicitly recorded fidelity gaps between arXiv:2607.09558v1
and the completed Coq development without changing the existing separator,
decision procedure, run semantics, or repaired statements R03/R07--R09/R11.
The new public surface must make the paper-shaped statements directly
checkable while keeping long structural proofs out of the audit namespace.

## Goals and non-goals

- Prove paper-strength public statements for Fact 3.2, Fact 3.6, the
  attractor equivalence and paper-shaped Lemma 7.1, Lemma 3.10's WPO claim,
  Remark 2.2, and Lemma 5.6.
- Preserve all existing public definitions and theorem types.
- Add no new mathematical axiom, choice oracle, proof irrelevance, UIP/K,
  `Eq_rect_eq`, or functional extensionality.
- Do not alter extraction or runtime imports: audit bridges must not enter
  the decision procedure's computation path.
- Do not claim that every sentence or example in the paper has been
  formalized merely because these six recorded gaps are closed.

## Approaches considered

1. Add every theorem to its historical owner file. This gives natural names
   but risks import cycles and spreads paper-facing wrappers through stable
   Task 11 modules.
2. Put all definitions and proofs in one audit module. This minimizes edits
   but turns the audit module into a second implementation layer.
3. **Selected hybrid.** Put reusable structural operations in small modules
   immediately above their existing data definitions, and collect only the
   paper-shaped records and wrapper theorems in
   `theories/Audit/PaperFidelityBridges.v`.

## Dependency structure

```text
BVAS/System, Runs, Contexts, RunOrder
        |
        +--> BVAS/RunLeafOperations       (Fact 3.2)
        +--> BVAS/RunOrderAntisymmetry    (Lemma 3.10 order)

WSVAS/BVASSimulation
        |
        +--> BVAS/LanguageFlattening      (ordered languages, Fact 3.6)

Geometry/ClosedLinearization + finite-cone geometry
WSVAS/WitnessAlphabet + Semilinear presentation
Separator/Attractor + SafetyWitness + WitnessUpdate
        |
        +--> Audit/PaperFidelityBridges   (paper-shaped public surface)
        +--> Audit/PaperFidelityExamples  (boundary regressions)
```

No file below `Audit/` is imported by reduction or decision modules.  The
two BVAS helper modules import only lower semantic layers plus the already
existing free-run layer; no Separator or Audit dependency points downward.

## Contract table

| Gap | Paper domain and premise | Existing checked basis | Missing bridge | Target public contract | Completion classification |
|---|---|---|---|---|---|
| Remark 2.2 | `P subset Z^d`, periodic and finitely generated | `full_periodic_iff_linearization_fixed`, finite generation of `Cone P`, rational closure | finite rational cone equals its rational topological closure | `Periodic P -> FinitelyGeneratedPeriodic P -> (FullPeriodic P <-> SameSet (ClosedLinearization P) P)` | EXACT when both directions are proved over `ZSet d` |
| Fact 3.2 | arbitrary valid free run and one increment per source occurrence | `apply_action_frame_shift`, exact natural-vector arithmetic | simultaneous structural lifting and source-list equation | length-aligned increment list yields a valid run with pointwise-added sources and target plus the increment sum | EXACT when occurrence order and independent increments are preserved |
| Fact 3.6 | arbitrary languages `K,L subset (N^d)^+` | free-run contexts and finite substitution | ordered-language shuffle and finite flattening | `ReachLanguage (K shuffle ReachLanguage(L)^+) target -> ReachLanguage (K shuffle L^+) target` | EXACT when neither commutativity nor finiteness/decidability is assumed |
| Attractor / Lemma 7.1 | paper initial-side attractor and paper safety witnesses | `attractor_initial_form`, `lemma_7_1_safety_witness_rank_descent` | reverse attractor implication and record transport | `PaperAttractor S A <-> Attractor S A`; paper-record rank descent | EQUIVALENT when both record conversions preserve nodes, coverage, homogeneity, and rank |
| Lemma 3.10 WPO | valid initialized runs and paper embedding order | reflexivity, transitivity, WQO, exact amalgamation | antisymmetry | `IRunLe rho sigma -> IRunLe sigma rho -> rho = sigma`, then packaged WPO/amalgamation | EXACT if raw `IRun` equality is proved; otherwise EQUIVALENT only after a full faithful representation theorem |
| Lemma 5.6 | every `S` and semilinear predicate `A` | `Semilinear A` exposes a `SemiCode`; `concrete_wsvas`; `lemma_5_6_bvas_wsvas_step_iff` | eliminate the presentation code from the public premise | `Semilinear A -> exists V, forall x y, WSVASStep V x y <-> BVASSideStepWithSet S (A union Reach S) x y` | EXACT when no closure/attractor premise remains |

## Representation decisions

### Ordered languages and shuffle

`Language d := list (NVec d) -> Prop`.  The shuffle relation is an inductive
interleaving that preserves the order of both input words.  Language star
and plus are finite concatenations, with plus explicitly nonempty.  A run
reaches a language when its exact `free_irun_sources` word belongs to it.
This avoids the existing `Permutation`-based APIs, which are correct for the
commutative set specialization but too weak to expose Fact 3.6 literally.

### Run antisymmetry

`IRun` contains no validity proofs or action occurrence indices.  It stores
only leaf values, action values, ordered child forests, and node targets.
The first implementation path therefore proves direct antisymmetry using a
mutual node-count/embedding argument.  A quotient or erased paper-run type is
not introduced unless a concrete counterexample to raw antisymmetry is
constructed.

### Paper safety witnesses

`PaperSafetyWitness` repeats the mathematical fields of `SafetyWitness` but
uses `PaperAttractor`, not the existing stronger-looking field.  Conversion
in both directions uses the attractor equivalence; all other fields and the
node list are definitionally preserved.  The paper-shaped rank descent is a
wrapper over the existing Lemma 7.1, not a second update construction.

### Lemma 5.6 existential

The public theorem destructs the `Semilinear A` witness inside `Prop`, chooses
the existing `concrete_wsvas S code`, and transports its one-step equivalence
along the denotation equivalence.  It does not construct a computational
choice function from arbitrary predicates.

## Boundary regressions

- dimension zero;
- duplicate equal-valued leaves with distinct increments;
- a two-leaf run with unequal increments;
- order-sensitive noncommutative singleton languages;
- empty `K` and empty `L`;
- zero reachable-side leaves in the attractor star;
- empty initial set and arbitrary non-semilinear `A`;
- equal action values represented by duplicate action-list occurrences;
- equal target with different trees and different child order;
- the finitely-generated hypothesis in Remark 2.2, plus the paper's
  non-finitely-generated counterexample `P = {0} union N_{>0}^2`.

## Verification and trust boundary

Every public bridge receives a focused `Check` and `Print Assumptions` audit.
The complete project is rebuilt and checked with `validate`, dependency
closure `coqchk`, final audit/extraction/runtime gates, forbidden-token scans,
and an independent paper-to-source review.  Existing
`Classical_Prop.classic` may propagate, but no additional principle is
introduced.  The extraction graph is checked to exclude the new Audit
modules.
