# arXiv:2607.09558v1 fidelity GAP closure

Date: 2026-10-27

Baseline: `2190c6fbfbf523c77224e247884bcae001ddf3bc`

This note records the closure of the six API/statement gaps identified by
`arxiv-2607.09558v1-fidelity-audit.md`.  It does not claim a line-by-line
formalization of every explanatory passage in the paper, and it does not
alter the R03/R07--R09/R11 repairs.

## Public contracts

```coq
fact_3_2_all_leaf_increments :
  forall d (S : IBVAS d) run increments,
    ValidFreeIRun S run ->
    length increments = length (free_irun_sources run) ->
    exists shifted sources,
      ValidFreeIRun S shifted /\
      LeafIncrementsRun run increments shifted /\
      add_source_increments (free_irun_sources run) increments =
        Some sources /\
      free_irun_sources shifted = sources /\
      irun_target shifted =
        nvec_add (irun_target run) (nvec_rsum increments).

fact_3_6_reach_shuffle_flatten :
  forall d (S : IBVAS d) (K L : Language d),
    NonemptyLanguage K -> NonemptyLanguage L ->
    forall target,
      ReachLanguage S
        (LanguageShuffle K (NonemptyWords (ReachL S L))) target ->
      ReachLanguage S (LanguageShuffle K (LanguagePlus L)) target.

irun_le_antisymmetric :
  forall d (rho sigma : IRun d),
    IRunLe rho sigma -> IRunLe sigma rho -> rho = sigma.

lemma_3_10_irun_wpo_amalgamation :
  forall d (S : IBVAS d), IRunWPOAmalgamation d S.

remark_2_2_full_iff_closed_linearization_fixed :
  forall d (P : ZSet d),
    Periodic P -> FinitelyGeneratedPeriodic P ->
    (FullPeriodic P <-> SameSet (ClosedLinearization P) P).

paper_attractor_iff_attractor :
  forall d (S : IBVAS d) A,
    PaperAttractor S A <-> Attractor S A.

paper_lemma_7_1_safety_witness_rank_descent :
  forall d (S : IBVAS d) Phi
      (w : PaperSafetyWitness S Phi),
    paper_witness_nodes w <> [] ->
    exists next : PaperSafetyWitness S Phi,
      WitnessRankLess
        (paper_witness_nodes next) (paper_witness_nodes w).

paper_lemma_5_6_bvas_wsvas_exists :
  forall d (S : IBVAS d) (A : NSet d),
    Semilinear A ->
    exists V : WSVAS d,
      forall source target,
        WSVASStep V source target <->
        BVASSideStepWithSet S
          (fun x => A x \/ Reach S x) source target.
```

## Dependency and premise audit

- Fact 3.2 is a mutual structural induction over ordered run trees and child
  forests.  The increment list is aligned with leaf occurrences; equal-valued
  leaves may receive different increments.  No initial-leaf premise is used.
- Fact 3.6 uses an inductive ordered interleaving, not `Permutation` as the
  definition of shuffle.  It performs only finite, occurrence-indexed choices
  already present in the input reach witnesses.  It assumes no decidability,
  semilinearity, finiteness, or commutativity of `K` or `L`.
- Raw `IRun` stores action values, ordered children, configurations, and
  leaves; it stores neither a `ValidIRun` proof nor rule-occurrence indices.
  The existing `Action` value does carry its arity-positivity proof field.
  Node count rules out a mutual embedding in which one
  direction matches strictly below the root, so direct antisymmetry is valid;
  no quotient or proof irrelevance is involved.
- Remark 2.2 uses finite generation essentially.  The proof obtains a finite
  rational-cone representation and proves that it is topologically closed.
  The executable Example 2.3 regression proves that the full periodic set
  `{0} union N_{>0}^2` gains `(1,0)` under closed linearization.
- `PaperAttractor` has exactly the paper's initial-side formulation.
  `paper_attractor_iff_attractor` is unconditional in `A`.  The witness
  conversions preserve the node list definitionally, hence preserve the rank
  relation used by Lemma 7.1.
- Lemma 5.6 eliminates a `SemiCode` witness only inside `Prop`.  Its public
  theorem has no code, free-run closure, attractor, or computability premise,
  and is deliberately a one-step equivalence rather than a reachability-star
  statement.

## Classification

| Historical gap | Result | Classification |
|---|---|---|
| Remark 2.2 | exact finite-generation fixed-point theorem | EXACT |
| Fact 3.2 | simultaneous occurrence-wise leaf increments | EXACT |
| Fact 3.6 | arbitrary ordered nonempty-word languages | EXACT |
| Attractor and Lemma 7.1 | bidirectional representation bridge | EQUIVALENT |
| Lemma 3.10 WPO | raw-run antisymmetry plus WQO/amalgamation package | EXACT / R03 REPAIRED |
| Lemma 5.6 | existential WSVAS, exact one-step relation | EQUIVALENT |

## Assumptions

Focused `Print Assumptions` reports the Fact 3.2, Fact 3.6, antisymmetry,
Lemma 3.10 package, Remark 2.2, attractor equivalence, and Lemma 5.6 bridge as
closed under the global context.  The paper-shaped Lemma 7.1 inherits only
`Classical_Prop.classic` from the already verified witness-update theorem.
No new axiom, choice oracle, UIP/K, `Eq_rect_eq`, proof irrelevance, or
functional extensionality is introduced.

## Extraction boundary

The reusable helper modules are proof/semantic modules.  The public wrappers
are in `Mell.Audit.PaperFidelityBridges`; no reduction or decision module
imports that Audit module.  The existing extraction dependency repair and
runtime computation path are therefore unchanged.

## Verification

- Focused compilation and the boundary regression module: PASS.
- Forced full `_CoqProject` rebuild: PASS.
- `make -f Makefile.coq validate` and full dependency-closure `coqchk`: PASS.
- Targeted `coqchk -silent` for every new module: PASS.
- `make check-final`, `make audit-final`, and `make extract-final`: PASS.
- Native extracted-runtime gate: PASS, 22/22 cases.
- Forbidden-construct and reverse-import scans: PASS.
- Target-only `git diff --check`: PASS.

Independent review findings and their disposition are recorded in the main
fidelity audit after the source-to-paper review is complete.

## Independent review

An independent reviewer re-opened the arXiv v1 TeX and the relevant Coq
sources.  The review reported PASS with no Critical or Important findings.  It
confirmed all six premise/conclusion correspondences, ordered occurrence
handling, raw-run antisymmetry, the finite-generation condition in Remark 2.2,
the unconditional attractor bridge, the one-step scope of Lemma 5.6, and the
absence of reverse imports into the computation path.  The sole wording
nuance—`Action` carries an arity-positivity proof although `IRun` carries no
validity proof—has been made explicit above.
