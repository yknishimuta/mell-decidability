# Mathematical Provenance

## 1. Scope and Conventions

This document traces the mathematical results used by the development from a
specific published source to the current, kernel-checked Rocq declaration.  It
is not merely a bibliography.  In particular, it distinguishes a cited
mathematical source from a Rocq axiom: the papers below supplied statements and
proof ideas, but their results were re-proved in Rocq rather than postulated.

The repository state audited here is commit
`f14e38acbc8c3e9f2df2886ae155e2659c00fdcb`.  The implementation is checked
with Coq 8.20.1; “Rocq” below refers to the proof development, while command and
toolchain names retain the Coq 8.20.1 spelling.  Source versions are fixed in
[`review/sources.json`](review/sources.json) where that registry contains a
complete source record; the two incomplete secondary attributions are marked
**UNVERIFIED** below.

The relation column uses these terms:

- **EXACT** — source and Rocq statements have the same mathematical domain,
  hypotheses, and conclusion.
- **EQUIVALENT** — representations differ, and the required equivalence or
  bidirectional bridge is proved.
- **REPAIRED** — a source statement or proof detail required a mathematical
  correction.  This label concerns the repair; the numbered theorem's final
  statement may still be exact.
- **DERIVED** — the source result follows from a differently factored,
  kernel-checked chain.
- **NOT REQUIRED** — the adopted proof does not depend on this intermediate
  source claim.
- **UNVERIFIED** — the retained evidence does not justify an exact
  source-number or repair-label correspondence.  No correspondence is guessed.

`DIRECT`, `BRIDGE`, and `ALTERNATIVE PROOF` further describe how a result is
used.  Links under “Location” point to current source; links under “Evidence”
point to detailed audits, executable counterexamples, or the fixed primary
source.

BLS-v1 fixes a positive dimension, whereas the Rocq carriers quantify over
`d : nat` and also validate the degenerate case `d = 0`.  Accordingly,
**EXACT** means exact after restricting the Rocq declaration to the paper's
positive-dimensional domain; the extra zero-dimensional case is a conservative
generalization, not a source premise.  Any other conservative generalization
of a source result is stated explicitly in its row.

## 2. Source Registry

### 2.1 Direct mathematical sources

| ID | Fixed source used | Verified locator and role |
|---|---|---|
| BLS-v1 | Clotilde Bizière, Jérôme Leroux, and Grégoire Sutre, “Solving the Reachability Problem for Branching Vector Addition Systems via Semilinear Inductive Invariants,” arXiv:2607.09558v1, 10 July 2026. [HTML](https://arxiv.org/html/2607.09558v1), [PDF](https://arxiv.org/pdf/2607.09558v1). | Sections 2–7 and Appendices A–C; PDF SHA-256 `61ca188e9899b911de5662a3b0672653e9d0a3d58d2ae39d34a870a46b5fa422`. Principal source for semilinear BVAS separation. |
| BLS-FoSSaCS | Clotilde Bizière, Jérôme Leroux, and Grégoire Sutre, “Bridging the Gap Between Plain VASS and Branching VASS,” *FoSSaCS 2026*, LNCS 16503, pp. 65–87. [DOI](https://doi.org/10.1007/978-3-032-22730-0_4). | Proposition 5; Lemmas 6, 8, 9, and 11; Theorem 12; Corollaries 7 and 14. Principal source for the BVASS-to-VASS-section chain. |
| Leroux-2012 | Jérôme Leroux, “Vector Addition Systems Reachability Problem (A Simpler Solution),” *Turing-100*, EPiC Series in Computing 10 (2012), pp. 214–228. [DOI](https://doi.org/10.29007/bnx2), [publisher copy](https://easychair.org/publications/paper/Blr/open). | The 2012 EPiC edition, especially Sections 3–6 and Corollary 6.3 on printed p. 224. Numbering is not imported from another edition. |
| LS-2015 | Ranko Lazić and Sylvain Schmitz, “Non-Elementary Complexities for Branching VASS, MELL, and Extensions,” *ACM Transactions on Computational Logic* 16(3), Article 20 (2015), pp. 20:1–20:30. [DOI](https://doi.org/10.1145/2733375), [author PDF](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/LS-tocl15.pdf). | Author PDF matching arXiv:1401.6785v2; Lemma 3's first construction, Fact 8, Section 4.1.2 and Claim 9.1. Proposition 7(2) is recorded but is not misidentified with the ordinary-MELL reduction proved here. |
| Leroux-2011 | Jérôme Leroux, “Vector Addition System Reachability Problem: A Short Self-Contained Proof,” *POPL 2011*, pp. 307–316. | BLS-v1 attributes a rational-cone characterization to Theorem 3.5.  The exact primary passage was not retained in the source registry, so that theorem-number correspondence remains **UNVERIFIED**; the needed direction is proved locally instead. |
| Schrijver-1999 | Alexander Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1999. | BLS-v1 cites Corollary 7.1b in its Lemma 6.6 argument.  This development proves the needed finite-basis result locally, so no theorem from the book is an unchecked dependency. |

Named WQO results (Dickson, Higman, and Kruskal) enter through the formal
libraries described in Section 7.  They are not hidden paper axioms.

### 2.2 Evidence hierarchy

The primary versions above determine numbering and statements.  The detailed
cross-check is in
[`review/arxiv-2607.09558v1-fidelity-audit.md`](review/arxiv-2607.09558v1-fidelity-audit.md),
with the six formerly missing public bridges in
[`review/arxiv-2607.09558v1-fidelity-gap-closure.md`](review/arxiv-2607.09558v1-fidelity-gap-closure.md).
Task-specific audit records provide proof-dependency and assumption evidence.
Historical plans are not treated as evidence that a theorem was implemented.

The historical meanings of repair IDs R01--R11 are taken from the
user-provided, repository-external design source
`2026-10-17-mell-formalization-design.md`, Section 6.3.  Its identity, status,
and SHA-256 are recorded in the
[`historical repair-ledger audit`](review/doc-prov-r-historical-repair-ledger.md).
That design fixes ID ownership but explicitly predates implementation and
machine verification; current Rocq declarations, executable counterexamples,
and task audits independently determine implementation status below.

## 3. Main Results and Dependency Chains

The main mathematical path is:

```text
Leroux 2012: VAS post/pre intersection is almost semilinear
        |
        v
BLS FoSSaCS 2026: BVASS reachability is a VASS section
        |
        v
BLS arXiv-v1: Lemma 4.6 and Sections 5–7
        |
        v
Mell.Separator.Main.separator_S
        |
        v
Mell.Separator.Singleton.singleton_separator
        |
        v
complete BVAS certificate search

Lazić–Schmitz 2015: MELL -> ILZ -> full-zero-test BVASS
        |
        v
Mell.Reduction.Main.reduce_mell_correct
        |
        +---------------- complete BVAS search ----------------+
                                                               v
                     Mell.Decision.MELL.mell_decide_true_iff
                     Mell.Decision.MELL.mell_decide_false_iff
```

The principal checked declarations are:

- `Mell.Separator.Main.separator_S` — BLS-v1 Theorem 3.3.
- `Mell.Separator.Singleton.singleton_separator` — project corollary producing
  a finite semilinear certificate for one unreachable target.
- `Mell.Reduction.Main.reduce_mell_correct` — the project composition of the
  ordinary-MELL reduction chain.
- `Mell.Decision.MELL.mell_decide_true_iff`,
  `Mell.Decision.MELL.mell_decide_false_iff`, and
  `Mell.Decision.MELL.mell_decide_with_cut` — total decision correctness.
- `Mell.Decision.MELL.mell_search_halts` and
  `Mell.Decision.MELL.decide_code_correct` — eventual finite-certificate
  discovery and the natural-number input interface.

The reduction, fair enumeration, executable certificate checking, codecs,
and their composition into a total Boolean function are original integration
work in this repository.  They should not be attributed wholesale to any one
paper.

## 4. Source-to-Rocq Correspondence

### 4.1 Bizière–Leroux–Sutre, arXiv v1

#### Section 2 and Appendix A

| Source result | Rocq theorem | Location | Relation | Repair | Evidence |
|---|---|---|---|---|---|
| BLS-v1, Lemma 2.1 | `Mell.Order.PeriodicOrder.periodic_order_wqo_iff_finitely_generated` | [`theories/Order/PeriodicOrder.v`](../theories/Order/PeriodicOrder.v) | EXACT statement; ALTERNATIVE PROOF | R11 | [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |
| BLS-v1, Remark 2.2 | `Mell.Geometry.ClosedLinearizationFinite.remark_2_2_full_iff_closed_linearization_fixed` | [`theories/Geometry/ClosedLinearizationFinite.v`](../theories/Geometry/ClosedLinearizationFinite.v) | EXACT | none | [gap closure](review/arxiv-2607.09558v1-fidelity-gap-closure.md) |
| BLS-v1, Example 2.3 | `Mell.Audit.PaperFidelityExamples.paper_example_2_3_not_closed_linearization_fixed` | [`theories/Audit/PaperFidelityExamples.v`](../theories/Audit/PaperFidelityExamples.v) | EXACT regression | guards finite-generation premise | [gap closure](review/arxiv-2607.09558v1-fidelity-gap-closure.md) |

Remark 2.2 explicitly retains `FinitelyGeneratedPeriodic P`.  The executable
Example 2.3 witness for `P = {0} union N_{>0}^2` prevents the false
generalization to arbitrary full periodic sets.

#### Section 3 and Appendix B

| Source result | Rocq theorem | Location | Relation | Repair | Evidence |
|---|---|---|---|---|---|
| BLS-v1, Fact 3.2 | `Mell.BVAS.RunLeafOperations.fact_3_2_all_leaf_increments` | [`theories/BVAS/RunLeafOperations.v`](../theories/BVAS/RunLeafOperations.v) | EXACT / DIRECT | none | [gap closure](review/arxiv-2607.09558v1-fidelity-gap-closure.md) |
| BLS-v1, Theorem 3.3 | `Mell.Separator.Main.separator_S` | [`theories/Separator/Main.v`](../theories/Separator/Main.v) | EXACT / DIRECT | inherits repaired chain below | [Task 11-F audit](review/t11-f-separator-S-audit.md) |
| BLS-v1, Fact 3.6 | `Mell.BVAS.LanguageFlattening.fact_3_6_reach_shuffle_flatten` | [`theories/BVAS/LanguageFlattening.v`](../theories/BVAS/LanguageFlattening.v) | EXACT / DIRECT | none | [gap closure](review/arxiv-2607.09558v1-fidelity-gap-closure.md) |
| BLS-v1, Lemma 3.7 | `Mell.Separator.WitnessUpdate.lemma_3_7_attractor_extension`, transported through `Mell.Audit.PaperFidelityBridges.paper_attractor_iff_attractor` | [`theories/Separator/WitnessUpdate.v`](../theories/Separator/WitnessUpdate.v), [`theories/Audit/PaperFidelityBridges.v`](../theories/Audit/PaperFidelityBridges.v) | EQUIVALENT / BRIDGE | none | [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |
| BLS-v1, Lemma 3.10 | `Mell.BVAS.RunOrderAntisymmetry.lemma_3_10_irun_wpo_amalgamation` | [`theories/BVAS/RunOrderAntisymmetry.v`](../theories/BVAS/RunOrderAntisymmetry.v) | EXACT package | R03 order/WQO boundary; R04 amalgamation proof | [historical ledger audit](review/doc-prov-r-historical-repair-ledger.md) |
| BLS-v1, Appendix B Lemma B.1 | `Mell.BVAS.RunOrderAntisymmetry.irun_le_antisymmetric`; `Mell.Order.FiniteBasis.irun_le_wqo`; `Mell.Order.FiniteBasis.irun_le_finite_cover` | [`theories/BVAS/RunOrderAntisymmetry.v`](../theories/BVAS/RunOrderAntisymmetry.v), [`theories/Order/FiniteBasis.v`](../theories/Order/FiniteBasis.v) | EXACT conclusion; corrected formalization boundary | R03 | [historical ledger audit](review/doc-prov-r-historical-repair-ledger.md) |
| BLS-v1, Appendix B Lemma B.2 | `Mell.BVAS.Amalgamation.run_amalgamation` | [`theories/BVAS/Amalgamation.v`](../theories/BVAS/Amalgamation.v) | EXACT after B.3 proof repair | R04 | [repair counterexample](../theories/Audit/RepairExamples.v) |
| BLS-v1, Appendix B Fact B.3 | `Mell.BVAS.RunOrder.root_same_action_mono` | [`theories/BVAS/RunOrder.v`](../theories/BVAS/RunOrder.v) | REPAIRED standalone statement | R04 | [repair counterexample](../theories/Audit/RepairExamples.v) |
| BLS-v1, Appendix B Fact B.4 | `Mell.BVAS.RunOrder.context_lift` | [`theories/BVAS/RunOrder.v`](../theories/BVAS/RunOrder.v) | EXACT after B.3 proof repair | R04 | [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |
| BLS-v1, Lemma 3.12 | `Mell.Separator.DirectedRuns.lemma_3_12_directed_closed_period_finitely_generated` | [`theories/Separator/DirectedRuns.v`](../theories/Separator/DirectedRuns.v) | EXACT | none | [Task 11-A audit](review/t11-a-doubled-period-geometry-audit.md) |
| BLS-v1, Lemma 3.13 | `Mell.Separator.DirectedRuns.lemma_3_13_directed_closed_period_inclusion` | [`theories/Separator/DirectedRuns.v`](../theories/Separator/DirectedRuns.v) | EXACT | none | [Task 11-A audit](review/t11-a-doubled-period-geometry-audit.md) |

`Fact 3.2` is occurrence-indexed: distinct equal-valued leaves may receive
different increments.  `Fact 3.6` uses ordered word shuffle and assumes only
that every member word of `K` and `L` is nonempty; `K` or `L` itself may be
empty.  For Lemma 3.10, raw `IRun` equality is appropriate: the data contains
ordered children, action values, and configurations, but no embedded validity
proof or rule-occurrence index.  Antisymmetry is proved directly, without a
quotient, UIP, or proof irrelevance.

#### Section 4

| Source result | Rocq theorem | Location | Relation | Repair | Evidence |
|---|---|---|---|---|---|
| BLS-v1, Lemma 4.3 | `Mell.VAS.PeriodicIntersection.periodic_cone_intersection` and projection/sum bridges | [`theories/VAS/PeriodicIntersection.v`](../theories/VAS/PeriodicIntersection.v) | DERIVED | none | [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |
| BLS-v1, Lemma 4.4 | `Mell.Geometry.ClosedLinearizationL2.closed_linearization_finitely_generated` | [`theories/Geometry/ClosedLinearizationL2.v`](../theories/Geometry/ClosedLinearizationL2.v) | EXACT | none | [Task 11-A audit](review/t11-a-doubled-period-geometry-audit.md) |
| BLS-v1, Lemma 4.5 | `Mell.Separator.TransformerPeriod.lemma_4_5_periodic_almost_semilinear_relation` | [`theories/Separator/TransformerPeriod.v`](../theories/Separator/TransformerPeriod.v) | EXACT conclusion; REPAIRED proof boundary | R01 | [repair regression](../theories/Audit/RepairExamples.v) |
| BLS-v1, Lemma 4.6 | `Mell.Separator.DoubledRelation.lemma_4_6_special_leaf_inter_semilinear` | [`theories/Separator/DoubledRelation.v`](../theories/Separator/DoubledRelation.v) | EXACT conclusion; corrected construction order | R02 | [Task 11-A audit](review/t11-a-doubled-period-geometry-audit.md) |
| BLS-v1, Lemma 4.7 | `Mell.Geometry.CenterPushIn.closed_linearization_push_in` | [`theories/Geometry/CenterPushIn.v`](../theories/Geometry/CenterPushIn.v) | EXACT | none | [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |
| BLS-v1, Lemma 4.8 | `Mell.Geometry.CenterCharacterization.center_characterization` | [`theories/Geometry/CenterCharacterization.v`](../theories/Geometry/CenterCharacterization.v) | EXACT | none | [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |
| BLS-v1, Lemma 4.9 | `Mell.Geometry.CenterAbsorption.center_absorbs_closed_linearization` | [`theories/Geometry/CenterAbsorption.v`](../theories/Geometry/CenterAbsorption.v) | EXACT | none | [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |
| BLS-v1, Lemma 4.10 | `Mell.Separator.TransformerPeriod.lemma_4_10_special_transformer_asymptotically_definable` | [`theories/Separator/TransformerPeriod.v`](../theories/Separator/TransformerPeriod.v) | EXACT | none | [Task 11-A audit](review/t11-a-doubled-period-geometry-audit.md) |
| BLS-v1, Lemma 4.11 | `Mell.Separator.TransformerPeriod.lemma_4_11_irun_period_asymptotically_definable` | [`theories/Separator/TransformerPeriod.v`](../theories/Separator/TransformerPeriod.v) | EXACT | none | [Task 11-A audit](review/t11-a-doubled-period-geometry-audit.md) |

The strict-cone repair is a proof repair, not a stronger public Lemma 4.5:
allowing a zero component coefficient adds a boundary ray; the checked
two-dimensional counterexample distinguishes the two sets.

#### Section 5 and Appendix C

| Source result | Rocq theorem | Location | Relation | Repair | Evidence |
|---|---|---|---|---|---|
| BLS-v1, Lemma 5.1 | `Mell.Separator.SafeLinearization.lemma_5_1_bvas_safe_linearization` | [`theories/Separator/SafeLinearization.v`](../theories/Separator/SafeLinearization.v) | EXACT | none | [Task 11-C audit](review/t11-c-safe-linearization-audit.md) |
| BLS-v1, Lemma 5.2 | `Mell.WSVAS.Amalgamation.lemma_5_2_wsvas_runs_wqo_amalgamation` | [`theories/WSVAS/Amalgamation.v`](../theories/WSVAS/Amalgamation.v) | EXACT | none | [Task 11-B audit](review/t11-b-wsvas-amalgamation-audit.md) |
| BLS-v1, Corollary 5.3 | `Mell.WSVAS.Amalgamation.corollary_5_3_wsvas_run_scaling` | [`theories/WSVAS/Amalgamation.v`](../theories/WSVAS/Amalgamation.v) | EQUIVALENT | none | [Task 11-B audit](review/t11-b-wsvas-amalgamation-audit.md) |
| BLS-v1, Lemma 5.4 | `Mell.WSVAS.SafeLinearization.lemma_5_4_wsvas_safe_linearization` | [`theories/WSVAS/SafeLinearization.v`](../theories/WSVAS/SafeLinearization.v) | EXACT | none | [Task 11-C audit](review/t11-c-safe-linearization-audit.md) |
| BLS-v1, Lemma 5.5 (WSVAS equality) | `Mell.WSVAS.Runs.valid_ws_run_step_star`; `Mell.Separator.SafeLinearization.ws_step_star_has_run` | [`theories/WSVAS/Runs.v`](../theories/WSVAS/Runs.v), [`theories/Separator/SafeLinearization.v`](../theories/Separator/SafeLinearization.v) | DERIVED | none | [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |
| BLS-v1, Lemma 5.5 (BVAS equality) | `Mell.WSVAS.BVASSimulation.lemma_5_5_bvas_wsvas_reach_iff` | [`theories/WSVAS/BVASSimulation.v`](../theories/WSVAS/BVASSimulation.v) | EQUIVALENT | none | [Task 11-B audit](review/t11-b-wsvas-amalgamation-audit.md) |
| BLS-v1, Lemma 5.6 | `Mell.Audit.PaperFidelityBridges.paper_lemma_5_6_bvas_wsvas_exists` | [`theories/Audit/PaperFidelityBridges.v`](../theories/Audit/PaperFidelityBridges.v) | EQUIVALENT / BRIDGE | none | [gap closure](review/arxiv-2607.09558v1-fidelity-gap-closure.md) |
| BLS-v1, Lemma 5.7 | `Mell.BVAS.OneSourceReduction.lemma_5_7_one_source_reduction` | [`theories/BVAS/OneSourceReduction.v`](../theories/BVAS/OneSourceReduction.v) | EXACT conclusion; explicit leaf proof case | R06 | [Task 11-C audit](review/t11-c-safe-linearization-audit.md) |
| BLS-v1, Appendix C Lemma C.1 | `Mell.WSVAS.RunOrder.lemma_c_1_wsrun_order_iff_higman` | [`theories/WSVAS/RunOrder.v`](../theories/WSVAS/RunOrder.v) | EXACT | none | [Task 11-B audit](review/t11-b-wsvas-amalgamation-audit.md) |
| BLS-v1, Appendix C Corollary C.2 | `Mell.WSVAS.RunOrder.corollary_c_2_wsrun_wqo` | [`theories/WSVAS/RunOrder.v`](../theories/WSVAS/RunOrder.v) | EXACT | none | [Task 11-B audit](review/t11-b-wsvas-amalgamation-audit.md) |
| BLS-v1, Appendix C Corollary C.3 | `Mell.WSVAS.Amalgamation.ws_run_order_stitch` and concatenation lemmas | [`theories/WSVAS/Amalgamation.v`](../theories/WSVAS/Amalgamation.v) | DERIVED | none | [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |
| BLS-v1, Appendix C Lemma C.4 | `Mell.WSVAS.Amalgamation.lemma_c_4_wsrun_exact_amalgamation` | [`theories/WSVAS/Amalgamation.v`](../theories/WSVAS/Amalgamation.v) | EXACT | none | [Task 11-B audit](review/t11-b-wsvas-amalgamation-audit.md) |

The paper-shaped Lemma 5.6 has only `Semilinear A` as caller-visible
hypothesis.  It existentially hides the concrete `SemiCode`; it does not add
closure, attractor, decidability, or executable code-selection premises.

#### Section 6

| Source result | Rocq theorem | Location | Relation | Repair | Evidence |
|---|---|---|---|---|---|
| BLS-v1, Theorem 6.1 | `Mell.Geometry.FaceStrippingTheorem.face_stripping_theorem` | [`theories/Geometry/FaceStrippingTheorem.v`](../theories/Geometry/FaceStrippingTheorem.v) | EQUIVALENT; repaired proof chain | R07–R09 | [Task 11-D audit](review/t11-d-face-stripping-audit.md) |
| BLS-v1, Lemma 6.3 | `Mell.Geometry.FaceStrippingDiagonal.lemma_6_3_stripping_diagonal` | [`theories/Geometry/FaceStrippingDiagonal.v`](../theories/Geometry/FaceStrippingDiagonal.v) | EXACT no-backward-edge conclusion; repaired indexing/proof | R09 | [Task 11-D audit](review/t11-d-face-stripping-audit.md) |
| BLS-v1, Lemma 6.5 | `Mell.Geometry.FaceZeroPatternWitness.face_zero_pattern_witness` | [`theories/Geometry/FaceZeroPatternWitness.v`](../theories/Geometry/FaceZeroPatternWitness.v) | EQUIVALENT | none | [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |
| BLS-v1, Lemma 6.6 | `Mell.Geometry.FaceStrippingBases.integer_affine_inequalities_finitary` | [`theories/Geometry/FaceStrippingBases.v`](../theories/Geometry/FaceStrippingBases.v) | DERIVED / ALTERNATIVE PROOF | none | [finite-basis audit](review/t10-c4-3b-1-b1-audit.md) |
| BLS-v1, Corollary 6.7 | `Mell.Geometry.Corollary67Finitary.corollary_6_7_finitary` | [`theories/Geometry/Corollary67Finitary.v`](../theories/Geometry/Corollary67Finitary.v) | EXACT | none | [Task 11-D audit](review/t11-d-face-stripping-audit.md) |
| BLS-v1, Lemma 6.8 | `Mell.Geometry.FaceStrippingExtract.extract_remainder_cylindric` | [`theories/Geometry/FaceStrippingExtract.v`](../theories/Geometry/FaceStrippingExtract.v) | EXACT conclusion; repaired argument order | R08 | [Task 11-D audit](review/t11-d-face-stripping-audit.md) |
| BLS-v1, Lemma 6.9 | `Mell.Geometry.FaceStrippingMinimalFace.lemma_6_9_minimal_extract`; `Mell.Geometry.FaceStrippingMinimalFace.lemma_6_9_any_minimal_face` | [`theories/Geometry/FaceStrippingMinimalFace.v`](../theories/Geometry/FaceStrippingMinimalFace.v) | EXACT | none | [minimal-face audit](review/t10-c4-3d0-minimal-face-audit.md) |
| BLS-v1, Lemma 6.10 | `Mell.Geometry.FaceStrippingLemma610FiniteBasis.lemma_6_10_maximal_extract_finitary` | [`theories/Geometry/FaceStrippingLemma610FiniteBasis.v`](../theories/Geometry/FaceStrippingLemma610FiniteBasis.v) | EXACT conclusion; repaired difference-membership proof | R07 | [Lemma 6.10 audit](review/t10-c4-3c2-lemma610-audit.md) |
| BLS-v1, Lemma 6.11 | `Mell.Geometry.FaceStrippingLemma611.lemma_6_11_stripping_invariants` | [`theories/Geometry/FaceStrippingLemma611.v`](../theories/Geometry/FaceStrippingLemma611.v) | EQUIVALENT | none | [Lemma 6.11 audit](review/t10-c4-3d2-lemma-611-audit.md) |

Lemma 6.6 and Corollary 6.7 are not omitted: the former is proved from the
checked lattice/Gordan development, and the latter is applied directly in
`Mell.Geometry.FaceStrippingGeometricCore` on the path to Lemma 6.10.

#### Section 7 and the paper attractor

| Source result | Rocq theorem | Location | Relation | Repair | Evidence |
|---|---|---|---|---|---|
| BLS-v1, attractor definition | `Mell.Audit.PaperFidelityBridges.PaperAttractor`; `Mell.Audit.PaperFidelityBridges.paper_attractor_iff_attractor` | [`theories/Audit/PaperFidelityBridges.v`](../theories/Audit/PaperFidelityBridges.v) | EQUIVALENT / BRIDGE | R10 witness contract | [gap closure](review/arxiv-2607.09558v1-fidelity-gap-closure.md) |
| BLS-v1, Lemma 7.1 | `Mell.Audit.PaperFidelityBridges.paper_lemma_7_1_safety_witness_rank_descent` | [`theories/Audit/PaperFidelityBridges.v`](../theories/Audit/PaperFidelityBridges.v) | EQUIVALENT / BRIDGE; strict rank decrease checked | R10 | [Task 11-E audit](review/t11-e-safety-witness-rank-decrease-audit.md) |
| BLS-v1, Lemma 7.2 | `Mell.Separator.WitnessUpdate.lemma_7_2_safety_witness_successors` | [`theories/Separator/WitnessUpdate.v`](../theories/Separator/WitnessUpdate.v) | EQUIVALENT pointwise form | none | [Task 11-E audit](review/t11-e-safety-witness-rank-decrease-audit.md) |
| BLS-v1, Lemma 7.3 | `Mell.Separator.WitnessUpdate.lemma_7_3_attractor_contact_propagation` | [`theories/Separator/WitnessUpdate.v`](../theories/Separator/WitnessUpdate.v) | EXACT; Rocq is slightly more general | none | [Task 11-E audit](review/t11-e-safety-witness-rank-decrease-audit.md) |
| BLS-v1, Lemma 7.4 | `Mell.Separator.WitnessUpdate.lemma_7_4_directed_irun_rebase` | [`theories/Separator/WitnessUpdate.v`](../theories/Separator/WitnessUpdate.v) | EXACT | none | [Task 11-E audit](review/t11-e-safety-witness-rank-decrease-audit.md) |
| BLS-v1, Lemma 7.5 | `Mell.Separator.WitnessUpdate.lemma_7_5_new_node_edge_direction`; `Mell.Separator.WitnessUpdate.replacement_edge_stays_new_and_nondecreasing` | [`theories/Separator/WitnessUpdate.v`](../theories/Separator/WitnessUpdate.v) | DERIVED / EXACT conjunction; repaired index/direction proof | R09 | [Task 11-E audit](review/t11-e-safety-witness-rank-decrease-audit.md) |

`PaperAttractor` is exactly `Reach(A+ shuffle Initial(S)*) subset A`.  The
unconditional equivalence to the internal reachable-side `Attractor` uses
Fact 3.6; it assumes neither semilinearity nor invariant closure.  Conversion
between `PaperSafetyWitness` and the internal witness preserves the node list,
full-run coverage, homogeneity, and strict `WitnessRankLess` result.

### 4.2 Bizière–Leroux–Sutre, FoSSaCS 2026

| Source result | Rocq theorem | Location | Relation | Repair | Evidence |
|---|---|---|---|---|---|
| Proposition 5 | `Mell.BVASS.StatefulAmalgamation.inserted_family_amalgamation`; `Mell.BVASS.StatefulAmalgamation.stateful_context_order_amalgamation` | [`theories/BVASS/StatefulAmalgamation.v`](../theories/BVASS/StatefulAmalgamation.v) | EQUIVALENT / DIRECT | R05 representation repair | [E0 audit](review/t10-e0-stateful-amalgamation-audit.md) |
| Lemma 6 | `Mell.BVASS.OrderedBridge.ordered_embed_implies_context_insert` | [`theories/BVASS/OrderedBridge.v`](../theories/BVASS/OrderedBridge.v) | NOT REQUIRED as a biconditional; one strong sufficient direction is checked | R05 | [stateful-order audit](review/t09-stateful-bvass-audit.md) |
| Corollary 7 | `Mell.Order.FiniteBasis.context_order_wqo`; `Mell.Order.FiniteBasis.context_order_finite_cover` | [`theories/Order/FiniteBasis.v`](../theories/Order/FiniteBasis.v) | DERIVED / ALTERNATIVE PROOF | R05 | [stateful-order audit](review/t09-stateful-bvass-audit.md) |
| Lemma 8 | `Mell.BVASS.StatefulAmalgamation.stateful_context_transfer_lemma_8` | [`theories/BVASS/StatefulAmalgamation.v`](../theories/BVASS/StatefulAmalgamation.v) | EQUIVALENT | R05-compatible occurrence path | [E0 audit](review/t10-e0-stateful-amalgamation-audit.md) |
| Lemma 9 | `Mell.BVASS.BoundedBranching.lemma_9_uniform_bounded_branching`; `Mell.BVASS.BoundedBranching.lemma_9_reach_bounded_branching_iff` | [`theories/BVASS/BoundedBranching.v`](../theories/BVASS/BoundedBranching.v) | EXACT / EQUIVALENT | none | [E2 audit](review/t10-e2-bounded-branching-audit.md) |
| Lemma 11 | `Mell.BVASS.BoundedVASSSection.bounded_vass_section_correct`; `Mell.BVASS.BoundedVASSSection.lemma_11_bounded_depth_vass_section` | [`theories/BVASS/BoundedVASSSection.v`](../theories/BVASS/BoundedVASSSection.v) | EQUIVALENT | none | [E3 audit](review/t10-e3-bounded-vass-section-audit.md) |
| Theorem 12 | `Mell.BVASS.AlmostSemilinear.bvass_reach_is_vass_section` | [`theories/BVASS/AlmostSemilinear.v`](../theories/BVASS/AlmostSemilinear.v) | EQUIVALENT | none | [E4 audit](review/t10-e4-theorem12-corollary14-audit.md) |
| Corollary 14 | `Mell.BVASS.AlmostSemilinear.vass_section_inter_semilinear`; `Mell.BVASS.AlmostSemilinear.bvass_reach_inter_semilinear` | [`theories/BVASS/AlmostSemilinear.v`](../theories/BVASS/AlmostSemilinear.v) | EQUIVALENT | none | [E4 audit](review/t10-e4-theorem12-corollary14-audit.md) |

The complete Lemma 6 biconditional is deliberately not claimed.  A fixed
child-position decoration is too strong in the presence of child permutation.
The development proves that its stronger ordered relation implies the genuine
context insertion relation, then obtains Corollary 7 by an alternative WQO
argument.  This preserves the downstream theorem statements and duplicate
child multiplicities.

### 4.3 Leroux 2012

| Source result | Rocq theorem | Location | Relation | Repair | Evidence |
|---|---|---|---|---|---|
| Lemma 3.1 | `Mell.VAS.Runs.vas_reach_monotone` | [`theories/VAS/Runs.v`](../theories/VAS/Runs.v) | EXACT | none | [VAS audit](review/t10-d-task1-vas-jancar-audit.md) |
| Lemma 4.1 | `Mell.VAS.JancarOrder.jancar_run_wqo` | [`theories/VAS/JancarOrder.v`](../theories/VAS/JancarOrder.v) | EQUIVALENT | none | [VAS audit](review/t10-d-task1-vas-jancar-audit.md) |
| Lemma 5.1 | `Mell.VAS.AsymptoticRelation.lemma_5_1_asymptotic_relation_compose`; `Mell.VAS.AsymptoticRelation.lemma_5_1_nrelation_compose` | [`theories/VAS/AsymptoticRelation.v`](../theories/VAS/AsymptoticRelation.v) | EXACT / DERIVED factorization | none | [composition audit](review/t10-d-task2b-asymptotic-relation-audit.md) |
| Lemma 5.2 | `Mell.VAS.Transformer.capacity_transformer_periodic`; `Mell.VAS.Transformer.transformer_along_run_periodic` | [`theories/VAS/Transformer.v`](../theories/VAS/Transformer.v) | EXACT | none | [transformer audit](review/t10-d-task2a-transformer-audit.md) |
| Lemma 5.5 | `Mell.VAS.Intraproductions.lemma_5_5_qgamma_add_intraproduction` | [`theories/VAS/Intraproductions.v`](../theories/VAS/Intraproductions.v) | EXACT | none | [intraproduction audit](review/t10-d-task3a-intraproductions-audit.md) |
| Lemma 5.6 | `Mell.VAS.Intraproductions.lemma_5_6_intraproduction_dominates` | [`theories/VAS/Intraproductions.v`](../theories/VAS/Intraproductions.v) | EXACT | none | [intraproduction audit](review/t10-d-task3a-intraproductions-audit.md) |
| Lemma 5.7 | `Mell.VAS.IntraproductionsLemma57.lemma_5_7_bounded_coordinates_intraproduction` | [`theories/VAS/IntraproductionsLemma57.v`](../theories/VAS/IntraproductionsLemma57.v) | EXACT | none | [Lemma 5.7 audit](review/t10-d-task3b-lemma57-audit.md) |
| Corollary 5.10 | `Mell.VAS.ProductionGraphPaths.corollary_5_10_production_graph_strongly_connected` | [`theories/VAS/ProductionGraphPaths.v`](../theories/VAS/ProductionGraphPaths.v) | EXACT | none | [production-graph audit](review/t10-d-task4a-production-graph-audit.md) |
| Corollary 5.12 | `Mell.VAS.ProductionGraphFiniteness.corollary_5_12_production_graph_class_finite` | [`theories/VAS/ProductionGraphFiniteness.v`](../theories/VAS/ProductionGraphFiniteness.v) | EQUIVALENT finite catalog | none | [finiteness audit](review/t10-d-task4b-production-graph-finiteness-audit.md) |
| Lemma 5.14 | `Mell.VAS.KirchhoffLemma514.lemma_5_14_gamma_in_kirchhoff_relation` | [`theories/VAS/KirchhoffLemma514.v`](../theories/VAS/KirchhoffLemma514.v) | EXACT | none | [Lemma 5.14 audit](review/t10-d-task5b-kirchhoff-relation-audit.md) |
| Lemma 5.15 | `Mell.VAS.KirchhoffLemma515.lemma_5_15_kirchhoff_in_capacity_cone` | [`theories/VAS/KirchhoffLemma515.v`](../theories/VAS/KirchhoffLemma515.v) | EXACT | none | [Lemma 5.15 audit](review/t10-d-task5c-lemma515-audit.md) |
| Corollary 5.16 | `Mell.VAS.KirchhoffCorollary516.corollary_5_16_capacity_transformer_asymptotically_definable`; `Mell.VAS.KirchhoffCorollary516.transformer_along_run_asymptotically_definable` | [`theories/VAS/KirchhoffCorollary516.v`](../theories/VAS/KirchhoffCorollary516.v) | EXACT | none | [Corollary 5.16 audit](review/t10-d-task5d-corollary516-audit.md) |
| Lemma 6.1 | `Mell.VAS.MinimalRunDecomposition.lemma_6_1_linear_reach_decomposition` | [`theories/VAS/MinimalRunDecomposition.v`](../theories/VAS/MinimalRunDecomposition.v) | EQUIVALENT finite downward-cover basis | none | [Lemma 6.1 audit](review/t10-d-task6b-lemma61-audit.md) |
| Lemma 6.2 | `Mell.VAS.PeriodicIntersection.lemma_6_2_qdefinable_intersection`; `Mell.VAS.PeriodicIntersection.lemma_6_2_asymptotically_definable_intersection` | [`theories/VAS/PeriodicIntersection.v`](../theories/VAS/PeriodicIntersection.v) | EXACT | none | [Lemma 6.2 audit](review/t10-d-task6c-lemma62-almost-semilinear-audit.md) |
| Corollary 6.3 | `Mell.VAS.Corollary63.corollary_6_3_plain_post_inter_almost_semilinear`; `Mell.VAS.Corollary63.corollary_6_3_plain_pre_inter_almost_semilinear` | [`theories/VAS/Corollary63.v`](../theories/VAS/Corollary63.v) | EXACT | none | [Corollary 6.3 audit](review/t10-d-task6d-corollary63-stateful-audit.md) |
| Corollary 6.3, finite-control lift | `Mell.VAS.StatefulAlmostSemilinear.vas_reach_relation_inter_semilinear`; `Mell.VAS.StatefulAlmostSemilinear.vas_post_inter_semilinear` | [`theories/VAS/StatefulAlmostSemilinear.v`](../theories/VAS/StatefulAlmostSemilinear.v) | EQUIVALENT / BRIDGE | none | [Corollary 6.3 audit](review/t10-d-task6d-corollary63-stateful-audit.md) |

This is the dependency chain supporting FoSSaCS Corollary 14.  The 2012
result is not cited as an opaque theorem: transformer, production-graph,
Kirchhoff, minimal-run, intersection, and projection obligations are all
represented by checked declarations.

### 4.4 Lazić–Schmitz 2015

| Source result | Rocq theorem | Location | Relation | Repair | Evidence |
|---|---|---|---|---|---|
| Fact 8, ordinary LL/MELL base translation | `Mell.Reduction.ILZ.mell_ilz_iff` | [`theories/Reduction/ILZ.v`](../theories/Reduction/ILZ.v) | EQUIVALENT / BRIDGE through YALLA | none | [reduction audit](review/t10-f-mell-to-bvas-reduction-audit.md) |
| Section 4.1.2, Claim 9.1 | `Mell.Reduction.MELLToABVASSCompleteness.ilz_machine_correct` | [`theories/Reduction/MELLToABVASSCompleteness.v`](../theories/Reduction/MELLToABVASSCompleteness.v) | EQUIVALENT root acceptance | none | [reduction audit](review/t10-f-mell-to-bvas-reduction-audit.md) |
| Section 4.1.2, fork-free construction | `Mell.Reduction.MELLToABVASS.ilz_machine_fork_free` | [`theories/Reduction/MELLToABVASS.v`](../theories/Reduction/MELLToABVASS.v) | EXACT property | none | [reduction audit](review/t10-f-mell-to-bvas-reduction-audit.md) |
| Lemma 3, first full-zero-test construction | `Mell.Reduction.ZeroTest.remove_zero_tests_correct` | [`theories/Reduction/ZeroTest.v`](../theories/Reduction/ZeroTest.v) | EQUIVALENT semantics | none | [reduction audit](review/t10-f-mell-to-bvas-reduction-audit.md) |
| Overall ordinary-MELL reduction | `Mell.Reduction.Main.reduce_mell_correct` | [`theories/Reduction/Main.v`](../theories/Reduction/Main.v) | DERIVED / ALTERNATIVE composition | none | [reduction audit](review/t10-f-mell-to-bvas-reduction-audit.md) |
| Executable coded reduction | `Mell.Reduction.Main.reduce_mell_code_correct`; `Mell.Reduction.Main.reduce_mell_many_one` | [`theories/Reduction/Main.v`](../theories/Reduction/Main.v) | project-original DERIVED result | none | [reduction audit](review/t10-f-mell-to-bvas-reduction-audit.md) |

Proposition 7(2) concerns affine/contractive MELL and lossy/expansive
BVASS-with-zero-tests.  The present ordinary-MELL theorem is therefore not
labelled an EXACT formalization of Proposition 7(2).  It composes the base
translation in Fact 8, Claim 9.1, Lemma 3's first construction, and the checked
state-erasure bridge.  Lemma 3's later dimension-preserving Turing reduction
and its complexity bounds are **NOT REQUIRED**.

### 4.5 Other Mathematical Sources

| Source result | Rocq theorem | Location | Relation | Repair | Evidence |
|---|---|---|---|---|---|
| Leroux 2011, attributed Theorem 3.5 narrow consequence | `Mell.Geometry.RationalConeAssembly.rational_closed_cone_finitely_generated`; `Mell.Geometry.LatticeGordanInterface.rational_closed_cone_is_polyhedral` | [`theories/Geometry/RationalConeAssembly.v`](../theories/Geometry/RationalConeAssembly.v), [`theories/Geometry/LatticeGordanInterface.v`](../theories/Geometry/LatticeGordanInterface.v) | DERIVED / ALTERNATIVE PROOF; source-number match UNVERIFIED | none | [`sources.json`](review/sources.json) |
| Schrijver 1999, Corollary 7.1b as cited by BLS-v1 Lemma 6.6 | `Mell.Geometry.FaceStrippingBases.integer_affine_inequalities_finitary` | [`theories/Geometry/FaceStrippingBases.v`](../theories/Geometry/FaceStrippingBases.v) | DERIVED / ALTERNATIVE PROOF | none | [finite-basis audit](review/t10-c4-3b-1-b1-audit.md) |
| Dickson/Higman/Kruskal WQO principles | concrete `afs` closure and embedding theorems used by run-order modules | [`theories/Order/AlmostFullBridge.v`](../theories/Order/AlmostFullBridge.v), [`theories/BVAS/RunOrder.v`](../theories/BVAS/RunOrder.v), [`theories/WSVAS/RunOrder.v`](../theories/WSVAS/RunOrder.v) | formal-library instantiations | R11 where signed orthants matter | [`library-coverage.json`](review/library-coverage.json) |

The first two rows replace an external appeal with a local proof; they are not
additional axioms.  The retained records do not support a stronger claim that
the complete Leroux 2011 theorem has been reproduced under the same number.

## 5. Corrections and Formalization Repairs

### 5.1 Evidence-backed repair ledger

The historical ID definitions are verified against the user-provided
17 October 2026 design source.  The source is outside this Git repository and
is therefore identified by content hash, not silently treated as a tracked
project artifact.  It was a design contract, not implementation evidence.
Each row consequently gives both the historical definition and the separately
checked present realization.  “Exact conclusion” means that the numbered
source result is not classified as a repaired proposition merely because its
proof or formal representation required repair.

| ID | Source result | Problem and repair | Kind | Checked result / evidence |
|---|---|---|---|---|
| R01 | BLS-v1, Lemma 4.5 | Use `Con(P) = {0} union union_i (Q_{>0} b_i + Con(P_i))`; the component coefficient is strictly positive.  Allowing zero adds a boundary ray. | proof/intermediate-equality repair; numbered conclusion exact | `Mell.Geometry.Cone.periodic_cone_union_strict`; `Mell.Separator.TransformerPeriod.lemma_4_5_periodic_almost_semilinear_relation`; checked one- and two-dimensional regressions in [`RepairExamples.v`](../theories/Audit/RepairExamples.v) |
| R02 | BLS-v1, Lemma 4.6 | Intersect the doubled reachability set with the marker/control restriction and the semilinear relation before projecting to the input/output coordinates; retain only marker total one (the design describes the 0/1 control cases). | proof-construction repair; numbered conclusion exact | `Mell.Separator.DoubledRelation.doubled_restriction_semilinear`, `doubled_projection_iff`, and `lemma_4_6_special_leaf_inter_semilinear`; [Task 11-A audit](review/t11-a-doubled-period-geometry-audit.md) |
| R03 | BLS-v1, Appendix B.1 | Preserve zero-child leaves, ordered child positions, and an independent root-output comparison in the exact `IRunLe`; prove its WQO and finite-cover basis.  Current actions have positive arity, so arity zero is represented by the explicit leaf label, not a nullary action. | representation/formalization repair; Appendix B.1 conclusion exact | `Mell.BVAS.RunOrder.IRunLe`; `Mell.Order.FiniteBasis.irun_le_wqo`; `Mell.Order.FiniteBasis.irun_le_finite_cover`; [historical ledger audit](review/doc-prov-r-historical-repair-ledger.md) |
| R04 | BLS-v1, Appendix B Fact B.3 / Lemma B.2 | Require the same action and ordered child comparison at the parent, lift through contexts, and retain the exact additive amalgamation equation.  The standalone old Fact B.3 is false for equal-output runs using different actions. | Fact B.3 statement repair with counterexample; Lemma B.2 proof repair and exact conclusion | `Mell.BVAS.RunOrder.root_same_action_mono`; `Mell.BVAS.RunOrder.context_lift`; `Mell.BVAS.Amalgamation.run_amalgamation`; `Mell.Audit.RepairExamples.old_fact_b3_missing_same_action` |
| R05 | BLS-FoSSaCS, Lemma 6 | From root-configuration comparison plus ordered-decoration embedding prove only the sound implication to the original context order; do not replace that occurrence-sensitive order in downstream amalgamation. | representation/proof repair; full biconditional not required | `Mell.BVASS.OrderedBridge.ordered_embed_implies_context_insert`; `Mell.BVASS.StatefulAmalgamation.stateful_context_order_amalgamation`; [stateful-order audit](review/t09-stateful-bvass-audit.md); [permutation regression](../theories/Audit/BridgeExamples.v) |
| R06 | BLS-v1, Lemma 5.7 | Handle a run consisting only of the distinguished leaf explicitly, without requiring that leaf to occur in the IBVAS initial list. | proof-case completion; numbered conclusion exact | `Mell.BVAS.OneSourceReduction.compress_free_run`; `Mell.BVAS.OneSourceReduction.lemma_5_7_one_source_reduction`; [Task 11-C audit](review/t11-c-safe-linearization-audit.md) |
| R07 | BLS-v1, Lemma 6.10 | Use period membership of differences `s_n-s_m`, not the generally false claim that translated sequence elements lie in `Q`; apply fullness only after difference-group and cone membership are established. | proof correction; numbered conclusion exact | `Mell.Geometry.FaceStrippingLemma610FiniteBasis.lemma_6_10_maximal_extract_finitary`; [audit](review/t11-d-face-stripping-audit.md); [regression](../theories/Audit/FaceStrippingSection6Examples.v) |
| R08 | historical locator: Lemma 6.11 / Theorem 6.1; current BLS-v1 correspondence: Lemma 6.8 | Preserve `ExtractFace Q F excluded remaining`: remove the excluded/lower set from the current remainder.  The historical locator is retained rather than silently renumbered to the present correspondence table. | notation/argument-order correction; numbered conclusion exact | `Mell.Geometry.FaceStrippingExtract.extract_remainder_cylindric`; [audit and regression](review/t11-d-face-stripping-audit.md) |
| R09 | BLS-v1, Lemma 6.3 / Lemma 7.5 | Translate the historical one-based `1 <= i < j <= n` convention to the implementation's zero-based slices, prove target-difference membership, and forbid later-to-earlier edges without forbidding the converse. | index/direction proof correction; mathematical direction exact | `Mell.Geometry.FaceStrippingDiagonal.lemma_6_3_stripping_diagonal`; `Mell.Separator.WitnessUpdate.lemma_7_5_new_node_edge_direction`; [audit](review/t11-d-face-stripping-audit.md); [regression](../theories/Audit/FaceStrippingDiagonalExamples.v) |
| R10 | BLS-v1, Section 7 | Preserve SCC-local homogeneity, the paper attractor, and coverage of complete valid runs; compare counts by cone dimension from high to low and prove strict rank decrease. | witness-contract/rank proof repair; no automatic repaired-proposition claim | `Mell.Separator.SafetyWitness.HomogeneousWitnessNodes`; `witness_run_coverage`; `Mell.Audit.PaperFidelityBridges.paper_attractor_iff_attractor`; `Mell.Separator.RankDecrease.witness_rank_less_well_founded`; `Mell.Separator.WitnessUpdate.lemma_7_1_safety_witness_rank_descent`; [Task 11-E audit](review/t11-e-safety-witness-rank-decrease-audit.md) |
| R11 | BLS-v1, Appendix A / Lemma 2.1 | After sign reflection restrict to `Q_s = f_s(P) intersection N^d`; combine the periodic order and Dickson coordinate order only on that carrier, and derive the nonnegative difference there. | proof correction; Lemma 2.1 statement exact | `Mell.Order.PeriodicOrder.periodic_order_wqo_iff_finitely_generated`; [fidelity audit](review/arxiv-2607.09558v1-fidelity-audit.md) |

The R03/R04 boundary is historical, not a new renumbering: R03 owns the exact
initialized-run order and its WQO/finite basis, while R04 owns the same-action
parent lemma, context lifting, and exact amalgamation equation.  The
same-output/different-action counterexample therefore belongs to R04.

### 5.2 Why the repairs do not weaken the main theorem

R01, R02, R04, R06, R07--R11 repair proof steps, intermediate statements,
representations, or witness invariants as specified above; R03 fixes the exact
formal order used by the Appendix-B proof.  R05 uses the paper's unordered,
occurrence-sensitive context meaning rather than a stronger positional
surrogate.  R07--R09 retain Theorem 6.1's decomposition and Lemmas 6.3/7.5's
mathematical direction.  R11 does not change Lemma 2.1, and R01 does not change
Lemma 4.5's conclusion.  Only the standalone, under-specified Fact B.3 is
classified as a repaired source statement.  None of these repairs adds a
caller-visible hypothesis to `separator_S`.

## 6. Alternative Proofs and Unused Intermediate Results

- FoSSaCS Lemma 6's full ordered-decoration biconditional is **NOT REQUIRED**.
  The one sound implication plus a direct WQO bridge proves Corollary 7 and all
  downstream results.
- Lazić–Schmitz Proposition 7(2), Lemma 3's second reduction, and their
  complexity claims are **NOT REQUIRED** for the exact ordinary-MELL semantic
  equivalence proved here.
- BLS-v1 Lemma 6.6 is proved locally through lattice/Gordan and integer
  inequality modules rather than accepted from Schrijver.  Its consequence,
  Corollary 6.7, is nevertheless used directly by the Lemma 6.10 development;
  neither item is unused.
- BLS-v1 Corollary C.3 is not exported under its paper number, but its stitching
  content is proved and used by `ws_run_order_stitch` and the Lemma C.4 proof.
- Examples 3.1, 3.5, 3.8, 3.9, 6.2, and 6.4 are explanatory and are not logical
  dependencies.  Repair-relevant counterexamples are retained as executable
  audit examples.

## 7. Formal Library Dependencies

These are formal proof dependencies, not direct mathematical citations of the
project's main theorem.  Exact pins and licenses are in
[`review/sources.json`](review/sources.json) and
[`THIRD_PARTY_NOTICES`](../THIRD_PARTY_NOTICES).

| Library | Fixed version | Formal role |
|---|---|---|
| Coq | 8.20.1 | Kernel, standard arithmetic, constructive search over natural stages, and extraction framework. |
| YALLA | 2.0.6 | MELL fragment semantics, classical/intuitionistic linear-logic bridge, and cut admissibility on the proof side.  Runtime ILZ computation is separated from these proof objects. |
| Coq-Kruskal packages | Kruskal-Trees 1.5, Finite 1.5, AlmostFull 1.2, Fan 1.2, Higman 1.3, Veldman 1.3, Theorems 1.2 | Prop-valued almost-full/WQO results for list and tree embeddings. |
| MathComp / finmap / bigenough forks | commits and version in `sources.json` | Finite algebra, matrices, rational arithmetic, finite maps, and bounded-index infrastructure. |
| Coq-Polyhedra | commit `f8b8ce8ebf2516ea1ee4aa6385435204c04d0b5a` | Rational polyhedra, H/V cone representations, faces, and Farkas infrastructure.  The project does not attribute its local Gordan and rational-closure theorems to an absent library theorem. |
| MiniCooper | vendored commit `3f051307039456a88cf093921278b0dcf224f7cf` | Verified Presburger quantifier elimination.  The key bridge is `MiniCooper.Theory.interpret_qe`; the project wrapper is `Mell.Presburger.Decide.presburger_decide_correct`. |

The rejected `rocq-archive/presburger` candidate is recorded in
`sources.json` but is not a build or proof dependency.

## 8. Assumptions and Trust Boundary

Targeted `Check` commands at the audited commit confirmed the fully qualified
names above.  Targeted `Print Assumptions` produced:

- `Mell.Reduction.Main.reduce_mell_correct`: closed under the global context;
- `Mell.Separator.Main.separator_S`: only `Classical_Prop.classic`;
- `Mell.Decision.MELL.mell_decide_true_iff`: only
  `Classical_Prop.classic`.

The paper-facing Fact 3.2, Fact 3.6, Remark 2.2, Lemma 3.10 antisymmetry,
Attractor equivalence, and Lemma 5.6 bridge are closed under the global
context.  The paper-facing Lemma 7.1 inherits only
`Classical_Prop.classic` from the existential safety-witness update.

`Classical_Prop.classic` is a foundational proof principle, not a mathematical
result imported from one of the cited papers.  The cited source theorems are
not declared as Rocq axioms.  The extracted program also depends operationally
on Coq 8.20.1's extraction, OCaml 4.14.2, Zarith 1.14, and audited standard
dependent-type casts; those implementation trust boundaries are documented in
[`review/final-trust-report.md`](review/final-trust-report.md) and are distinct
from mathematical provenance.

## 9. Coverage and Verification Status

The BLS-v1 table covers its numbered results used by the proof in Sections
2–7 and Appendices A–C, including all six former public-bridge gaps: Remark
2.2, Facts 3.2 and 3.6, Lemma 3.10, the paper Attractor/Lemma 7.1, and Lemma
5.6.  The FoSSaCS and Leroux tables expose the complete chain used to prove
BLS-v1 Lemma 4.6.  The Lazić–Schmitz table separates the actual ordinary-MELL
composition from nearby but different complexity reductions.

Current status:

- no source theorem is assumed through a new project axiom;
- `separator_S`, `singleton_separator`, `reduce_mell_correct`, and the public
  decision theorems are kernel checked;
- the final public correctness theorems have no mathematical assumption other
  than the documented `Classical_Prop.classic` dependency where reported;
- source-fidelity evidence and `coqchk` evidence are distinct: kernel checking
  establishes proof-term validity, while the tables and independent reviews
  establish correspondence to the cited statements;
- the historical definitions of all repair labels R01--R11 are now verified
  against the hash-fixed, user-provided design source, and their current Rocq
  realizations are cross-checked separately;
- the exact Leroux-2011 Theorem 3.5 primary passage remains **UNVERIFIED**.
  The locally proved narrow consequence does not establish the source-number
  match.

This document does not claim a line-by-line formalization of every explanatory
paragraph or example in the sources.

## 10. References

1. C. Bizière, J. Leroux, and G. Sutre. “Solving the Reachability Problem for
   Branching Vector Addition Systems via Semilinear Inductive Invariants.”
   arXiv:2607.09558v1, 2026.
2. C. Bizière, J. Leroux, and G. Sutre. “Bridging the Gap Between Plain VASS
   and Branching VASS.” *FoSSaCS 2026*, LNCS 16503, pp. 65–87. DOI:
   [10.1007/978-3-032-22730-0_4](https://doi.org/10.1007/978-3-032-22730-0_4).
3. J. Leroux. “Vector Addition Systems Reachability Problem (A Simpler
   Solution).” *Turing-100*, EPiC Series in Computing 10, 2012, pp. 214–228.
   DOI: [10.29007/bnx2](https://doi.org/10.29007/bnx2).
4. R. Lazić and S. Schmitz. “Non-Elementary Complexities for Branching VASS,
   MELL, and Extensions.” *ACM Transactions on Computational Logic* 16(3),
   Article 20, 2015. DOI:
   [10.1145/2733375](https://doi.org/10.1145/2733375).
5. J. Leroux. “Vector Addition System Reachability Problem: A Short
   Self-Contained Proof.” *POPL 2011*, pp. 307–316.
6. A. Schrijver. *Theory of Linear and Integer Programming*. Wiley, 1999.
