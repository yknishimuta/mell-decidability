# DOC-PROV-R Historical Repair-Ledger Audit

## Scope

This audit fixes the historical meanings of R01--R11 without treating a design
record as proof that the repairs were implemented.  It cross-checks three
separate evidence classes:

1. the user-provided original design for ID ownership;
2. the current Rocq declarations for implementation;
3. executable counterexamples and task audits for source correspondence.

The audited repository baseline is
`f14e38acbc8c3e9f2df2886ae155e2659c00fdcb`.  No mathematical source was
modified by DOC-PROV-R.

## Historical source identity

- Supplied filename: `2026-10-17-mell-formalization-design.md`
- Inspection path outside this repository:
  `/Users/nishimuta/Downloads/mell-codex-design/docs/superpowers/specs/2026-10-17-mell-formalization-design.md`
- Title: *MELL 決定可能性の Coq 形式化設計*
- Declared creation date: 2026-10-17
- Declared status: design
- Size: 35,521 bytes; 414 lines
- SHA-256:
  `1084e041c7106acbaad07c2cffb3e344820f1b4121b2b06ea647176b4f826ff9`
- Repository status: not present in the current `mell-decidability` Git tree;
  the supplied external copy is also not a tracked file from which a Git blob
  or source commit can be recovered.

The header says that the named declarations are implementation contracts, not
compiled code.  The design also says that the combined build, proof scripts,
and machine verification had not yet been performed.  The source is therefore
authoritative for historical R-number identity only.  It is not evidence that
any current Rocq theorem is correct, and it is not an author corrigendum to the
published paper.

## Historical ledger transcription

The following is a faithful English rendering of Section 6.3, lines 271--293.
The locators are intentionally not normalized to later paper-table numbering.

| ID | Historical source locator | Historical repair contract |
|---|---|---|
| R01 | Lemma 4.5 | Use the cone decomposition with a strictly positive component coefficient. |
| R02 | Lemma 4.6 | Intersect the doubled system with `D × H` before projection and restrict the correspondence to control sum 0/1. |
| R03 | Appendix B.1 | Include arity zero, preserve ordered child positions and a separate root-output comparison, and prove the exact `IRunLe` WQO/finite-cover basis. |
| R04 | Fact B.3 / Lemma B.2 | Compare parents only from the same action and comparable children; retain context lifting and the exact additive amalgamation equation. |
| R05 | FoSSaCS Lemma 6 | Use root-configuration comparison plus ordered-decoration embedding only as a one-way implication to the original context order; do not replace that order downstream. |
| R06 | Lemma 5.7 | Treat the leaf-only run explicitly. |
| R07 | Lemma 6.10 | Prove `s_n-s_m` belongs to `Q intersection K^perp` directly; do not claim `s_n` belongs to `Q`. |
| R08 | Lemma 6.11 / Theorem 6.1 | Keep the `extract_F(X,Y)` argument order consistent and subtract `X` from the remaining `Y`. |
| R09 | Lemma 6.3 / 7.5 | Use `1 <= i < j <= n`; reason by target-difference membership rather than applying a run relation to vectors. |
| R10 | Section 7 | Preserve homogeneity, attractor, and full-run coverage, and strictly decrease the lexicographic degree-count rank. |
| R11 | Appendix A | After sign reflection, restrict to the natural-orthant carrier and combine the periodic and Dickson orders there to obtain a nonnegative difference. |

The design further fixes the R11 carrier as
`Q_s = f_s(P) intersection N^d`.  It records counterexamples for R01, R04,
R05, and R07, but those descriptions were checked against current executable
evidence rather than accepted as completed proofs.

## Current Rocq reconciliation

| ID | Current declaration or invariant | Evidence judgment |
|---|---|---|
| R01 | `Mell.Geometry.Cone.periodic_cone_union_strict`; `Mell.Separator.TransformerPeriod.lemma_4_5_periodic_almost_semilinear_relation` | Implemented.  `RepairExamples.v` checks both the old one-dimensional set-equality counterexample and the boundary ray introduced by a non-strict coefficient.  This repairs the proof boundary, not the public Lemma 4.5 conclusion. |
| R02 | `Mell.Separator.DoubledRelation.doubled_restriction_semilinear`, `doubled_projection_iff`, `lemma_4_6_special_leaf_inter_semilinear` | Implemented.  Marker/control restriction and the relation are imposed in `DoubledReachRestricted` before coordinate projection.  The public Lemma 4.6 conclusion remains exact. |
| R03 | `Mell.BVAS.RunOrder.IRunLe`; `Mell.Order.FiniteBasis.irun_le_wqo`; `irun_le_finite_cover` | Implemented.  The explicit leaf is the zero-child label; `Action` itself remains positive-arity.  `IRunsEmbed` preserves ordered child positions, while `IRunLe` adds an independent root-target comparison. |
| R04 | `Mell.BVAS.RunOrder.root_same_action_mono`; `context_lift`; `Mell.BVAS.Amalgamation.run_amalgamation` | Implemented.  `old_fact_b3_missing_same_action` refutes the under-specified standalone Fact B.3.  Lemma B.2's exact conclusion and Lemma 3.10's public premises are retained. |
| R05 | `Mell.BVASS.OrderedBridge.ordered_embed_implies_context_insert`; `Mell.BVASS.StatefulAmalgamation.stateful_context_order_amalgamation` | Implemented.  `BridgeExamples.v` shows why fixed positional decoration cannot replace the occurrence-sensitive context order under child permutation. |
| R06 | `Mell.BVAS.OneSourceReduction.compress_free_run`; `lemma_5_7_one_source_reduction` | Implemented.  The induction's leaf branch constructs the distinguished leaf directly without an initial-list premise. |
| R07 | `Mell.Geometry.FaceStrippingLemma610FiniteBasis.lemma_6_10_maximal_extract_finitary` | Implemented.  The proof uses period membership of differences; the translated-chain regression has an origin outside the period although successive differences lie in it. |
| R08 | `Mell.Geometry.FaceStrippingExtract.extract_remainder_cylindric` | Implemented.  The current BLS-v1 correspondence table calls this Lemma 6.8, while the historical ledger says Lemma 6.11 / Theorem 6.1.  Both locators are retained explicitly. |
| R09 | `Mell.Geometry.FaceStrippingDiagonal.lemma_6_3_stripping_diagonal`; `Mell.Separator.WitnessUpdate.lemma_7_5_new_node_edge_direction` | Implemented.  Current code uses equivalent zero-based indices and forbids later-to-earlier edges; the converse remains possible. |
| R10 | `Mell.Separator.SafetyWitness.SafetyWitness`, `Mell.Separator.SafetyWitness.HomogeneousWitnessNodes`, `Mell.Separator.SafetyWitness.witness_run_coverage`, `Mell.Audit.PaperFidelityBridges.paper_attractor_iff_attractor`, `Mell.Separator.RankDecrease.witness_rank_less_well_founded`, `Mell.Separator.WitnessUpdate.lemma_7_1_safety_witness_rank_descent` | Implemented.  The witness stores SCC-local homogeneity and coverage of complete valid runs; the high-rank-first count tuple is well founded and strictly decreases.  This is a proof/witness-contract repair, not by itself evidence that the published Lemma 7.1 statement was false. |
| R11 | `Mell.Order.PeriodicOrder.periodic_order_wqo_iff_finitely_generated` | Implemented.  The proof restricts to `OrthantPart` before applying the nonnegative-coordinate argument.  Lemma 2.1's statement remains exact. |

## R03/R04 ownership decision

The historical ledger resolves the formerly conflated assignments:

- R03 owns the representation of initialized-run order, including the
  zero-child leaf label, ordered child occurrences, independent root output,
  WQO, and finite cover.
- R04 owns the same-action parent rule, context lifting, and exact
  amalgamation equation.  Consequently the +1/+2 same-output,
  different-action counterexample belongs to R04.

This changes repair-ID attribution only.  It does not alter the mathematical
source-to-Rocq result table or renumber the historical ledger.

## Proposition versus proof repair

The design lists planned corrections and cannot itself justify the label
**REPAIRED** for every numbered paper proposition.  The current evidence
supports these narrower conclusions:

- the standalone old Fact B.3 statement is false and repaired by R04;
- R01, R02, R04 as used by Lemma B.2, and R06--R11 repair proof steps,
  intermediate claims, representations, or witness invariants while retaining
  the numbered conclusions recorded as exact or equivalent;
- R03 establishes the exact formal order needed for Appendix B.1;
- R05 deliberately proves only the sound one-way bridge needed downstream.

## Leroux 2011 boundary

The design distinguishes Leroux 2012 Corollary 6.3 from the separate geometric
dependency attributed to Leroux 2011 Theorem 3.5.  The exact POPL 2011 primary
passage and theorem-number correspondence have not been established.  The
local theorems
`Mell.Geometry.RationalConeAssembly.rational_closed_cone_finitely_generated`
and
`Mell.Geometry.LatticeGordanInterface.rational_closed_cone_is_polyhedral`
therefore remain an alternative derivation of the needed narrow consequence;
the Leroux 2011 source-number match remains **UNVERIFIED**.
