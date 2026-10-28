# arXiv:2607.09558v1 fidelity and additional-assumption audit

Date: 2026-10-27

Audited revision: `2190c6fbfbf523c77224e247884bcae001ddf3bc`

Branch: `work/mell-formalization`

Primary source: Bizière--Leroux--Sutre, *Solving the Reachability
Problem for Branching Vector Addition Systems via Semilinear Inductive
Invariants*, arXiv:2607.09558v1.

## Executive conclusion

The formalization proves the paper's main result, Theorem 3.3, at the same
mathematical strength.  Its public theorem `Mell.Separator.Main.separator_S`
quantifies over every represented IBVAS and every semilinear safety region
containing its reachability set, and returns a semilinear inductive invariant
inside that region.  No finite-generation, decidability, non-emptiness, or
positive-dimension premise is exposed by the Coq theorem.  Coq additionally
covers dimension zero.

No class-D additional premise (a premise absent from the paper and not
derivable from the paper's hypotheses) was found in a theorem used by
`separator_S`.  Explicit premises such as validity of initialized runs,
nonnegativity of a periodic set, a supplied finite semilinear code, and
ordered face lists are either definitions unpacked by the paper (class A) or
representation witnesses obtained from the paper's hypotheses (class B).

The proof is not a transcription of every sentence in the article.  It has
four important kinds of deviation:

1. It repairs known proof errors without weakening the numbered conclusion:
   the Appendix-B same-action issue, strict cone coefficients, the signed
   orthant argument, and the Section-6 differences/extract/indexing issues.
2. It replaces several paper appeals to folklore or external sources by
   kernel-checked developments (Kruskal/Higman closures, rational cone and
   lattice geometry, finite bases, and semilinear closure).
3. It omits examples, remarks, and auxiliary statements that are not needed
   by the final dependency chain.  These are marked `UNUSED`, not silently
   counted as proved.
4. The six limited statement/bridge gaps recorded by the original audit have
   now been closed by kernel-checked public bridges.  They are: Remark 2.2,
   Fact 3.2, Fact 3.6, the paper/internal attractor equivalence and paper-shaped
   Lemma 7.1, literal antisymmetry for Lemma 3.10's WPO, and the existential
   paper-shaped Lemma 5.6.  The historical GAP findings remain documented
   below, together with their exact closure declarations.  None of these
   additions changes `separator_S`, `singleton_separator`, or the decision
   procedure.  The R03/R07--R09/R11 repairs retain their `REPAIRED`
   classification rather than being relabelled merely because a wrapper was
   added.

There are no admitted obligations or new mathematical axioms.  The late
geometric and existence proofs depend only on `Classical_Prop.classic`; many
core run, WSVAS, and amalgamation theorems are closed under the global
context.  Kernel acceptance and `coqchk` establish proof integrity, but are
separate from the source-fidelity judgment recorded here.

## Method and evidence

The v1 HTML and TeX source were inspected directly.  The downloaded HTML had
SHA-256
`eb86ce14f19ca0aafaad1107798d7d8f12c18b2611df05de53c3abd9dc351639`.
Sections 2--7 and Appendices A--C were enumerated from the TeX sources rather
than inferred from earlier audit reports.

For Coq, the audit inspected definitions, theorem bodies, section variables,
record fields, and coercions.  A focused check file imported the relevant
modules, enabled `Set Printing Implicit`, and ran `Check` and
`Print Assumptions` for the main contracts.  It compiled with Coq 8.20.1.
Source locations below are repository-relative and theorem names are fully
qualified on first use.

The status vocabulary is:

- `EXACT`: same mathematical domain, hypotheses, and conclusion;
- `EQUIVALENT`: different representation with checked bidirectional bridges;
- `REPAIRED`: a necessary correction to a faulty proof/statement detail;
- `DERIVED`: follows from named, kernel-checked general results;
- `UNUSED`: not needed in the formal proof and not claimed as formalized;
- `GAP`: literal paper content lacks a checked bridge or proof;
- `UNVERIFIED`: evidence was insufficient.  No item remains `UNVERIFIED`.

## Definition fidelity

| Paper notion | Coq representation and semantic check | Result |
|---|---|---|
| quasi-order/WQO/WPO | The `KruskalAfProp.af` interface represents almost-full/WQO relations; reflexivity and transitivity are proved separately. `irun_le_antisymmetric` proves the missing partial-order law on the raw ordered run trees. | EXACT for Lemma 3.10's WPO package |
| periodic generation/order | `zvec_generated generators`, `FinitelyGeneratedPeriodic`, and `PeriodicLe P x y := exists p, P p /\ y=x+p` implement the monoid span and its translation order. | EXACT |
| linear/semilinear set | `SemiCode` is a finite list of base/generator-list components and `Semilinear X := exists code, forall x, X x <-> denote code x`. Empty and duplicate components are allowed. | EQUIVALENT |
| finite-arity IBVAS | `Mell.BVAS.System.IBVAS d` contains a finite list of initial vectors and a finite list of positive-arity signed actions. Grouping the list by arity yields the paper's finite tuple \((\Delta_0,\ldots,\Delta_r)\); conversely concatenating finite \(\Delta_i\) yields the list. Empty initial/action lists and duplicate rules are permitted. | EQUIVALENT |
| configurations and signed updates | `NVec d` represents \(\mathbb N^d\), `ZVec d` represents actions, and `apply_action` returns a target only when the signed sum remains nonnegative. Every intermediate node of a valid tree is therefore nonnegative. | EXACT |
| initialized versus arbitrary runs | The same `IRun` tree type is interpreted by two predicates: `ValidIRun` requires initial leaves, while `ValidFreeIRun` permits arbitrary leaf configurations and `free_irun_sources` records their occurrence list. The two validity notions are never identified. | EXACT |
| source words | `free_irun_sources`, `SourceShuffle`, and marked-source predicates are list/occurrence based. Equal-valued leaves remain separate occurrences, including when the distinguished leaf value also lies in the side set. | EXACT |
| reachability | `Reach S x := exists run, ValidIRun S run /\ irun_target run = x`. Validity is of the whole execution tree, not merely its root equation. | EXACT |
| initialized-run order | `IRunLe left right := nvec_le (target left) (target right) /\ IRunEmbed left right`. `IRunEmbed` may match below the root and preserves action and ordered child occurrences. Mutual embedding has equal node count, excludes a strict below-root match, and gives raw tree equality. | EXACT |
| subrun occurrence | `IRunOccurrence` is an occurrence-sensitive structural relation, used in directed edges and special-leaf replacement; it is not value membership. | EXACT |
| periodic/asymptotic | `Periodic` is zero plus additive closure on `ZSet`; `PeriodicNSet` is its natural-vector form. `AsymptoticallyDefinable` states rational definability of `Cone`. | EXACT |
| cone and closed linearization | `Cone P` uses nonnegative rational combinations; `ClosedLinearization P` is `(P-P) \cap closure_Q(Cone P)`. Natural-vector bridges retain nonnegativity and never truncate negative integers. | EXACT |
| rational definability | `QDefinable C := exists f : QFormula, qformula_closed d f = true /\ forall x, C x <-> qformula_semantics (qvec_environment x) f`. `QFormula` is the full rational linear first-order syntax, including quantifiers and constants; QE supplies normal forms when required. It is not definitionally a closed homogeneous H-representation. | EQUIVALENT |
| group/vector space/span/dimension | Integer groups and rational spans are predicate-level structures; `SpanDimension` is tied to finite generator rank and proves monotonicity and strict proper-face decrease. | EQUIVALENT |
| rational face | `FaceOf C F` uses supporting homogeneous linear forms and extensional `SameSet`; faces contain zero, and the empty face of other libraries is not admitted as a face here. | EQUIVALENT |
| full periodic set | `FullPeriodic` packages periodicity and a group/cone representation extensionally equivalent to \(Q=(Q-Q)\cap\operatorname{Cone}(Q)\). It does not identify `Q-Q` with all of \(\mathbb Z^d\). | EQUIVALENT |
| Q-cylindric/finitary | `QCylindric Q X` is \(X+Q\subseteq X\); `FinitaryQCylindric` gives a finite base list whose translates are extensionally exactly `X`. Empty bases are allowed. | EXACT |
| WSVAS | `WSVAS d` carries an arbitrary transition type, a reflexive/transitive WQO, signed monotone action, and the exact action diamond. Transitions need not be finite or decidably equal. | EXACT |
| WSVAS run/order | `WSRun` permits zero transitions; `ValidWSRun` checks every signed update. `WSRunOrder` compares both ends of every gap and transition labels. Lemma C.1 additionally records direction comparison, so the empty encoding is sound. | EXACT |
| directed initialized run | `DirectedIRun` pairs a valid initialized run with a finitely generated nonnegative rational cone. `DirectedRunMember` uses the actual run order plus an exact target offset in that cone. | EXACT |
| Safety Witness | `SafetyWitness` stores a semilinear internal attractor inside the safe region, an occurrence-indexed finite node list, SCC-local homogeneity, and coverage of every valid initialized execution tree. `PaperSafetyWitness` uses the paper initial-side attractor, and checked conversions in both directions preserve the node list and hence rank. | EQUIVALENT; exact run-level coverage |
| homogeneous SCC | vertices are `Fin.t (length nodes)` and mutual graph reachability defines SCCs; equal-valued duplicate nodes remain different occurrences. Homogeneity requires equal cones only inside one SCC. | EXACT |
| face stripping | faces are extensional rational cones; `OrderedStrippingFaces` is a duplicate-free reverse-inclusion linear extension beginning with the whole cone. Slices use `ExtractFace period face excluded remaining`, the corrected argument order. | EQUIVALENT / REPAIRED |
| witness rank | `WitnessRankLess` compares counts by cone span dimension, highest differing dimension first. It does not compare total node counts and uses the directed node's original cone. | EXACT |

The paper fixes a positive dimension in its preliminaries.  The Coq definitions
and theorems also accept `d = 0`; this is a conservative generalization, not a
restriction.  No inspected definition excludes empty initial sets, zero
periods, repeated actions/leaves, unary rules, or arbitrary positive arity.

### Non-numbered definition inventory by section

This inventory covers the paper-specific definitions used in Sections 2--7;
ordinary arithmetic/list notation is omitted.

| Section | Paper definitions | Coq definition/equation |
|---|---|---|
| 2 | quasi-order, WQO, WPO, minimal elements | `af`/`afs` plus explicit reflexivity/transitivity; antisymmetry must be a separate proposition. Finite covers are `CountableFiniteBasis`/`FiniteBasis`. |
| 2 | periodic set and period order | `Periodic P := P 0 /\ forall x y, P x -> P y -> P (x+y)`; `PeriodicLe P x y := exists p, P p /\ y=x+p`. |
| 2 | finite periodic generation | `FinitelyGeneratedPeriodic P := exists gs, Forall P gs /\ SameSet P (zvec_generated gs)`. |
| 2 | linear/semilinear | `LinearComponent`/`SemiCode`; `Semilinear X := exists code, forall x, X x <-> denote code x`. |
| 2 | Q-cylindric/finitary and diagonal | `QCylindric Q X := forall x q, X x -> Q q -> X (x+q)`; `FinitaryQCylindric` is an extensional finite union of translates; `QDiagonal Q R` translates both coordinates by one `q`. |
| 2 | group, cone, span, dimension, closure | `IntegerAdditiveGroup`, `Cone`, `QSpan`, `SpanDimension`, and `QClosure` in `Geometry`; all use exact integer/rational vectors. |
| 2 | full, linearization, closed linearization | `Linearization P := Difference P \cap Cone P`; `ClosedLinearization P := Difference P \cap QClosure (Cone P)` after the integer-to-rational embedding; `FullPeriodic` is an extensional group/cone representation. |
| 2 | rational polyhedral cone and face | `RationalPolyhedralCone`, `FaceOf`, `ConeLineality`, and finite supporting-normal lists. `SameSet` is used instead of function equality. |
| 3 | BVAS/IBVAS, action, run, source/target/reach | `Action`, `IBVAS`, the shared tree type `IRun`, predicates `ValidIRun`/`ValidFreeIRun`, `irun_target`, `free_irun_sources`, and `Reach`. Positive arity is a field of every non-leaf action. |
| 3 | inductive invariant | `InitialIncluded S I /\ Closed S I`; the equivalent local packaged form is `IBVASInductiveInvariant`. |
| 3 | shuffle and attractor | occurrence-list predicates remain available for the commutative specialization. `Language`, ordered `WordShuffle`, `LanguageStar`/`LanguagePlus`, and `fact_3_6_reach_shuffle_flatten` expose the arbitrary-language form. `PaperAttractor` and `paper_attractor_iff_attractor` prove both attractor formulations equivalent for every predicate. |
| 3 | initialized-run order/subrun | `IRunLe := target coordinate order /\ IRunEmbed`; `IRunOccurrence rho sigma := exists C, sigma=context_plug C rho`. |
| 3 | `P_rho` | `IRunPeriod S rho x` requires a valid extension `sigma`, `IRunLe rho sigma`, and the exact natural-vector target equation. |
| 3 | directed run, `P_w`, `Q_w`, edge | `DirectedIRun`, `DirectedOffset`, `DirectedPeriod`, `DirectedClosedPeriod`, `DirectedRunMember`, and `DirectedIRunEdge` in `DirectedRuns.v`. |
| 3/7 | graph, SCC, homogeneous witness, rank | occurrence vertices `Fin.t (length nodes)`, `WitnessEdge`, reflexive-transitive reachability, `SameSCC`, `HomogeneousWitnessNodes`, `SafetyWitness`, `witness_rank_tuple`, and high-dimension-first `WitnessRankLess`. |
| 4 | definable cone/asymptotically definable | `QDefinable C`; `AsymptoticallyDefinable P := QDefinable (Cone P)`. |
| 4 | almost linear/semilinear | finite lists of translated asymptotically-definable periodic components in the `AlmostSemilinear` modules. |
| 4 | special-leaf relation/transformer | `SpecialLeafReach S x y`; `SpecialTransformer S c x y` is the exact translated special-leaf relation at base `c`. |
| 4 | center | `Center P v := forall g, Difference P g -> exists r, forall n, P (g+(r+n)v)`. |
| 5 | WSVAS and transition diamond | record `WSVAS` displayed above; action is signed and the last field is exact equality, not an inequality. |
| 5 | WSVAS run, direction, run order | `WSRun`, `ValidWSRun`, `(ws_source,ws_target)`, `WSRunGapDecomposition`, and `WSRunOrder`; empty transition lists are valid. |
| 5 | Higman encoding | `encode_ws_run`, `WSHigmanEmbed`, `WSDirectionLe`; Lemma C.1 is their exact conjunction. |
| 5 | witness alphabet/concrete WSVAS | sum type `WitnessAlphabet` distinguishes initialized-run evidence from tagged semilinear-component evidence; fixed-length side-witness vectors form transitions. |
| 5 | main-branch step and reach | `BVASSideStep`, `WSVASStep`, `WSVASStepStar`, `ReachWSVASFromSet`, `ReachFromShuffle`, and `ReachFromNonemptyShuffle`. |
| 6 | extract | `ExtractFace Q F X Y s := forall q, FacePeriod Q F q -> Y (s+q) /\ ~X (s+q)`. This is `Y\X`, not the reversed difference. |
| 6 | ordered faces/stripping recursion | `OrderedStrippingFaces`, `StrippingRemainder`, `StrippingSlice`, and `StageCandidateFace`; indices are zero-based and the head is `Cone Q`. |
| 6 | backward-period cover/boundary edge | `BackwardPeriodCover Q X Y := forall y, Y y -> exists q, Q q /\ X (y+q)` and `NoBoundaryEdge X Y R`. |
| 7 | bottom SCC region/linear slice/replacement | `BottomSCCRegion`, `BottomSCCLinearSlice`, `FaceReplacementBlock`, tagged replacement nodes, and retained-old-node predicates. These are proof data inside rank descent, not extra theorem parameters. |

Appendix A introduces no new semantic object. Appendix B uses the Section-3
run order and one-hole contexts. Appendix C's alphabet, word encoding, Higman
embedding, gap decomposition, and exact diamond are the Section-5 definitions
listed above.

## Complete public contracts for the central chain

The following are the source-facing forms of the checked Gallina types.  The
focused log also printed every implicit universe-free argument and module
qualification.

```coq
Mell.Order.FiniteBasis.irun_le_wqo :
  forall d (S : IBVAS d),
    afs (ValidIRun S) IRunLe

Mell.BVAS.Amalgamation.run_amalgamation :
  forall d (S : IBVAS d) root left right,
    ValidIRun S root -> ValidIRun S left -> ValidIRun S right ->
    IRunLe root left -> IRunLe root right ->
    exists merged,
      ValidIRun S merged /\ IRunLe left merged /\ IRunLe right merged /\
      nvec_add (irun_target root) (irun_target merged) =
      nvec_add (irun_target left) (irun_target right)

Mell.Separator.DirectedRuns.lemma_3_12_directed_closed_period_finitely_generated :
  forall d (S : IBVAS d) (w : DirectedIRun S),
    FinitelyGeneratedPeriodic (DirectedClosedPeriod w)

Mell.Separator.DirectedRuns.lemma_3_13_directed_closed_period_inclusion :
  forall d (S : IBVAS d) u v,
    DirectedIRunEdge u v -> DirectedConeIncluded u v ->
    forall z, DirectedClosedPeriod u z -> DirectedClosedPeriod v z

Mell.Separator.DoubledRelation.lemma_4_6_special_leaf_inter_semilinear :
  forall d (S : IBVAS d) H,
    SemilinearNRelation H ->
    AlmostSemilinearNRelation
      (fun x y => H x y /\ SpecialLeafReach S x y)

Mell.Separator.TransformerPeriod.lemma_4_10_special_transformer_asymptotically_definable :
  forall d (S : IBVAS d) base,
    AsymptoticallyDefinableNRelation (SpecialTransformer S base)

Mell.Separator.TransformerPeriod.lemma_4_11_irun_period_asymptotically_definable :
  forall d (S : IBVAS d) rho,
    ValidIRun S rho -> AsymptoticallyDefinableNSet (IRunPeriod S rho)
```

```coq
Mell.WSVAS.Amalgamation.lemma_5_2_wsvas_runs_wqo_amalgamation :
  forall d (V : WSVAS d),
    afs (ValidWSRun V) (WSRunOrder V) /\
    forall root alpha beta,
      ValidWSRun root -> ValidWSRun alpha -> ValidWSRun beta ->
      WSRunOrder root alpha -> WSRunOrder root beta ->
      exists sigma,
        ValidWSRun sigma /\ WSRunOrder alpha sigma /\
        WSRunOrder beta sigma /\
        nvec_add (ws_source root) (ws_source sigma) =
          nvec_add (ws_source alpha) (ws_source beta) /\
        nvec_add (ws_target root) (ws_target sigma) =
          nvec_add (ws_target alpha) (ws_target beta)

Mell.WSVAS.SafeLinearization.lemma_5_4_wsvas_safe_linearization :
  forall d (V : WSVAS d) base period target,
    PeriodicNSet period -> AsymptoticallyDefinableNSet period ->
    Semilinear target ->
    ReachWSVASFromSet V (NSetTranslate base period) target ->
    exists p, period p /\
      ReachWSVASFromSet V
        (NSetTranslate (nvec_add base p) (ClosedLinearizationN period)) target

Mell.WSVAS.BVASSimulation.lemma_5_5_bvas_wsvas_reach_iff :
  forall d (S : IBVAS d) code X target,
    ClosedUnderFreeRuns S (SimulationInvariant S code) ->
    (ReachFromShuffle S X (SimulationInvariant S code) target <->
     exists source, X source /\
       WSVASStepStar (concrete_wsvas S code) source target)

Mell.WSVAS.WitnessAlphabet.lemma_5_6_bvas_wsvas_step_iff :
  forall d (S : IBVAS d) code source target,
    BVASSideStep S code source target <->
    WSVASStep (concrete_wsvas S code) source target

Mell.BVAS.OneSourceReduction.lemma_5_7_one_source_reduction :
  forall d (S : IBVAS d) I P X,
    ClosedUnderFreeRuns S I -> PeriodicNSet P -> NSetStable X P ->
    (forall y, ReachFromShuffle S X I y -> NSetMinkowskiN I P y) ->
    forall y,
      ReachFromShuffle S X I y <-> ReachFromNonemptyShuffle S X I y
```

```coq
Mell.Separator.SafeLinearization.lemma_5_1_bvas_safe_linearization :
  forall d (S : IBVAS d) A T P b,
    IBVASInductiveInvariant S (fun x => A x \/ Reach S x) ->
    Semilinear A -> Semilinear T ->
    PeriodicNSet P -> AsymptoticallyDefinableNSet P ->
    (forall y,
      ReachFromShuffle S (NSetTranslate b P)
        (fun x => A x \/ Reach S x) y -> T y) ->
    (forall y, T y ->
      NSetMinkowskiN (fun x => A x \/ Reach S x)
        (ClosedLinearizationN P) y) ->
    exists p, P p /\
      forall y,
        ReachFromNonemptyShuffle S
          (NSetTranslate (nvec_add b p) (ClosedLinearizationN P))
          (fun x => A x \/ Reach S x) y -> T y
```

```coq
Mell.Geometry.FaceStrippingTheorem.face_stripping_theorem :
  forall d Q X Y,
    Periodic Q -> FinitelyGeneratedPeriodic Q -> FullPeriodic Q ->
    FinitaryQCylindric Q X -> FinitaryQCylindric Q Y ->
    (forall z, X z -> Y z) ->
    exists faces,
      OrderedStrippingFaces Q faces /\
      nth_error faces 0 = Some (Cone Q) /\
      SameSet (StrippingRemainder Q X Y faces 0) Y /\
      SameSet (StrippingRemainder Q X Y faces (length faces)) X /\
      (forall i, i <= length faces ->
        FinitaryQCylindric Q (StrippingRemainder Q X Y faces i) /\
        forall z, X z -> StrippingRemainder Q X Y faces i z) /\
      (forall i F, i < length faces -> nth_error faces i = Some F ->
        FinitaryQCylindric (FacePeriod Q F)
          (StrippingSlice Q X Y faces i) /\
        forall z, StrippingSlice Q X Y faces i z -> Y z /\ ~ X z) /\
      (forall i j, i < j -> j < length faces -> forall z,
        ~ (StrippingSlice Q X Y faces i z /\
           StrippingSlice Q X Y faces j z)) /\
      (forall z, Y z /\ ~ X z <->
        exists i, i < length faces /\ StrippingSlice Q X Y faces i z) /\
      (BackwardPeriodCover Q X Y ->
        forall z, ~ StrippingSlice Q X Y faces 0 z)

Mell.Geometry.FaceStrippingDiagonal.lemma_6_3_stripping_diagonal :
  forall d Q X Y faces R,
    Periodic Q -> FinitelyGeneratedPeriodic Q -> FullPeriodic Q ->
    FinitaryQCylindric Q X -> FinitaryQCylindric Q Y ->
    (forall z, X z -> Y z) -> OrderedStrippingFaces Q faces ->
    QDiagonal Q R -> NoBoundaryEdge X Y R ->
    forall i j x y,
      i < j -> j < length faces ->
      StrippingSlice Q X Y faces j x ->
      StrippingSlice Q X Y faces i y -> ~ R x y
```

```coq
Mell.Separator.WitnessUpdate.lemma_7_1_safety_witness_rank_descent :
  forall d (S : IBVAS d) Phi (w : SafetyWitness S Phi),
    witness_nodes w <> [] ->
    exists next : SafetyWitness S Phi,
      WitnessRankLess (witness_nodes next) (witness_nodes w)

Mell.Separator.Main.separator_S :
  forall d (S : IBVAS d) Phi,
    Semilinear Phi ->
    (forall x, Reach S x -> Phi x) ->
    exists J,
      Semilinear J /\ InitialIncluded S J /\ Closed S J /\
      (forall x, J x -> Phi x)
```

### Supplementary exact signatures used for numbered derived items

These signatures make explicit the proof bundles behind table entries marked
`DERIVED`; they are not merely module-level references.

```coq
(* Fact 3.2: one occurrence, iterated/combined structurally for many leaves. *)
Mell.BVAS.RunOrder.apply_action_frame_shift :
  forall d action before after left right target delta,
    right = nvec_add left delta ->
    apply_action action (before ++ left :: after) = Some target ->
    apply_action action (before ++ right :: after) =
      Some (nvec_add target delta)

Mell.BVAS.OneSourceReduction.marked_free_shift :
  forall d (S : IBVAS d) X I P run offset,
    NSetStable X P ->
    MarkedFreeIRun S X I run -> P offset ->
    exists shifted,
      MarkedFreeIRun S X I shifted /\
      irun_target shifted = nvec_add (irun_target run) offset

(* Fact 3.6: one marked occurrence. *)
Mell.Separator.WitnessUpdate.marked_free_substitute :
  forall d (S : IBVAS d) X I R outer,
    MarkedFreeIRun S R I outer ->
    (forall value, R value ->
      exists inner,
        ValidFreeIRun S inner /\ irun_target inner = value /\
        SourceMultiShuffle X I (free_irun_sources inner)) ->
    exists result,
      ValidFreeIRun S result /\
      irun_target result = irun_target outer /\
      SourceMultiShuffle X I (free_irun_sources result)

(* Fact 3.6: simultaneous side expansion actually used. *)
Mell.Separator.WitnessUpdate.multi_substitute_runs :
  forall d (S : IBVAS d) X I R,
    (forall value, R value ->
      exists inner,
        ValidFreeIRun S inner /\ irun_target inner = value /\
        SourceMultiShuffle X I (free_irun_sources inner)) ->
    (forall run,
      ValidFreeIRun S run ->
      List.Forall (fun value => R value \/ I value)
        (free_irun_sources run) -> ExpandedRun S X I R run) /\
    (forall runs,
      ValidFreeIRuns S runs ->
      List.Forall (fun value => R value \/ I value)
        (free_iruns_sources runs) -> ExpandedRuns S X I R runs)

Mell.Separator.WitnessUpdate.lemma_3_7_attractor_extension :
  forall d (S : IBVAS d) A I X,
    Attractor S A -> IBVASInductiveInvariant S I ->
    (forall value, A value -> I value) ->
    Attractor S
      (fun value => A value \/ ReachFromNonemptyShuffle S X I value)

Mell.Separator.Attractor.attractor_initial_form :
  forall d (S : IBVAS d) A,
    Attractor S A ->
    forall y,
      ReachFromNonemptyShuffle S A (InitialNSet S) y -> A y
```

```coq
(* Lemma 4.3. *)
Mell.VAS.PeriodicIntersection.periodic_cone_intersection :
  forall d P Q point,
    Periodic P -> Periodic Q ->
    (Cone (fun z => P z /\ Q z) point <->
     Cone P point /\ Cone Q point)

Mell.Separator.TransformerPeriod.periodic_cone_minkowski :
  forall d P Q,
    Periodic P -> Periodic Q -> forall point,
    (Cone (ZSetMinkowski P Q) point <->
     exists p q, Cone P p /\ Cone Q q /\
       qvec_eq point (qvec_add p q))

Mell.VAS.AlmostSemilinearProjection.target_projection_cone :
  forall d relation point,
    PeriodicNRelation relation ->
    (Cone (NSetAsZ (NRelationTargetProjection relation)) point <->
     exists source,
       RationalRelationCone (NRelationAsZ relation) source point)

(* Lemma 4.4. *)
Mell.Geometry.ClosedLinearizationL2.closed_linearization_finitely_generated :
  forall d P,
    Periodic P -> NonnegativeSet P -> AsymptoticallyDefinable P ->
    FinitelyGeneratedPeriodic (ClosedLinearization P)

(* Lemma 4.5. *)
Mell.Separator.TransformerPeriod.lemma_4_5_periodic_almost_semilinear_relation :
  forall d (R : NRelation d),
    PeriodicNRelation R -> AlmostSemilinearNRelation R ->
    AsymptoticallyDefinableNRelation R

(* Lemma 4.7. *)
Mell.Geometry.CenterPushIn.closed_linearization_push_in :
  forall d P,
    Periodic P -> NonnegativeSet P ->
    exists p, P p /\
      forall g x,
        Difference P g -> ClosedLinearization P (zvec_sub x p) ->
        exists r, forall n,
          P (zvec_add g (zvec_nsmul (r+n) x))

(* Lemmas 4.8 and 4.9. *)
Mell.Geometry.CenterCharacterization.center_characterization :
  forall d P v,
    Periodic P ->
    (Center P v <->
     Difference P v /\ PositiveSpanningCombination P v)

Mell.Geometry.CenterAbsorption.center_absorbs_closed_linearization :
  forall d P,
    Periodic P ->
    SameSet
      (fun z => exists v q,
        Center P v /\ ClosedLinearization P q /\ z = zvec_add v q)
      (Center P)
```

```coq
(* Appendix C. *)
Mell.WSVAS.RunOrder.lemma_c_1_wsrun_order_iff_higman :
  forall d (V : WSVAS d) rho sigma,
    WSRunOrder V rho sigma <->
    WSDirectionLe V rho sigma /\ WSHigmanEmbed V rho sigma

Mell.WSVAS.RunOrder.corollary_c_2_wsrun_wqo :
  forall d (V : WSVAS d),
    afs (ValidWSRun V) (WSRunOrder V)

Mell.WSVAS.Amalgamation.ws_run_order_stitch :
  forall d (V : WSVAS d) lp lt ls rp rt rs,
    WSRunOrder V lp rp -> ws_transition_le V lt rt ->
    WSRunOrder V ls rs ->
    WSRunOrder V (ws_run_stitch lp lt ls) (ws_run_stitch rp rt rs)

Mell.WSVAS.Amalgamation.lemma_c_4_wsrun_exact_amalgamation :
  forall d (V : WSVAS d) root alpha beta,
    ValidWSRun root -> ValidWSRun alpha -> ValidWSRun beta ->
    WSRunOrder V root alpha -> WSRunOrder V root beta ->
    exists sigma,
      ValidWSRun sigma /\ WSRunOrder V alpha sigma /\
      WSRunOrder V beta sigma /\
      nvec_add (ws_source root) (ws_source sigma) =
        nvec_add (ws_source alpha) (ws_source beta) /\
      nvec_add (ws_target root) (ws_target sigma) =
        nvec_add (ws_target alpha) (ws_target beta)

Mell.WSVAS.Amalgamation.corollary_5_3_wsvas_run_scaling :
  forall d (V : WSVAS d) root run r,
    ValidWSRun root -> ValidWSRun run -> WSRunOrder V root run ->
    1 <= r ->
    exists scaled,
      ValidWSRun scaled /\ WSRunOrder V run scaled /\
      nvec_add (nvec_scale (r-1) (ws_source root)) (ws_source scaled) =
        nvec_scale r (ws_source run) /\
      nvec_add (nvec_scale (r-1) (ws_target root)) (ws_target scaled) =
        nvec_scale r (ws_target run)

(* Lemma 5.5, general WSVAS run/step-star equality. *)
Mell.WSVAS.Runs.valid_ws_run_step_star :
  forall d (V : WSVAS d) run,
    ValidWSRun run -> WSVASStepStar V (ws_source run) (ws_target run)

Mell.Separator.SafeLinearization.ws_step_star_has_run :
  forall d (V : WSVAS d) source target,
    WSVASStepStar V source target ->
    exists run,
      ValidWSRun run /\ ws_source run = source /\ ws_target run = target

Mell.Separator.SafeLinearization.reach_wsvas_from_set_iff_star :
  forall d (V : WSVAS d) sources targets,
    ReachWSVASFromSet V sources targets <->
    forall target,
      (exists source, sources source /\ WSVASStepStar V source target) ->
      targets target
```

```coq
(* Lemmas 6.5--6.11. *)
Mell.Geometry.FaceZeroPatternWitness.face_zero_pattern_witness :
  forall d Q F normals,
    Periodic Q -> FaceOf (Cone Q) F ->
    List.Forall
      (fun e => SupportingNormal (Cone Q) (zvec_to_qvec e)) normals ->
    exists q,
      FacePeriod Q F q /\
      forall e, List.In e normals ->
        (IntegerNormalOrthogonalToFace F e <->
         qinner (zvec_to_qvec e) (zvec_to_qvec q) == 0)

Mell.Geometry.FaceStrippingBases.integer_affine_inequalities_finitary :
  forall d constraints,
    exists bases : list (ZVec d),
      List.Forall (AffineSolutions constraints) bases /\
      SameSet (AffineSolutions constraints)
        (fun z => exists b h,
          List.In b bases /\ HomogeneousSolutions constraints h /\
          z = zvec_add b h)

Mell.Geometry.Corollary67Finitary.corollary_6_7_finitary :
  forall d Q normals tight threshold,
    Periodic Q -> FinitelyGeneratedPeriodic Q -> FullPeriodic Q ->
    (forall x, Cone Q x <->
      forall e, List.In e normals -> 0 <= qinner (zvec_to_qvec e) x) ->
    (forall e, List.In e tight -> List.In e normals) ->
    FinitaryQCylindric
      (FacePeriod Q (ThresholdFace (Cone Q) tight))
      (RationalThresholdSlice Q normals tight threshold)

Mell.Geometry.FaceStrippingExtract.extract_remainder_cylindric :
  forall d Q X Y F,
    Periodic Q -> FaceOf (Cone Q) F ->
    QCylindric Q X -> QCylindric Q Y ->
    (forall z, X z -> Y z) ->
    QCylindric Q (fun z => Y z /\ ~ ExtractFace Q F X Y z)

Mell.Geometry.FaceStrippingMinimalFace.lemma_6_9_minimal_extract :
  forall d Q X Y,
    Periodic Q -> FinitelyGeneratedPeriodic Q -> FullPeriodic Q ->
    QCylindric Q X -> QCylindric Q Y ->
    (forall z, X z -> Y z) ->
    SameSet (ExtractFace Q (ConeLineality (Cone Q)) X Y)
      (fun z => Y z /\ ~ X z)

Mell.Geometry.FaceStrippingLemma610FiniteBasis.lemma_6_10_maximal_extract_finitary :
  forall d Q X Y F,
    Periodic Q -> FinitelyGeneratedPeriodic Q -> FullPeriodic Q ->
    FinitaryQCylindric Q X -> FinitaryQCylindric Q Y ->
    (forall z, X z -> Y z) ->
    MaximalNonemptyExtractFace Q X Y F ->
    FinitaryQCylindric (FacePeriod Q F) (ExtractFace Q F X Y)

Mell.Geometry.FaceStrippingLemma611.lemma_6_11_stripping_invariants :
  forall d Q X Y faces,
    Periodic Q -> QCylindric Q X -> QCylindric Q Y ->
    (forall z, X z -> Y z) -> OrderedStrippingFaces Q faces ->
    (forall i, i <= length faces ->
      QCylindric Q (StrippingRemainder Q X Y faces i)) /\
    (forall i, i <= length faces -> forall F,
      StageCandidateFace Q X Y faces i F ->
      exists j G,
        i <= j /\ j < length faces /\ nth_error faces j = Some G /\
        SameSet F G)

Mell.Geometry.FaceStrippingLemma611.stripping_current_face_eliminated :
  forall d Q X Y faces,
    Periodic Q ->
    (forall F, List.In F faces -> FaceOf (Cone Q) F) ->
    forall i F,
      i < length faces -> nth_error faces i = Some F ->
      ~ StageCandidateFace Q X Y faces (S i) F
```

```coq
(* Lemmas 7.2--7.5. *)
Mell.Separator.WitnessUpdate.lemma_7_2_safety_witness_successors :
  forall d (S : IBVAS d) Phi (w : SafetyWitness S Phi) u alpha y,
    List.In u (witness_nodes w) -> DirectedRunMember u alpha ->
    SpecialLeafReach S (irun_target alpha) y ->
    witness_attractor w y \/
    exists v,
      WitnessSuccessor (witness_nodes w) u v /\
      exists beta,
        DirectedRunMember v beta /\ irun_target beta = y /\
        IRunOccurrence alpha beta

Mell.Separator.WitnessUpdate.lemma_7_3_attractor_contact_propagation :
  forall d (S : IBVAS d) A Q u v,
    Attractor S A -> PeriodicNSet Q -> NSetStable A Q ->
    DirectedIRunEdge u v ->
    (forall q, NClosedDirectedPeriod u q <-> Q q) ->
    (forall q, NClosedDirectedPeriod v q <-> Q q) ->
    (exists x, A x /\ DirectedRootTranslate u Q x) ->
    exists y, A y /\ DirectedRootTranslate v Q y

Mell.Separator.WitnessUpdate.lemma_7_4_directed_irun_rebase :
  forall d (S : IBVAS d) w rho
      (member : DirectedRunMember w rho),
    (forall sigma,
      DirectedRunMember (rebase_directed_irun w rho member) sigma ->
      DirectedRunMember w sigma) /\
    (forall q,
      DirectedPeriod (rebase_directed_irun w rho member) q ->
      DirectedClosedPeriod w q)

Mell.Separator.WitnessUpdate.lemma_7_5_new_node_edge_direction :
  forall d (S : IBVAS d) Q X Y faces i j u v,
    (forall rho, DirectedRunMember u rho ->
      StrippingSlice Q X Y faces i (nvec_to_zvec (irun_target rho))) ->
    (forall rho, DirectedRunMember v rho ->
      StrippingSlice Q X Y faces j (nvec_to_zvec (irun_target rho))) ->
    (forall a b x y,
      a < b -> b < length faces ->
      StrippingSlice Q X Y faces b x ->
      StrippingSlice Q X Y faces a y ->
      ~ SpecialLeafRelationZ S x y) ->
    i < length faces -> j < length faces ->
    DirectedIRunEdge u v -> i <= j

Mell.Separator.WitnessUpdate.replacement_edge_stays_new_and_nondecreasing :
  forall d (S : IBVAS d) Phi (w : SafetyWitness S Phi)
      root representative_vertex representative offset faces
      (blocks : list
        (FaceReplacementBlock (witness_nodes w) root representative
          (NSetAsZ
            (BottomSCCLinearSlice (witness_nodes w) root representative
              (witness_attractor w) offset))
          (NSetAsZ
            (BottomSCCRegion (witness_nodes w) root representative))
          faces))
      retained source_stage source target,
    BottomSCCRoot (WitnessEdge (witness_nodes w)) root ->
    BottomSCC (WitnessEdge (witness_nodes w)) root representative_vertex ->
    witness_vertex_node (witness_nodes w) representative_vertex
      representative ->
    DirectedOffset representative offset ->
    BottomSCCStrippingPackage (witness_nodes w) root representative
      (witness_attractor w) offset faces ->
    (forall node,
      List.In node retained <->
      RetainedOldNode (witness_nodes w) root node) ->
    List.In (source_stage, source) (tagged_replacement_nodes blocks) ->
    List.In target (retained ++ replacement_nodes blocks) ->
    DirectedIRunEdge source target ->
    exists target_stage,
      List.In (target_stage, target) (tagged_replacement_nodes blocks) /\
      source_stage <= target_stage
```

## Numbered source-to-Coq correspondence

### Section 2 and Appendix A

| Paper item and precise content | Coq declaration / dependency | Status and premise comparison |
|---|---|---|
| Lemma 2.1: periodic \(P\subseteq\mathbb Z^d\) is finitely generated iff \(\le_P\) is WQO on `P`. | `Mell.Order.PeriodicOrder.periodic_order_wqo_iff_finitely_generated : forall d P, Periodic P -> (afs P (PeriodicLe P) <-> FinitelyGeneratedPeriodic P)` | EXACT. Appendix A is replaced by a signed, orthant-correct proof. R11 repairs the paper proof's failure to restrict to the actual orthant part. |
| Remark 2.2: for finitely generated periodic `P`, `P` is full iff `clin(P)=P`. | `Mell.Geometry.ClosedLinearizationFinite.remark_2_2_full_iff_closed_linearization_fixed`. Its proof first establishes that every finitely generated rational cone is topologically closed. | EXACT; the finite-generation hypothesis is explicit and retained. |
| Example 2.3 | `paper_example_2_3_not_closed_linearization_fixed` proves that `P={0} union N_{>0}^2` is full while the positive horizontal axis point belongs to `clin(P)` but not `P`. | EXACT regression; it prevents deleting finite generation from Remark 2.2. |
| Appendix A proof details | `PeriodicOrder.v`, especially orthant decomposition and order-equivalence lemmas. | REPAIRED (R11), conclusion EXACT. |

### Section 3 and Appendix B

| Paper item | Coq declaration / exact content | Status |
|---|---|---|
| Example 3.1 | Motivation for a separator. | UNUSED. |
| Fact 3.2: independently increasing arbitrary run leaves increases the root by their summed increments. | `Mell.BVAS.RunLeafOperations.fact_3_2_all_leaf_increments`. `LeafIncrementsRun` is occurrence-indexed and preserves the ordered source list. | EXACT; increments may differ and the root equation is exact. |
| Theorem 3.3 | `Mell.Separator.Main.separator_S` (complete type above). | EXACT. |
| Remark 3.4 | Discussion of effective search, not a mathematical premise of Theorem 3.3. | UNUSED in this theorem; realized later by the decision layer. |
| Example 3.5 | Explanatory attractor example. | UNUSED. |
| Fact 3.6: for arbitrary languages `K,L`, `Reach(K shuffle Reach(L)^+) ⊆ Reach(K shuffle L^+)`. | `Mell.BVAS.LanguageFlattening.fact_3_6_reach_shuffle_flatten`; `WordShuffle` is ordered interleaving and finite substitution is by leaf occurrence. | EXACT. No commutativity, semilinearity, finiteness, or decidable membership premise is present. |
| Lemma 3.7: if A is an attractor inside invariant I, then `A ∪ Reach(X+ shuffle I*)` is an attractor. | `Mell.Separator.WitnessUpdate.lemma_3_7_attractor_extension` with `Attractor`, `IBVASInductiveInvariant`, and `A⊆I`. | EXACT. The explicit inclusion is the paper phrase "I containing A" (A). |
| Examples 3.8, 3.9 | Directed-run examples. | UNUSED. |
| Lemma 3.10: initialized runs form a WPO and satisfy exact amalgamation. | `Mell.BVAS.RunOrderAntisymmetry.lemma_3_10_irun_wpo_amalgamation` packages reflexivity, transitivity, `irun_le_antisymmetric`, WQO, and `run_amalgamation`. | EXACT for the paper theorem; Appendix-B proof remains REPAIRED by R03 because matched roots must have the same action. |
| Remark 3.11 | Consequences/intuition for directed runs. | DERIVED where used. |
| Lemma 3.12: every \(Q_w\) is finitely generated. | `lemma_3_12_directed_closed_period_finitely_generated`. | EXACT. |
| Lemma 3.13: `u→v` and `C_u⊆C_v` imply `Q_u⊆Q_v`. | `lemma_3_13_directed_closed_period_inclusion`. | EXACT. `DirectedConeIncluded` is definitionally the stated inclusion (A). |
| Appendix B Lemma B.1: `(IRuns(B), trianglelefteq)` is a WPO. | `irun_le_refl`, `irun_le_trans`, `irun_le_wqo`, and `irun_le_antisymmetric`; decorated-tree/Kruskal plus node-count proof. | EXACT. |
| Appendix B Lemma B.2: exact initialized-run amalgamation. | `Mell.BVAS.Amalgamation.run_amalgamation`. | EXACT after the B.3 same-action repair. |
| Appendix B Fact B.3: root update monotonicity. | `root_same_action_mono`. | REPAIRED: the paper statement without equal matched actions is false; `Audit/RepairExamples.v` gives a counterexample. The corrected fact is exactly what Lemma 3.10 requires. |
| Appendix B Fact B.4: global context lifting. | `context_lift` and validity-preserving context lemmas. | EXACT after B.3 repair. |

### Section 4

| Paper item | Coq declaration / dependency | Status |
|---|---|---|
| Remark 4.1 and Example 4.2 | Definable-cone warning/example. | UNUSED as statements; the strict-boundary counterexample is regression-tested. |
| Lemma 4.3: cone commutes with periodic intersection, Minkowski sum, and projection. | `periodic_cone_intersection`; cone-sum lemmas used by `lemma_4_5_periodic_almost_semilinear_relation`; `source_projection_cone`/`target_projection_cone` and relation projection bridges. | DERIVED. Positive common-denominator lemmas prevent unsupported rational scaling. |
| Lemma 4.4: `clin(P)` is finitely generated for asymptotically definable periodic `P⊆N^d`. | `Mell.Geometry.ClosedLinearizationL2.closed_linearization_finitely_generated`, with `Periodic`, `NonnegativeSet`, and `AsymptoticallyDefinable`. | EXACT. `NonnegativeSet` merely spells out `P⊆N^d` (A). |
| Lemma 4.5: every almost-semilinear periodic set is asymptotically definable. | `lemma_4_5_periodic_almost_semilinear_relation` and set specialization. | REPAIRED/EXACT. Strict positive coefficients are essential at component boundaries; the old relaxed cone equality has a checked counterexample. |
| Lemma 4.6: special-leaf reach relation intersect semilinear relation is almost semilinear. | `lemma_4_6_special_leaf_inter_semilinear`. | EXACT. The doubling construction, marker invariant, restriction-before-projection, and projection closure are all proved. |
| Lemma 4.7: push-in. | `Mell.Geometry.CenterPushIn.closed_linearization_push_in` (complete implicit type in focused log). | EXACT. Its explicit nonnegativity premise is the paper's `P⊆N^d` (A). |
| Lemma 4.8: center characterization. | `Mell.Geometry.CenterCharacterization.center_characterization`. | EXACT. |
| Lemma 4.9: `Cent(P)+clin(P)=Cent(P)`. | `Mell.Geometry.CenterAbsorption.center_absorbs_closed_linearization`. | EXACT. |
| Lemma 4.10: transformer is asymptotically definable periodic. | `lemma_4_10_special_transformer_asymptotically_definable`; periodicity is proved separately for `SpecialTransformer`. | EXACT. |
| Lemma 4.11: \(P_\rho\) is asymptotically definable. | `lemma_4_11_irun_period_asymptotically_definable`. | EXACT. The structural equality, empty child sum, cone equality, and projection step are kernel-checked. `ValidIRun` is membership in the paper's `IRuns(B)` (A). |

### Section 5 and Appendix C

| Paper item | Coq declaration / exact content | Status |
|---|---|---|
| Lemma 5.1: BVAS safe linearization. | `Mell.Separator.SafeLinearization.lemma_5_1_bvas_safe_linearization` (complete type above). | EXACT. The invariant premise is precisely the paper hypothesis that `I=A∪Reach(B)` is an inductive invariant. |
| Lemma 5.2: WSVAS run WQO and exact source/target amalgamation. | `lemma_5_2_wsvas_runs_wqo_amalgamation`. | EXACT. |
| Corollary 5.3: positive integer extrapolation of run directions. | `corollary_5_3_wsvas_run_scaling`, using the subtraction-free equalities `(r-1)root + scaled = r run` at both endpoints. | EQUIVALENT. |
| Lemma 5.4: WSVAS safe linearization. | `lemma_5_4_wsvas_safe_linearization`. | EXACT. The semilinear complement/ray proof and witness-free almost-full argument introduce no choice oracle. |
| Lemma 5.5, first equality: WSVAS runs coincide with reflexive-transitive step reachability. | `valid_ws_run_step_star`, `Mell.Separator.SafeLinearization.ws_step_star_has_run`, and `reach_wsvas_from_set_iff_star`. | DERIVED, both directions checked, including zero-step runs. |
| Lemma 5.5, BVAS equality under `Reach(I+) ⊆ I`. | `lemma_5_5_bvas_wsvas_reach_iff`. | EQUIVALENT. `ClosedUnderFreeRuns` is the checked run-level form of that closure; the paper-shaped equivalence is proved through marked leaves. |
| Lemma 5.6: for semilinear A, a concrete WSVAS simulates one main-branch BVAS step with `I=A∪Reach(B)`. | `Mell.Audit.PaperFidelityBridges.paper_lemma_5_6_bvas_wsvas_exists`; it eliminates the `Semilinear A` code witness inside `Prop` and returns the concrete WSVAS with a pointwise one-step iff. | EQUIVALENT. No code, closure, attractor, or decidability premise remains in the public contract. |
| Lemma 5.7: one-source reduction. | `lemma_5_7_one_source_reduction`. | EXACT. It distinguishes one marked occurrence from one-or-more marked occurrences. |
| Appendix C Lemma C.1 | `lemma_c_1_wsrun_order_iff_higman : WSRunOrder rho sigma <-> WSDirectionLe rho sigma /\ WSHigmanEmbed rho sigma`. | EXACT; direction is retained for empty encodings. |
| Appendix C Corollary C.2 | `corollary_c_2_wsrun_wqo`. | EXACT. Transition types may be infinite. |
| Appendix C Corollary C.3 | recursive `ws_run_order_stitch` plus empty-run and concatenation lemmas. | DERIVED. |
| Appendix C Lemma C.4 | `lemma_c_4_wsrun_exact_amalgamation`. | EXACT; source and target equations are separate conjuncts. |

### Section 6

| Paper item | Coq declaration / dependency | Status |
|---|---|---|
| Theorem 6.1: finite disjoint face-stripping decomposition, finitary face periods, optional empty whole-cone slice. | `Mell.Geometry.FaceStrippingTheorem.face_stripping_theorem`; proper-face dimension is `ordered_stripping_noninitial_face_dimension_lt`. | EQUIVALENT/REPAIRED. The theorem is over `ZSet`, as in the paper. The separate explicit `Periodic Q` premise is redundant because `FullPeriodic Q` contains it (A), so it does not strengthen the mathematical contract. |
| Example 6.2 | Two-dimensional illustration. | Regression only; UNUSED in proof. |
| Lemma 6.3: a Q-diagonal relation cannot go from a later slice to an earlier slice. | `lemma_6_3_stripping_diagonal`. | REPAIRED (R09): zero-based indices and direction are made consistent. The mathematical no-backward-edge claim is exact. |
| Example 6.4 | Illustrative face geometry. | UNUSED. |
| Lemma 6.5: a face contains a period point with exactly its common zero normals. | `Mell.Geometry.FaceZeroPatternWitness.face_zero_pattern_witness`. | EQUIVALENT. The explicit finite supporting-normal list is supplied by the rational-polyhedral H-representation (B). |
| Lemma 6.6: finiteness of minimal integer solutions of rational inequalities. | `Mell.Geometry.FaceStrippingBases.integer_affine_inequalities_finitary`, supported by the checked lattice/Gordan modules. | DERIVED; no unchecked appeal to Schrijver remains. |
| Corollary 6.7 | `Mell.Geometry.Corollary67Finitary.corollary_6_7_finitary`. | EXACT in the H-representation used by Lemma 6.10. |
| Lemma 6.8: removing an extract preserves Q-cylindricity. | `Mell.Geometry.FaceStrippingExtract.extract_remainder_cylindric`. | REPAIRED (R08 argument order), conclusion EXACT. |
| Lemma 6.9: minimal-face extract equals the whole remainder difference. | `lemma_6_9_minimal_extract` and `lemma_6_9_any_minimal_face`. | EXACT; the minimal face is lineality, not assumed to be `{0}`. |
| Lemma 6.10: a maximal nonempty extract is finitary for `Q∩F`. | `lemma_6_10_maximal_extract_finitary`. | REPAIRED (R07): membership is proved for differences, never for arbitrary translated sequence points. Maximality is an actual premise and used. |
| Lemma 6.11: candidate faces remain in the unprocessed suffix and the current face is removed. | `lemma_6_11_stripping_invariants` plus stage-removal lemmas in the same module. | EQUIVALENT. |

### Section 7

| Paper item | Coq declaration / exact content | Status |
|---|---|---|
| Lemma 7.1: every nonempty safety witness has a strictly lower-rank safety witness. | Existing `lemma_7_1_safety_witness_rank_descent`, plus `PaperSafetyWitness`, bidirectional witness conversion, and `paper_lemma_7_1_safety_witness_rank_descent`. | EQUIVALENT. The paper-facing theorem contains only `PaperAttractor`; conversion preserves nodes and strict rank descent. |
| Lemma 7.2: successors cover runs reached from a directed node, modulo the attractor. | `lemma_7_2_safety_witness_successors`. | EQUIVALENT pointwise form. It returns the actual output run, successor node, and occurrence witness. |
| Lemma 7.3: attractor contact propagates across a directed edge with common closed period. | `lemma_7_3_attractor_contact_propagation`. | EXACT; the Coq theorem is slightly more general because it does not require finite generation of the common period. |
| Lemma 7.4: rebasing a directed run inside one of its members stays inside the old node and its period lies in the old closed period. | `lemma_7_4_directed_irun_rebase`. | EXACT. |
| Lemma 7.5: a new node only points to a new node of nondecreasing face index. | `lemma_7_5_new_node_edge_direction` proves index monotonicity between new nodes; `replacement_edge_stays_new_and_nondecreasing` additionally excludes retained old targets and packages existence of the target stage. | DERIVED/EXACT as the conjunction of the two checked theorems. |

## Additional-premise classification

| Coq-side condition | Class | Justification |
|---|---|---|
| `ValidIRun S rho` on statements about `rho ∈ IRuns(B)` | A | It is the definition of initialized-run membership. |
| `NonnegativeSet P` in natural-period geometry | A | The paper writes `P⊆N^d`; Coq's base type is `ZSet`, so the inclusion is explicit. |
| `Periodic Q` alongside `FullPeriodic Q` in Section 6 | A | `FullPeriodic` already contains periodicity; projection derives it. Redundant, not strengthening. |
| finite generator lists for directed cones/faces | A/B | Directed runs are defined with finitely generated cones; rational-polyhedral face theorems construct the lists. |
| a `SemiCode` in the concrete WSVAS | B | `Semilinear A` is existentially a code plus denotation equivalence. Elimination is inside Prop; no code-selection oracle is assumed. |
| `ClosedUnderFreeRuns S I` in Lemma 5.5 | B | It is derived from the paper's `Reach_B(I^+)⊆I`/inductive-invariant assumption by the free-run induction bridge. |
| `witness_safe_semilinear` and `witness_reach_safe` fields | A/B | The paper fixes a semilinear `Phi` with `Reach(B)⊆Phi` before defining a safety witness. Coq packages that ambient context in the record so every update carries it unchanged; it is not a stronger per-update premise. |
| reachable-side `Attractor` field in `SafetyWitness` | B | `paper_attractor_iff_attractor` derives both formulations for arbitrary `A`; `PaperSafetyWitness` conversions preserve all remaining fields and the node list. It is a representation premise automatically obtained from the paper definition. |
| `DirectedConeIncluded u v` in Lemma 3.13 | A | Definitionally `C_u⊆C_v`, exactly the paper premise. |
| ordered finite face list in intermediate Section-6 lemmas | B | `polyhedral_faces_linearized` constructs it from the finitely generated rational cone. The public Theorem 6.1 existentially returns it. |
| explicit supporting normals in Lemma 6.5/Corollary 6.7 | B | The rational-polyhedral H-representation supplies them; they are proof data, not a caller-visible premise of Theorem 6.1. |
| same action in the corrected Appendix-B root lemma | C | Without it Fact B.3 is false. `IRunEmbed` supplies it at matched nodes, so Lemma 3.10's statement is unchanged. |
| strict positive component coefficients in Lemma 4.5 proof | C | Allowing zero adds boundary rays; a checked two-dimensional counterexample witnesses the failure. The numbered conclusion is unchanged. |
| orthant membership in the signed Lemma 2.1 proof | C | R11 is required for signed periodic sets; it repairs the proof, not the theorem statement. |
| difference membership, corrected extract order, and corrected indices in Section 6 | C | R07--R09 each repair an invalid proof step or inconsistent notation without strengthening Theorem 6.1/Lemma 6.3. |
| decidable transitions, finite WSVAS alphabet, nonempty initials, `d>0`, finite generation of arbitrary P in Lemmas 5.1/5.4 | D | **Not present** in the checked contracts. |
| any remaining suspected condition | E | None among the six audited bridge gaps; no unresolved class-D premise was found. |

## Repairs and why they are not hidden strengthening

- **R03, Appendix B:** the article's standalone Fact B.3 omits equality of
  root actions. `old_fact_b3_missing_same_action` in
  `theories/Audit/RepairExamples.v` is a concrete counterexample.  Coq proves
  `root_same_action_mono`; matched nodes of `IRunEmbed` already provide the
  equality, so Lemma 3.10 retains its original hypotheses.
- **Strict-cone repair:** a non-strict coefficient would incorrectly add a
  boundary direction. The audit regressions show the relaxed right-hand side
  contains `(1,0)` while the intended cone does not. Lemma 4.5's conclusion
  is unchanged.
- **R07:** Lemma 6.10 uses `s_n-s_m∈Q∩K^⊥`; it never assumes a translated
  sequence element itself is in `Q`. Fullness is applied only after both
  difference-group and cone membership are proved.
- **R08:** `ExtractFace Q F X Y` means `s+(Q∩F)⊆Y\X`. The implementation
  consistently treats the first set as excluded/lower and the second as the
  current remainder. A one-dimensional regression distinguishes the reversed
  operation.
- **R09:** the implementation is zero-based and forbids edges from a later
  slice to an earlier slice. It does not forbid the converse.
- **R11:** the signed proof of Lemma 2.1 restricts its Dickson argument to the
  actual orthant part. No false cofinality claim over all signed vectors is
  used.

R05 concerns a different, stateful BVASS context-family order. The Section-3
`IRunLe` audited here remains the stateless Appendix-B order; the two were not
silently identified.

## Omitted, externally attributed, and replaced proof material

The following omissions do not leave an unproved dependency in Theorem 3.3:

- Examples and most remarks are explanatory; only counterexamples relevant to
  repairs are retained as executable audits. Remark 2.2 and its Example 2.3
  guard are now checked explicitly.
- Paper appeals to Dickson, Higman, and Kruskal are instantiated by the
  repository's `afs` library and product/list/tree closure theorems.
- The FoSSaCS almost-semilinearity result used by paper Lemma 4.6 is represented
  by a checked special-leaf/doubled-system development; restriction and
  projection are explicit.
- The rational cone, face finiteness, dimension drop, lattice--cone
  intersection, and finite-basis facts used in Section 6 are proved in the
  Geometry modules. There is no opaque mathematical axiom standing for
  Gordan's lemma or Schrijver's integer-basis result.
- Corollary C.3 is not exported under the paper number, but its composition
  content is `ws_run_order_stitch` and the recursive stitching proof used by
  Lemma C.4.
- The implementation-level Lemma 5.6 remains code-parameterized, while the
  public paper bridge existentially hides that presentation. `Semilinear A`
  supplies the code in `Prop`; no executable selection oracle is asserted.

## Historical gaps and their closure

The following six items were `GAP` in the audit at the baseline commit.  They
are retained here as a historical ledger; each is now closed by the named
kernel-checked declaration.

### Lemma 3.10 antisymmetry

The paper defines `wpo` as a **partial** order that is WQO, then calls
`trianglelefteq` a WPO. The baseline repository proved:

```coq
irun_le_refl  : Reflexive IRunLe
irun_le_trans : Transitive IRunLe
irun_le_wqo   : forall d S, afs (ValidIRun S) IRunLe
```

and exact amalgamation, but lacked antisymmetry.  The closure module defines a
mutual node count, proves that below-root embedding is strictly larger, and
reduces equal-count mutual embeddings to ordered, same-action root embeddings.
It proves:

```coq
Mell.BVAS.RunOrderAntisymmetry.irun_le_antisymmetric :
  forall d rho sigma,
    IRunLe rho sigma -> IRunLe sigma rho -> rho = sigma
```

`IRun` has no embedded validity proof and no rule-occurrence index: it stores
the action value, ordered children, and configuration labels. Thus raw equality
is the faithful paper equality; no quotient, UIP, or proof irrelevance is used.
Current classification: `EXACT` (with R03 still `REPAIRED`).

### Paper-shaped standalone wrappers

The missing existential wrapper is now
`paper_lemma_5_6_bvas_wsvas_exists`.  Its only predicate premise is
`Semilinear A`; it returns a WSVAS and a two-argument one-step equivalence with
side set `A union Reach S`. Current classification: `EQUIVALENT`.

### Unused arbitrary-language generality

`Language d := list (NVec d) -> Prop` and ordered `WordShuffle` now express the
paper's arbitrary languages without commutative closure.  Occurrence-aligned
finite substitution yields `fact_3_6_reach_shuffle_flatten`.  Empty languages
remain permitted; only members are required to be nonempty words, as in the
paper. Current classification: `EXACT`.

### Simultaneous leaf monotonicity

`fact_3_2_all_leaf_increments` now quantifies over an arbitrary valid free run
and a same-length list of independent increments.  It constructs the shifted
run, preserves source occurrence order, and proves the exact target equation
with the increment sum. Current classification: `EXACT`.

### Attractor and Safety-Witness bridge

`paper_attractor_iff_attractor` proves the equivalence for every predicate,
with no semilinearity, invariant, decidability, or initial-inclusion premise.
`PaperSafetyWitness` exposes the paper formulation and bidirectional
conversions preserve the exact node list.  The existing rank-descent theorem
therefore yields `paper_lemma_7_1_safety_witness_rank_descent` without an
extra reachable-side premise. Current classification: `EQUIVALENT`.

`remark_2_2_full_iff_closed_linearization_fixed` proves the exact finite-
generation statement over `ZSet d`.  The proof supplies the previously
missing theorem that finitely generated rational cones are topologically
closed.  The Example 2.3 regression proves the unrestricted strengthening is
false. Current classification: `EXACT`.

After these additions none of the six recorded fidelity items remains `GAP`.
This does not assert that every explanatory sentence or example in the paper
has been formalized; items explicitly classified `UNUSED` remain so.

## Main dependency chain

```text
Lemma 2.1 / finite bases
        + Lemma 3.10 run WQO and exact amalgamation
        -> Lemmas 4.6, 4.10, 4.11
        -> Lemmas 3.12 and 3.13

Appendix C + Lemmas 5.4--5.7
        -> Lemma 5.1 safe linearization

Section 6 geometry + repaired Lemmas 6.8--6.11
        -> Theorem 6.1 and Lemma 6.3

Lemma 5.1 + Theorem 6.1 + Lemma 6.3
        -> Lemmas 7.1--7.5
        -> rank descent to an empty Safety Witness
        -> separator_S (Theorem 3.3)
```

There is no dependency from `separator_S` back to singleton separation or the
decision procedure.

## Axiom and trust-boundary result

The focused `Print Assumptions` audit found only two outcomes:

- closed under the global context for core periodic-order, run-amalgamation,
  WSVAS order/amalgamation/simulation, and several local run lemmas;
- `Classical_Prop.classic` for the finite-choice, semilinear-complement,
  geometric, rank-descent, and final separator chain.

No `Axiom`, `Admitted`, `admit`, `Abort`, `ClassicalEpsilon`,
`ClassicalChoice`, countable-choice oracle, UIP/K, `Eq_rect_eq`, functional
extensionality, or disabled kernel check is introduced by the audited chain.
`Classical_Prop.classic` is a foundational proof dependency; it is not an
extra mathematical hypothesis in a public theorem type.

## Verification record

- Branch and baseline commit: matched the requested values.
- Primary-source inventory: Sections 2--7 and Appendices A--C checked from the
  v1 TeX source.
- Focused compilation of all six bridge modules and their boundary regressions:
  PASS under Coq 8.20.1.
- Complete public `Check` and `Print Assumptions` audit: PASS.  Fact 3.2,
  Fact 3.6, raw-run antisymmetry, the Lemma 3.10 package, Remark 2.2, the
  attractor equivalence, and Lemma 5.6 are closed under the global context;
  the paper-shaped Lemma 7.1 has only `Classical_Prop.classic`.
- Forced full `_CoqProject` rebuild: PASS.
- `make -f Makefile.coq validate`, including dependency-closure
  `coqchk -silent`: PASS.
- Targeted `coqchk -silent` for all new modules: PASS.
- `make check-final`, `make audit-final`, and `make extract-final`: PASS.
- Native runtime gate: PASS (22/22 expected YES/NO and codec cases).
- Forbidden-construct scan and target-only `git diff --check`: PASS.
- No reduction, decision, separator, or extraction module imports the new
  Audit bridge; the existing extracted computation path is unchanged.

## Independent review

The baseline fidelity audit was independently reviewed directly against the
v1 TeX and Coq sources.  A further independent review of the six gap-closing
bridges re-opened the primary source and the new Coq modules and reported PASS
with no Critical or Important findings.  It confirmed the exact premises and
conclusions of all six bridges, occurrence-sensitive ordered operations,
raw-run antisymmetry, the finite-generation boundary in Remark 2.2, the
unconditional attractor equivalence, and the one-step scope of Lemma 5.6.  It
also confirmed that no Decision or Reduction module imports the new Audit
bridge.  This review is distinct from kernel checking and `coqchk`.  The
historical GAP findings remain in the record, while the closure table
identifies their verified successor theorems.
