# T10-C4 final integration audit

Date: 2026-10-23

Audited baseline: `2091260e2dd1f34bd02873093c912cb948b4b10d`

Scope: read-only integration audit of T10-C1--C4.  No Gallina definition,
theorem, build configuration, or existing audit artifact was changed.

## 1. Result

The C1--C4 geometry chain is internally complete through the Face-Stripping
Theorem and its directional diagonal corollary.  All required declarations
are present at the audited HEAD, the full Coq build succeeds, and `coqchk`
accepts every principal module.  For the public theorems below,
`Print Assumptions` reports either no assumptions or only
`Classical_Prop.classic`.

This does **not** complete Section 7, the Leroux VAS theorem, the BVASS/VASS
section theorem, the separation theorem used by the conditional BVAS
decision procedure, or unconditional MELL decidability.

## 2. Exact public interfaces

The following types were obtained at this HEAD with `Check`; notation is
printed in the source-facing form used by the project.

```coq
rational_closed_cone_finitely_generated :
  forall d (C : QSet d),
    QDefinable C -> IsCone C -> TopologicallyClosed C ->
    exists generators : list (QVec d),
      SameSet C (qcone_generated generators).

lattice_gordan :
  forall d (group : ZSet d) (cone : QSet d),
    FinitelyGeneratedGroup group ->
    RationalPolyhedralCone cone ->
    FinitelyGeneratedPeriodic
      (fun value => group value /\ cone (zvec_to_qvec value)).

closed_linearization_full :
  forall d (set : ZSet d),
    Periodic set -> FullPeriodic (ClosedLinearization set).

closed_linearization_finitely_generated :
  forall d (set : ZSet d),
    Periodic set -> NonnegativeSet set -> AsymptoticallyDefinable set ->
    FinitelyGeneratedPeriodic (ClosedLinearization set).

center_characterization :
  forall d (set : ZSet d) value,
    Periodic set ->
    (Center set value <->
      Difference set value /\ PositiveSpanningCombination set value).

center_absorbs_closed_linearization :
  forall d (set : ZSet d),
    Periodic set ->
    SameSet
      (fun result => exists value offset,
        Center set value /\
        ClosedLinearization set offset /\
        result = zvec_add value offset)
      (Center set).

closed_linearization_push_in :
  forall d (set : ZSet d),
    Periodic set -> NonnegativeSet set ->
    exists anchor : ZVec d, set anchor /\
      forall offset point : ZVec d,
        Difference set offset ->
        ClosedLinearization set (zvec_sub point anchor) ->
        exists radius : nat, forall n : nat,
          set (zvec_add offset
            (zvec_nsmul (radius + n)%nat point)).

polyhedral_faces_finite :
  forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists faces : list (QSet d),
      (forall face, List.In face faces -> FaceOf cone face) /\
      (forall face, FaceOf cone face ->
        exists representative,
          List.In representative faces /\ SameSet face representative).

polyhedral_faces_linearized :
  forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists faces : list (QSet d),
      (exists tail, faces = cone :: tail) /\
      (forall face, List.In face faces -> FaceOf cone face) /\
      (forall face, FaceOf cone face ->
        exists representative,
          List.In representative faces /\ SameSet face representative) /\
      (forall i j face_i face_j,
        nth_error faces i = Some face_i ->
        nth_error faces j = Some face_j ->
        i <> j -> ~ SameSet face_i face_j) /\
      (forall i j face_i face_j,
        nth_error faces i = Some face_i ->
        nth_error faces j = Some face_j ->
        FaceSubset face_j face_i -> i <= j).

proper_face_dimension_lt :
  forall d (cone face larger : QSet d)
    face_dimension larger_dimension,
    RationalPolyhedralCone cone ->
    FaceOf cone face -> FaceOf cone larger ->
    ProperFaceSubset face larger ->
    SpanDimension face face_dimension ->
    SpanDimension larger larger_dimension ->
    (face_dimension < larger_dimension)%coq_nat.

polyhedral_cone_integer_hrep :
  forall (d : nat) (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists normals : list (ZVec d),
      forall value : QVec d,
        cone value <->
        forall normal : ZVec d,
          List.In normal normals ->
          0 <= qinner (zvec_to_qvec normal) value.

lemma_6_9_minimal_extract :
  forall d (period excluded remaining : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    QCylindric period excluded ->
    QCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    SameSet
      (ExtractFace period (ConeLineality (Cone period))
        excluded remaining)
      (fun value => remaining value /\ ~ excluded value).

lemma_6_10_maximal_extract_finitary :
  forall d (period excluded remaining : ZSet d) (face : QSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    MaximalNonemptyExtractFace period excluded remaining face ->
    FinitaryQCylindric
      (FacePeriod period face)
      (ExtractFace period face excluded remaining).

lemma_6_11_stripping_invariants :
  forall d (period excluded initial_remaining : ZSet d) faces,
    Periodic period ->
    QCylindric period excluded ->
    QCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces ->
    (forall stage, stage <= length faces ->
      QCylindric period
        (StrippingRemainder period excluded initial_remaining
          faces stage)) /\
    (forall stage, stage <= length faces -> forall face,
      StageCandidateFace period excluded initial_remaining
        faces stage face ->
      exists index representative,
        stage <= index /\ index < length faces /\
        nth_error faces index = Some representative /\
        SameSet face representative).
```

The complete Theorem 6.1 package is:

```coq
face_stripping_theorem :
  forall d (period excluded initial_remaining : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    exists faces : list (QSet d),
      OrderedStrippingFaces period faces /\
      nth_error faces 0 = Some (Cone period) /\
      SameSet (StrippingRemainder period excluded initial_remaining
        faces 0) initial_remaining /\
      SameSet (StrippingRemainder period excluded initial_remaining
        faces (length faces)) excluded /\
      (forall stage, stage <= length faces ->
        FinitaryQCylindric period
          (StrippingRemainder period excluded initial_remaining
            faces stage) /\
        forall value, excluded value ->
          StrippingRemainder period excluded initial_remaining
            faces stage value) /\
      (forall stage face,
        stage < length faces ->
        nth_error faces stage = Some face ->
        FinitaryQCylindric (FacePeriod period face)
          (StrippingSlice period excluded initial_remaining
            faces stage) /\
        forall value,
          StrippingSlice period excluded initial_remaining
            faces stage value ->
          initial_remaining value /\ ~ excluded value) /\
      (forall earlier later,
        earlier < later -> later < length faces -> forall value,
        ~ (StrippingSlice period excluded initial_remaining
              faces earlier value /\
           StrippingSlice period excluded initial_remaining
              faces later value)) /\
      (forall value,
        (initial_remaining value /\ ~ excluded value) <->
        exists stage, stage < length faces /\
          StrippingSlice period excluded initial_remaining
            faces stage value) /\
      (BackwardPeriodCover period excluded initial_remaining ->
        forall value,
          ~ StrippingSlice period excluded initial_remaining
              faces 0 value).
```

The directional relation theorem and the same-witness integrated theorem are:

```coq
lemma_6_3_stripping_diagonal :
  forall d (period excluded initial_remaining : ZSet d)
    (faces : list (QSet d))
    (relation : ZVec d -> ZVec d -> Prop),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    OrderedStrippingFaces period faces ->
    QDiagonal period relation ->
    NoBoundaryEdge excluded initial_remaining relation ->
    forall earlier later left right,
      earlier < later -> later < length faces ->
      StrippingSlice period excluded initial_remaining faces later left ->
      StrippingSlice period excluded initial_remaining faces earlier right ->
      ~ relation left right.

face_stripping_theorem_diagonal :
  forall d (period excluded initial_remaining : ZSet d)
    (relation : ZVec d -> ZVec d -> Prop),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period initial_remaining ->
    (forall value, excluded value -> initial_remaining value) ->
    QDiagonal period relation ->
    NoBoundaryEdge excluded initial_remaining relation ->
    exists faces : list (QSet d),
      (OrderedStrippingFaces period faces /\
       nth_error faces 0 = Some (Cone period) /\
       SameSet (StrippingRemainder period excluded initial_remaining
         faces 0) initial_remaining /\
       SameSet (StrippingRemainder period excluded initial_remaining
         faces (length faces)) excluded /\
       (forall stage, stage <= length faces ->
         FinitaryQCylindric period
           (StrippingRemainder period excluded initial_remaining
             faces stage) /\
         forall value, excluded value ->
           StrippingRemainder period excluded initial_remaining
             faces stage value) /\
       (forall stage face,
         stage < length faces -> nth_error faces stage = Some face ->
         FinitaryQCylindric (FacePeriod period face)
           (StrippingSlice period excluded initial_remaining
             faces stage) /\
         forall value,
           StrippingSlice period excluded initial_remaining
             faces stage value ->
           initial_remaining value /\ ~ excluded value) /\
       (forall earlier later,
         earlier < later -> later < length faces -> forall value,
         ~ (StrippingSlice period excluded initial_remaining
               faces earlier value /\
            StrippingSlice period excluded initial_remaining
               faces later value)) /\
       (forall value,
         (initial_remaining value /\ ~ excluded value) <->
         exists stage, stage < length faces /\
           StrippingSlice period excluded initial_remaining
             faces stage value) /\
       (BackwardPeriodCover period excluded initial_remaining ->
         forall value,
           ~ StrippingSlice period excluded initial_remaining
               faces 0 value)) /\
      (forall earlier later left right,
        earlier < later -> later < length faces ->
        StrippingSlice period excluded initial_remaining
          faces later left ->
        StrippingSlice period excluded initial_remaining
          faces earlier right ->
        ~ relation left right).
```

Important connectors additionally checked were
`face_zero_pattern_witness`,
`periodic_polyhedral_common_zero_pattern_normals`,
`integer_affine_inequalities_finitary`,
`affine_group_inequalities_finitary`, `corollary_6_7_finitary`, and
`extract_remainder_cylindric`.  They respectively provide the per-face
zero-pattern witness, one fixed normal list valid for all faces, the integer
affine finite bases, the finite-generated-group restriction, Corollary 6.7's
threshold slice, and Lemma 6.8's remainder cylindricity.  The separate
`finitary_qcylindric_sub` theorem is a later finite-basis inheritance tool;
it is not the implementation of Lemma 6.8.

## 3. Correspondence with Bizière--Leroux--Sutre (2026)

The comparison is against the cited arXiv v1.  “Stronger” below means the
Coq theorem permits a wider domain; it does not mean a stronger paper result
has been silently assumed.

| Paper | Coq public theorem(s) | Paper hypotheses | Coq hypotheses | Difference/status |
|---|---|---|---|---|
| Lemma 4.7 | `closed_linearization_push_in` | periodic subset of `N^d`; closed linearization | `Periodic`, explicit `NonnegativeSet` | Same content; nonnegativity is explicit. Verified. |
| Lemma 4.8 | `center_characterization` | periodic set and the paper's center/positive spanning notions | `Periodic` | Coq is formulated on signed `ZVec`; otherwise exact. Verified. |
| Lemma 4.9 | `center_absorbs_closed_linearization` | periodic set | `Periodic` | Signed-vector generalization. Verified. |
| Lemma 6.3 | `lemma_6_3_stripping_diagonal`; `face_stripping_theorem_diagonal` | full finitely generated periodic `Q`, finitary `X subset Y`, `Q`-diagonal relation, no edge from `X` to `Y\\X` | The same properties, with inclusion and boundary condition explicit | Exact directional result: later slice to earlier slice only. Verified. |
| Lemma 6.5 | `periodic_polyhedral_common_zero_pattern_normals`; generic core `face_zero_pattern_witness` | one fixed finite supporting-normal family `E`, valid for every face of `Cone(Q)` | `Periodic`, rational polyhedrality for construction of the common `E`; the core takes `FaceOf` and `Forall SupportingNormal` | The common-E quantifier order is preserved; the core works for signed periods. Verified. |
| Lemma 6.6 | `integer_affine_inequalities_finitary`; downstream bridge `affine_group_inequalities_finitary` | integer affine inequalities on the ambient integer lattice | no extra premise for the ambient theorem; the bridge assumes `FinitelyGeneratedGroup` | Ambient result is exact; the group-restricted theorem is a Coq strengthening needed by Corollary 6.7. Verified. |
| Corollary 6.7 | `corollary_6_7_finitary` | full finitely generated periodic `Q`, finite integer H-representation and tight subset | explicit `Periodic`, finite generation, fullness, H-representation, and sublist premise | Exact threshold-slice conclusion; rational equalities use two ceiling constraints internally. Verified. |
| Lemma 6.8 | `extract_remainder_cylindric` | the remainder `Y minus Extract_F(X,Y)` is `Q`-cylindric | `Periodic`, `FaceOf`, cylindricity of `X,Y`, and `X subset Y` | Exact. Verified. |
| Lemma 6.9 | `lemma_6_9_minimal_extract` | minimum face and cylindric `X subset Y` | explicit `Periodic`, finite generation, fullness, and both cylindricities | The minimum face is constructively identified as cone lineality; no pointedness. Verified. |
| Lemma 6.10 | `lemma_6_10_maximal_extract_finitary` | maximal face with nonempty extract; finitary `X,Y` | explicit periodic/finite/full premises and `MaximalNonemptyExtractFace` | Exact. Verified. |
| Lemma 6.11 | `lemma_6_11_stripping_invariants` plus `stripping_remainder_finitary` and `stripping_slice_finitary` | recursive remainders are cylindric; remaining candidate faces occur later | `OrderedStrippingFaces` packages enumeration and reverse-inclusion order | Exact invariant core and finite-basis consequences. Verified. |
| Theorem 6.1 | `face_stripping_theorem` | full finitely generated periodic `Q`; finitary `X subset Y` | the same properties are explicit | Full 0-based partition, finite bases, and optional first-slice emptiness. Verified. |

The paper assumes positive ambient dimension and works inside nonnegative
integer vectors.  Several Coq declarations also cover dimension zero and
signed periodic subsets, but downstream applications may instantiate the
paper's narrower setting without an adapter.

## 4. Section 7 connection audit

The existing geometry theorem supplies exactly the ordering fact used in
Lemma 7.5.  Instantiating `relation` with BVAS reachability, the conclusion

```text
earlier < later ->
left in S_later -> right in S_earlier ->
not relation left right
```

is the paper's `i < j -> R cap (S_j x S_i) = empty` under the repository's
0-based indexing.  `face_stripping_theorem_diagonal` obtains this property
for the **same** existential `faces` witness as every Theorem 6.1 clause.
No new geometric wrapper is needed.

The Section 7 instantiation is not yet formalized.  It still needs:

- a BVAS reachability relation on the chosen signed-vector carrier and a
  proof that it is `QDiagonal` for the directed-irun period;
- the attractor/safety-witness argument yielding `NoBoundaryEdge X Y R`;
- definitions of attractors, safety witnesses, directed iruns, abstract
  graph nodes, and their reach relation;
- identification of each directed-irun period with the corresponding
  `FacePeriod`;
- a bridge from `SpanDimension` and `proper_face_dimension_lt` to the
  well-founded lexicographic rank used in Lemma 7.1;
- a bridge from `FinitaryQCylindric` finite translates to the repository's
  `Semilinear`/code representation before newly constructed graph nodes can
  be called semilinear.

Consequently Lemma 7.5 can consume the C4 conclusion directly once its BVAS
premises are proved, while Lemma 7.1 remains a substantial Section 7 proof.

## 5. Assumption and dependency audit

`Print Assumptions` at the audited HEAD gave:

- closed under the global context:
  `closed_linearization_full`, `polyhedral_cone_integer_hrep`,
  `finitary_qcylindric_sub`, and `lemma_6_9_minimal_extract`;
- only `Classical_Prop.classic`:
  `rational_closed_cone_finitely_generated`, `lattice_gordan`,
  `closed_linearization_finitely_generated`, `center_characterization`,
  `center_absorbs_closed_linearization`, `closed_linearization_push_in`,
  `polyhedral_faces_finite`, `polyhedral_faces_linearized`,
  `proper_face_dimension_lt`, `face_zero_pattern_witness`,
  `periodic_polyhedral_common_zero_pattern_normals`,
  `integer_affine_inequalities_finitary`,
  `affine_group_inequalities_finitary`, `corollary_6_7_finitary`,
  `extract_remainder_cylindric`,
  `lemma_6_10_maximal_extract_finitary`,
  `lemma_6_11_stripping_invariants`, `face_stripping_theorem`,
  `lemma_6_3_stripping_diagonal`, and
  `face_stripping_theorem_diagonal`.

`Print All Dependencies` was also run for the rational-cone finite-generation
entry, Lemma 6.10, and the integrated diagonal theorem.  Its transitive list
contains ordinary proved standard-library declarations (including decidable
equality infrastructure); it introduces no additional assumption beyond the
`Print Assumptions` result above.

A source scan of `theories/Geometry` found no `Axiom`, `Admitted`, `Abort`,
`ClassicalEpsilon`, functional extensionality, `Eq_rect_eq`, or UIP use.

## 6. Verification

- full build: `opam exec --switch . -- make -f Makefile.coq -j2` — exit 0;
- `coqchk -silent` over the 15 principal C1--C4 modules — exit 0;
- exact `Check` and `Print Assumptions` audit of the required public results
  and correspondence connectors — exit 0;
- target source scan and repository-status preservation check — passed;
- independent review — passed for theorem direction, same-face-list reuse,
  Section 7 mapping, and the outstanding connector list.

No mathematical blocker was found inside C1--C4.  The remaining blockers are
downstream interfaces and theorems listed in Sections 4 and 7 above.
