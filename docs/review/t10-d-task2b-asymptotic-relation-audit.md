# T10-D Task 2B: asymptotically definable relation composition

Date: 2026-10-23

Baseline: `a416c86eedf0d09bb2882fde70b62dbd19e18a24`

Scope: Leroux (2012), Lemma 5.1.  This unit proves the composition closure of
periodic relations whose rational cones are first-order definable over
`(Q,+,<=)`.  It does not prove that every capacity transformer has this
property and does not enter intraproductions or production graphs.

## 1. Pair encoding and the natural-relation bridge

```coq
Definition ZRelation (d : nat) := ZVec d -> ZVec d -> Prop.

Definition ZRelCompose {d} (R S : ZRelation d) : ZRelation d :=
  fun input output => exists middle, R input middle /\ S middle output.

Definition ZRelationPairs {d} (R : ZRelation d) : ZSet (d + d) :=
  fun pair => R (zpair_left pair) (zpair_right pair).
```

`zpair_pack` is vector append, while `zpair_left` and `zpair_right` use
`Vector.splitat`.  The implementation proves both round trips, injectivity,
and preservation of zero, addition, natural scalar multiplication, and the
integer-to-rational embedding.  The corresponding rational pair operations
preserve `QVecEq`; no Leibniz equality of non-normalized rationals is assumed.

The natural relation lift is exact:

```coq
Definition NRelationAsZ {d} (R : NRelation d) : ZRelation d :=
  fun input output =>
    exists ninput noutput,
      input = nvec_to_zvec ninput /\
      output = nvec_to_zvec noutput /\
      R ninput noutput.
```

Thus a signed vector belongs only when it is exactly the image of a natural
vector.  Negative coordinates are never truncated.  The lift preserves
composition, nonnegativity, witness uniqueness, and periodicity.

## 2. Periodic integer relations and their rational cones

```coq
Definition PeriodicZRelation {d} (R : ZRelation d) : Prop :=
  R (zvec_zero d) (zvec_zero d) /\
  forall x1 y1 x2 y2,
    R x1 y1 -> R x2 y2 ->
    R (zvec_add x1 x2) (zvec_add y1 y2).

Definition RationalRelationCone {d} (R : ZRelation d)
    (input output : QVec d) : Prop :=
  Cone (ZRelationPairs R) (qpair_pack input output).
```

`PeriodicZRelation R` is proved equivalent to
`Periodic (ZRelationPairs R)`.  Composition is periodic by adding its two
integer middle witnesses.  The relation cone is the existing algebraic
finite nonnegative-rational cone—not a topological closure.  Public lemmas
establish its zero, addition, nonnegative rational scaling, generator
membership, pair splitting, and `QVecEq` extensionality.

The denominator-clearing interface is:

```coq
periodic_cone_positive_multiple_iff :
  forall k (set : ZSet k) point,
    Periodic set ->
    (Cone set point <->
      exists multiplier : nat, exists integer_point : ZVec k,
        (0 < multiplier)%nat /\ set integer_point /\
        QVecEq (qvec_scale (q_of_nat multiplier) point)
          (zvec_to_qvec integer_point)).
```

It is a specialization of the existing
`periodic_standard_cone_denominator_clearing`.  The multiplier is strictly
positive, and periodicity is used to combine the cleared finite coefficients
inside the original set.

## 3. Cone/composition exchange

```coq
periodic_relation_cone_compose :
  forall d (R S : ZRelation d),
    PeriodicZRelation R -> PeriodicZRelation S ->
    forall input output : QVec d,
      (RationalRelationCone (ZRelCompose R S) input output <->
       exists middle : QVec d,
         RationalRelationCone R input middle /\
         RationalRelationCone S middle output).
```

For the forward direction, denominator clearing of the composed pair exposes
an integer middle witness; dividing its embedding by the positive multiplier
gives the rational middle point.

For the reverse direction, the two positive multipliers are replaced by
their product.  Periodicity supplies the required integer multiples of both
relation witnesses.  The two candidate middle integer vectors have
`QVecEq`-equal rational embeddings; `zvec_to_qvec_injective` turns this into
Leibniz equality before constructing the relation-composition witness.  This
is the step that prevents an unproved identification of the middle points.

The regression uses singleton relations at `(1,1)` and `(2,2)` to record why
periodicity cannot be removed: their relation composition is empty because
the middle values differ.  A positive regression proves composition of
`y=2*x` and `z=3*y` is exactly `z=6*x`.  A signed instance checks the same
relation at `-3`, and a separate `QVecEq` regression checks the non-normalized
representations `1/2` and `2/4`.

## 4. Rational first-order definability

The new syntax adapter is deliberately limited to coordinate preimages.  It
renames only free vector coordinates, shifts those coordinates under
`QFExists`/`QFForall`, and proves both formula closedness and semantic
preservation.  Two pair formulas are pulled back to the `(x,y,z)` tuple,
intersected with `qdefinable_intersection`, and the middle block is eliminated
with the existing `qdefinable_projection`.

```coq
qdefinable_relation_compose :
  forall d (left right : QSet (d + d)),
    QSetExtensional left -> QSetExtensional right ->
    QDefinable left -> QDefinable right ->
    QDefinable (fun pair => exists middle : QVec d,
      left (qpair_pack (qpair_left pair) middle) /\
      right (qpair_pack middle (qpair_right pair))).
```

The triple selectors and their reconstruction lemmas are proved for all
dimensions, including `d=0`.  Bound-variable positions, free-variable
positions, and the output `(x,z)` projection are checked independently.

## 5. Leroux Lemma 5.1

```coq
Definition AsymptoticallyDefinableZRelation {d} (R : ZRelation d) : Prop :=
  PeriodicZRelation R /\ QDefinable (RelationConePairs R).

lemma_5_1_asymptotic_relation_compose :
  forall d (R S : ZRelation d),
    AsymptoticallyDefinableZRelation R ->
    AsymptoticallyDefinableZRelation S ->
    AsymptoticallyDefinableZRelation (ZRelCompose R S).

lemma_5_1_nrelation_compose :
  forall d (R S : NRelation d),
    AsymptoticallyDefinableNRelation R ->
    AsymptoticallyDefinableNRelation S ->
    AsymptoticallyDefinableNRelation (NRelCompose R S).
```

The integer theorem combines periodicity, cone/composition exchange, and the
formula-level composition theorem.  The natural theorem first uses the exact
nonnegative lift, then transports the result across the proved extensional
equivalence between the two lifted compositions.  This completes Lemma 5.1;
there is no remaining mathematical premise inside that lemma.

## 6. Conditional run-transformer application

```coq
transformer_along_run_asymptotic_of_capacities :
  forall d (system : PlainVAS d) (run : VASRun d),
    (forall capacity,
      List.In capacity (RunSource run :: RunTargets run) ->
      AsymptoticallyDefinableNRelation
        (CapacityTransformer system capacity)) ->
    AsymptoticallyDefinableNRelation
      (TransformerAlongRun system run).
```

`TransformerAlongTargets` always contains at least the source capacity, even
for a length-zero run.  Consequently the proof starts from that capacity and
inducts over the target list; it does not need an artificial empty-composition
identity case.  This theorem is conditional: Task 2B does not assert that a
capacity transformer is asymptotically definable.  The regression instantiates
the theorem with a run containing two targets (three capacities), checking
that the finite-composition induction uses every listed capacity premise.

## 7. Verification and assumptions

The initial audit import failed before `RelationCone` and
`AsymptoticRelation` existed (RED).  The focused source and regression build,
the complete `_CoqProject` build, and `coqchk -silent` succeed at the current
HEAD.  Target-only `git diff --check` and scans for forbidden proof escapes
also succeed.

`Print Assumptions` reports `Closed under the global context` for:

- `periodic_cone_positive_multiple_iff`;
- `periodic_relation_cone_compose`;
- `qdefinable_relation_compose`;
- `lemma_5_1_asymptotic_relation_compose`;
- `lemma_5_1_nrelation_compose`;
- `transformer_along_run_asymptotic_of_capacities`.

No new axiom, `Admitted`, `Abort`, `ClassicalEpsilon`, choice oracle, UIP/K,
`Eq_rect_eq`, functional extensionality, or runtime oracle occurs in the
target files.  No use of `Classical_Prop.classic` is introduced by Task 2B.

An independent review recompiled the three modules, reran `coqchk -silent`,
checked the six public assumption reports and forbidden-construction scan,
and inspected the common-multiplier/middle-vector argument, bound-variable
reindexing, exact natural lift, and scope boundary.  It reported no Critical,
Important, or Minor findings.

## 8. Task 3 handoff

The next stage still must prove the missing premise of the conditional run
theorem.  In the terminology of Leroux (2012), that requires formalizing
intraproductions, production graphs, and their Kirchhoff relation, then
showing that each capacity transformer has the required rationally definable
cone.  Task 2B provides composition closure only; it does not supply that base
case and does not claim Corollary 5.16.
