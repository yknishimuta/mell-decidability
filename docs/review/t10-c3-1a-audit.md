# T10-C3-1A audit: rational span and a finite spanning list

Date: 2026-10-20

Baseline: `e09a7a3579aca9f502567ca52f285ac6931dedec`

Scope: C3-1A only.  This unit formalizes the rational vector space generated
by a periodic integer set and extracts a finite spanning list from the set.
It does not define positive spanning combinations and does not prove Lemma
4.8's center characterization (C3-1B).

## Definitions and equality

The project already uses the global name `Vec` for length-indexed Coq
vectors, so the mathematical `Vec(P)` is exposed as `VecOf P` rather than
shadowing that existing public type.

```coq
QSpan generators value :=
  exists coefficients : Vector.t Q (length generators),
    QVecEq value (qgroup_combination generators coefficients)

VecOf set value :=
  exists generators : list (ZVec d),
    List.Forall set generators /\ QSpan generators value
```

The coefficient vector is aligned with every occurrence of the generator
list.  Coefficients range over all of standard `Q`: positive, negative, and
zero values are all admitted.  Generator duplication is therefore preserved
and no decidable equality on `QVec` or `ZVec` is assumed.  `QVecEq`, not
Leibniz equality of rational representations, is the public numerical
equality.

## Public theorem

With `Set Printing Implicit`, the completed theorem is:

```coq
finite_p_spanning :
  forall (d : nat) (set : ZSet d),
    @Periodic d set ->
    exists generators : list (ZVec d),
      @List.Forall (ZVec d) set generators /\
      forall value : QVec d,
        @VecOf d set value <-> @QSpan d generators value
```

The required vector-space operations are constructive and have types:

```coq
qspan_zero : forall d generators,
  QSpan generators (qvec_zero d)

qspan_add : forall d generators left right,
  QSpan generators left -> QSpan generators right ->
  QSpan generators (qvec_add left right)

qspan_opp : forall d generators value,
  QSpan generators value -> QSpan generators (qvec_opp value)

qspan_scale : forall d generators coefficient value,
  QSpan generators value ->
  QSpan generators (qvec_scale coefficient value)
```

The empty generator list spans exactly the zero vector: its only coefficient
vector has length zero and `qgroup_combination []` is `qvec_zero`.  This is
exposed as the bidirectional lemma:

```coq
qspan_nil_iff : forall d (value : QVec d),
  QSpan ([] : list (ZVec d)) value <-> QVecEq value (qvec_zero d)
```

## Finite-generation bridge

The proof reuses these completed interfaces without changing them:

```coq
FinitelyGeneratedGroup group :=
  exists generators : list (ZVec d),
    SameSet group (ZGroupGenerated generators)

difference_group_finitely_generated :
  forall d (set : ZSet d),
    Periodic set -> FinitelyGeneratedGroup (Difference set)
```

For every selected group generator, `generated_generator` and
`zvec_generated_in_zgroup_generated` first prove membership in the generated
group.  The `SameSet` witness then supplies its `Difference set` proof, which
is destructed into two actual set elements.  Concatenating those witness
pairs produces the finite list whose elements all lie in `set`.

Each difference generator is the rational combination `1 * left + (-1) *
right`.  `qgroup_combination_inject` connects integer group combinations to
rational combinations.  Since every element of a periodic set is its own
difference from zero, every source element is in the rational span of the
constructed list.  Closure under arbitrary rational combinations completes
both directions of `finite_p_spanning`.

No MathComp `rat` adapter, Gaussian elimination, basis selection, linear
independence, or cardinality bound is introduced.

## Regression and the C3-1B boundary

The examples cover dimension zero, the zero monoid, `2N`, the full integer
line, a low-rank submonoid of `Z^2`, mixed-sign generators, an empty spanning
list, and a duplicated spanning list.

For `P = Z`, an independent one-dimensional spanning list such as `[1]`
spans the rational line only because negative coefficients are available.
It cannot express `-1` with strictly positive coefficients.  Lemma 4.8's
later positive-combination characterization therefore must permit a
dependent list such as `[1; -1]`; C3-1B must not replace the finite spanning
list by an independent basis or weaken strict positivity to nonnegativity.

C3-1B still needs:

1. `PositiveSpanningCombination P value`, using a finite `P`-list that spans
   `VecOf P` and a coefficient at every occurrence satisfying `0 < q`;
2. the forward implication from `Center P value` to membership in
   `Difference P` plus such a strictly positive combination;
3. the reverse push-in argument from the positive combination to `Center`;
4. exact handling of duplicates and zero coefficients introduced by
   intermediate algebra without weakening the final strict inequalities.

## RED/GREEN and trust boundary

RED was observed before implementation: the audit module failed with
`Cannot find a physical path bound to logical path RationalSpan with prefix
Mell.Geometry`.

All span-operation lemmas and the integer/rational connection are closed
under the global context.  `finite_p_spanning` inherits only
`Classical_Prop.classic`, through `difference_group_finitely_generated` and
its T10-B finite-basis proof.  It does not depend on ClassicalEpsilon,
UIP/K, `Eq_rect_eq`, functional extensionality, a new axiom, or an oracle.

Fresh final verification on the completed tree used:

```text
make CORE_LOG_DIR=/tmp/mell-c3-1a-final-logs audit-t10-c3-1a
opam exec --switch . -- make -f Makefile.coq -j2
```

Both commands exited 0.  The focused target rebuilt and evaluated the
examples, checked the theorem names and expected classical dependency, ran
`coqchk -silent` on `Mell.Geometry.RationalSpan` and
`Mell.Audit.RationalSpanExamples`, and rejected forbidden proof escapes.
The full Coq regression reported that all targets were up to date and exited
0.

An independent review reported **Ready**, with no critical, important, or
minor findings.  It separately checked the definitions, both directions of
the public equivalence, the empty and duplicate cases, the integer-group
bridge, the complete assumptions output, and both modules with `coqchk`.
