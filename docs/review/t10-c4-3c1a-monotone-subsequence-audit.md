# T10-C4-3C1A monotone-subsequence audit

Baseline: `e2bc7f545ee6f4219ae5b8e2edb5465c49aeb9c8`.

## Implemented boundary

This checkpoint proves the infinite `PeriodicLe`-monotone subsequence bridge
needed twice by Lemma 6.10.  It stops before C4-3C1B and contains no geometric
contradiction argument.

The main theorem is:

```coq
finitary_qcylindric_monotone_subsequence :
  forall d (period set : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FinitaryQCylindric period set ->
    forall sequence : nat -> ZVec d,
      (forall n, set (sequence n)) ->
      exists indices : nat -> nat,
        (forall n, indices n < indices (S n)) /\
        (forall n,
          PeriodicLe period
            (sequence (indices n))
            (sequence (indices (S n)))).
```

## Constructive witness path

No strengthening of `afs` or iteration of `af_good_pair` is assumed.  The
proof exposes the finite data already present in the hypotheses:

1. `FinitaryQCylindric` supplies a finite base list.
2. `FinitelyGeneratedPeriodic` supplies a finite period-generator list and an
   `NVec` coefficient witness for every increment.
3. A representation is the pair `(base position, coefficient vector)`.
   Its correctness predicate uses `nth_error` and integer-vector equality, so
   it is decidable.
4. `pair_codec nat_codec (nvec_codec k)` makes the witness type countable.
   `constructive_indefinite_description_nat` performs terminating linear
   search for each sequence entry, producing an actual representation
   function.  This is the explicit Prop-to-function bridge; no choice oracle
   is used.
5. Finite pigeonhole reasoning selects a base position occurring arbitrarily
   far out.  Its successive occurrences are again found by decidable linear
   search.
6. `nvec_monotone_subsequence` is proved by coordinate induction.  The
   one-dimensional step separates an infinitely repeated value from the case
   where every finite lower set eventually disappears.  It therefore builds
   a nondecreasing subsequence without postulating an infinite Dickson
   theorem.
7. Equal base positions cancel.  `linear_combination_sub` turns componentwise
   coefficient growth into a generated period increment, hence `PeriodicLe`.

The installed Kruskal `Dickson_lemma` and `af_good_pair` were audited; both
provide only a finite good pair, not an infinite chain.  They are deliberately
not used as if they supplied the stronger conclusion.

## Reindexing API

The module additionally proves:

- `strictly_increasing_unbounded` and `strictly_increasing_compose`;
- `periodic_le_sequence`, extending adjacent comparisons to arbitrary ordered
  indices;
- `eventually_constant_strict_subsequence`;
- `tail_unbounded_strict_subsequence` for nondecreasing integer sequences;
- `finite_supporting_normals_tail_reindex`.

The last theorem consumes C3C0's common tail index `N` and uses
`tail_reindex sequence N`.  Constant normals are constant from the new index
zero, unbounded normals remain tail-unbounded, and every supporting-normal
inner-product sequence remains nondecreasing.  Thus a later threshold must be
taken from the reindexed zeroth element, not the original sequence's zeroth
element.

## Axiom audit

`Print Assumptions` for the main theorem, `nvec_monotone_subsequence`, and the
finite-normal tail theorem reports only:

```text
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

The classical uses select an infinitely recurring finite color or distinguish
the repeated-value case.  Every successive index and every finite-generated
representation is obtained by decidable constructive search.  There is no
`ClassicalEpsilon`, countable/dependent choice, new axiom, `Admitted`, `Abort`,
UIP/K, `Eq_rect_eq`, functional extensionality, or external oracle.

## Regression scope

The focused audit covers exact public types, dimension zero, constant and
strictly increasing sequences, an initially decreasing sequence with a
monotone tail, alternating finite-base colors, and a tail-unbounded integer
sequence starting below zero.  The theorem itself is polymorphic in the
period and hence covers the audited finitely generated periods `{0}`, `N`,
`2N`, `N²`, `Z`, low-rank periods, signed generators, duplicate generators,
zero generators, and the empty generator list established by the preceding
periodic-order regressions.

## Verification

- RED: the focused audit initially used `Fail Check` for the missing main,
  strict-index, and finite-normal-tail declarations.
- GREEN: both the source module and focused audit compile.
- The complete `_CoqProject` build succeeds.
- `coqchk -silent -Q theories Mell` succeeds for the source and audit modules.
- The prohibited-token scan and scoped `git diff --check` succeed.

## Independent review

An independent read-only review returned `READY` with no Critical or Important
findings.  It confirmed the representation search does not assume choice, the
base cancellation and `PeriodicLe` direction are correct, the common tail is
used at reindexed zero, and the generic generated-period regression covers the
requested empty, zero, duplicate, signed, and low-rank generator cases.  One
editorial `N2` spelling was corrected to `N²`.

## C4-3C1B boundary

C4-3C1B must apply the theorem to the relevant finitary slice, reindex by the
common normal-classification tail, and carry out the geometric contradiction.
It must use the reindexed first value for the Corollary 6.7 thresholds.  No
part of that contradiction or Lemma 6.10 is implemented here.
