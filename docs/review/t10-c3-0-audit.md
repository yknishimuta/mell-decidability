# T10-C3-0 audit: center of a periodic set

Date: 2026-10-20

Baseline: `6cf77b2e3b743773685a75aafd80c8112c16c3f1`

Scope: T10-C3-0 only.  This unit fixes the definition of the center, proves
its two elementary closure properties, and records the linear-algebra
interface needed by C3-1.  It does not formalize Lemma 4.8, push-in, faces,
or any later C3 task.

## Source contract

Bizière--Leroux--Sutre, *Solving the Reachability Problem for Branching
Vector Addition Systems via Semilinear Inductive Invariants* (2026),
Section 4.1 defines the center of a periodic set `P` as the vectors `v` such
that, for every `g` in `P-P`, some natural `r` satisfies `g + (r + N)v`
included in `P`.  The Gallina definition preserves that quantifier order
literally:

```coq
Definition Center {d} (set : ZSet d) : ZSet d :=
  fun value =>
    forall offset, Difference set offset ->
      exists radius : nat, forall n : nat,
        set (zvec_add offset
          (zvec_nsmul (radius + n)%nat value)).
```

Source: <https://arxiv.org/html/2607.09558v1#S4.SS1> (Definition preceding
Lemma 4.8).  In particular, the offset ranges over the actual `Difference
P`; it is not replaced by the ambient integer space.

## Public interface

With `Set Printing Implicit`, the completed public theorems are:

```coq
center_in_difference :
  forall (d : nat) (set : ZSet d) (value : ZVec d),
    @Periodic d set -> @Center d set value -> @Difference d set value

center_add :
  forall (d : nat) (set : ZSet d) (left right : ZVec d),
    @Periodic d set ->
    @Center d set left ->
    @Center d set right ->
    @Center d set (@zvec_add d left right)
```

`center_in_difference` compares two consecutive points in the eventual
tail.  `center_add` obtains a tail for `left` at the requested offset and a
tail for `right` at zero, then uses periodic addition at the common index
`left_radius + right_radius + n`.  Neither proof assumes finite generation,
nonnegativity, or asymptotic definability.

The definition deliberately has no unconditional zero law.  The regression
set `2N` contains zero and is periodic, but offset `-2` belongs to its
difference set; adding any multiple of the zero vector leaves `-2` outside
`2N`.  Hence zero is not central there.

## C3-1 linear-algebra interface audit

No project declaration currently defines `Vec(P)`, a finite spanning list
drawn from `P`, or `PositiveSpanningCombination`.  The project-native
representation is `QVec d := Fin.t d -> Q` using Coq's standard `Q` and
numeric equality `QVecEq`.  `qlinear_combination` in
`Mell.Geometry.LatticeGordanV` already expresses an aligned finite rational
combination, but its cone lemmas impose nonnegative coefficients; it must
not be reused to weaken strict positivity.

MathComp supplies the following useful finite-dimensional declarations:

```coq
span : forall (K : fieldType) (vT : vectType K),
  seq vT -> {vspace vT}

memv_span : forall (K : fieldType) (vT : vectType K)
  (X : seq vT) (v : vT), v \in X -> v \in <<X>>%VS

coord_span : forall (K : fieldType) (vT : vectType K) (n : nat)
  (X : n.-tuple vT) (v : vT),
  v \in <<X>>%VS ->
  v = (\sum_i @coord K vT n X i v *: X`_i)%R
```

Coq-Polyhedra's `extra_misc` additionally supplies:

```coq
span_gen : forall (K : fieldType) (vT : vectType K), seq vT -> seq vT

span_gen_basis : forall (K : fieldType) (vT : vectType K) (S : seq vT),
  basis_of <<S>> (@span_gen K vT S)

span_gen_sub : forall (K : fieldType) (vT : vectType K) (S : seq vT),
  subseq (@span_gen K vT S) S

span_gen_span_eq : forall (K : fieldType) (vT : vectType K) (S : seq vT),
  <<S>>%VS = <<@span_gen K vT S>>%VS
```

These results operate on an already finite sequence over MathComp's field
representation (`rat` for the intended instantiation).  They do not by
themselves extract a finite spanning subsequence from an arbitrary predicate
`P : ZSet d`, and the existing `MathCompRationalAdapter` does not convert
standard `QVec`/`QVecEq` to MathComp rows.  C3-1 therefore still needs the
following project-native bridge (names provisional, mathematical types
fixed):

```coq
qvec_span_finite_subset :
  forall d (P : ZSet d),
    exists spanning : list (ZVec d),
      Forall P spanning /\
      forall p, P p ->
        exists coefficients : list Q,
          length coefficients = length spanning /\
          QVecEq (zvec_to_qvec p)
            (qlinear_combination
              (List.map zvec_to_qvec spanning) coefficients)

PositiveSpanningCombination P value :=
  exists spanning : list (ZVec d),
    Forall P spanning /\
    (* spanning generates Vec(P) over Q *) /\
    exists coefficients : list Q,
      length coefficients = length spanning /\
      Forall (fun coefficient => (0 < coefficient)%Q) coefficients /\
      QVecEq (zvec_to_qvec value)
        (qlinear_combination
          (List.map zvec_to_qvec spanning) coefficients)
```

The remaining C3-1 theorem is exactly the source's Lemma 4.8:

```coq
forall d (P : ZSet d) value,
  Periodic P ->
  (Center P value <->
    Difference P value /\ PositiveSpanningCombination P value)
```

The missing work is (1) a native finite-dimensional span definition and
finite-spanning-subset lemma, or a proved `Q`/`rat` row adapter that transfers
the MathComp results; (2) arbitrary-sign rational combination algebra; and
(3) the two directions of Lemma 4.8 with every coefficient strictly
positive.  These are recorded only; no C3-1 theorem is asserted here.

## Regression and trust boundary

The audit examples cover dimension zero, the zero monoid, `2N`, and the gap
monoid `{0} union {n | n >= 2}`.  They prove zero is not central in `2N`, and
that `1` is central but is not a member of the gap monoid.

Both public theorems are constructive and are closed under the global
context.  They use no classical axiom, choice principle, UIP/K,
`Eq_rect_eq`, functional extensionality, or oracle.

RED was observed before the implementation: the audit module failed with
`Cannot find a physical path bound to logical path Center with prefix
Mell.Geometry`.  GREEN used the focused `check-t10-c3-0` target, followed by
the complete `Makefile.coq` build.  The focused `audit-t10-c3-0` target
confirmed both complete public types, two `Closed under the global context`
reports, forbidden-dependency scans, and `coqchk -silent` exit status zero.
All command logs were directed to a temporary directory so pre-existing
uncommitted audit logs were not changed.

The independent reviewer found no Critical or Important issue.  Its sole
initial Minor finding was the source title in this document; the citation
above now uses the title published at arXiv:2607.09558v1.  The reviewer also
independently elaborated both modules, checked the linear-algebra declaration
types, ran `Print Assumptions` and `coqchk -silent`, and confirmed the C3-0
scope and absence of prohibited dependencies.
