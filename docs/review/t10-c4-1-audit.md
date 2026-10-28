# T10-C4-1 audit: finiteness of faces of a rational polyhedral cone

Baseline: `ca6483b6f33cd8dbc3c34f74f37b773ad22258fc`.

Scope: C4-1 only.  This task constructs a finite list covering every face up
to `SameSet`; it does not implement face stripping, a linear extension of the
face order, or a dimension theorem.

## Constructive sublist enumeration

`ListSubsequence selected source` records an order-preserving choice of list
positions.  The recursive function

```coq
all_sublists (head :: tail) =
  all_sublists tail ++ map (cons head) (all_sublists tail)
```

therefore keeps different occurrences of equal generators distinct.  The
following facts are constructive and closed under the global context:

```coq
all_sublists_complete :
  forall (A : Type) (source selected : list A),
    ListSubsequence selected source ->
    In selected (all_sublists source)

all_sublists_sound :
  forall (A : Type) (source selected : list A),
    In selected (all_sublists source) ->
    ListSubsequence selected source

all_sublists_contains_nil :
  forall (A : Type) (source : list A),
    In [] (all_sublists source)

all_sublists_contains_source :
  forall (A : Type) (source : list A),
    In source (all_sublists source)

all_sublists_length :
  forall (A : Type) (source : list A),
    length (all_sublists source) = 2 ^ length source
```

The duplicate-position regression computes
`all_sublists [1;1] = [[];[1];[1];[1;1]]`, so equal values do not collapse
the two position choices.

## Connection to C4-0

The filter used by `face_generator_filter` is proved to be a
`ListSubsequence`.  This yields:

```coq
face_has_sublist_generators :
  forall (d : nat) (generators : list (QVec d)) (face : QSet d),
    FaceOf (qcone_generated generators) face ->
    exists selected : list (QVec d),
      In selected (all_sublists generators) /\
      SameSet face (qcone_generated selected)
```

The proof also supplies `SameSet` reflexivity, symmetry and transitivity and
transport lemmas for replacing either the ambient cone or the face.  It uses
only pointwise equivalence and introduces no function extensionality.

## Finite face representatives and quantitative bound

For a fixed generator list, `polyhedral_face_candidates` maps every selected
sublist to its generated cone.  A Prop-level recursive selection retains only
candidates satisfying `FaceOf cone`.  The selection uses
`Classical_Prop.classic` to split each finite candidate; it does not provide
or claim a computable face decision procedure.

The bounded result is:

```coq
polyhedral_faces_finite_bounded :
  forall (d : nat) (cone : QSet d)
         (generators : list (QVec d)),
    SameSet cone (qcone_generated generators) ->
    exists faces : list (QSet d),
      length faces <= 2 ^ length generators /\
      (forall face, In face faces -> FaceOf cone face) /\
      (forall face, FaceOf cone face ->
        exists representative,
          In representative faces /\
          SameSet face representative)
```

Thus the number of external face classes is at most `2^m` for a chosen
presentation with `m` generators.  The list may still contain extensionally
equal representatives; no `NoDup` claim using Leibniz equality is made.

The required public result is:

```coq
polyhedral_faces_finite :
  forall (d : nat) (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists faces : list (QSet d),
      (forall face, In face faces -> FaceOf cone face) /\
      (forall face, FaceOf cone face ->
        exists representative,
          In representative faces /\
          SameSet face representative)
```

## Boundary regressions

The audit examples cover dimension zero, the zero cone, full space,
nonpointed cones and lineality, duplicated positions, zero generators, and a
redundant diagonal generator.  For the two-dimensional nonnegative quadrant:

- the whole cone, both nonnegative coordinate rays, and the zero cone are
  proved to be faces;
- every face is proved `SameSet` to one of those four;
- the four standard faces are proved pairwise distinct under `SameSet`;
- adding `(1,1)` as a redundant generator is proved not to add a new face.

The full-space regression separately proves that the zero cone is not a face
of `Q^2`, preventing the invalid assumption that every cone necessarily has
the zero face.

## Axiom boundary

- `all_sublists_complete`, `all_sublists_length`, and
  `face_has_sublist_generators`: `Closed under the global context`.
- `polyhedral_faces_finite_bounded` and `polyhedral_faces_finite` depend only
  on `Classical_Prop.classic`, introduced by the finite Prop-level filtering
  of candidates.
- No `ClassicalEpsilon.constructive_indefinite_description`, UIP/K,
  `Eq_rect_eq`, functional extensionality, `Admitted`, new `Axiom`, or oracle
  is present.

## C4-2 interface and remaining obligations

C4-2 may reuse the finite representative list, its soundness, its
`SameSet`-completeness, and the `2^m` bound.  Still missing, and deliberately
not proved in C4-1, are:

1. a `SameSet`-respecting inclusion relation on representatives and its
   finite-order/linear-extension construction;
2. the definition connecting a face to the rational span/dimension used by
   the paper;
3. a proof that a proper face has strictly smaller dimension, including the
   nonzero supporting functional on the ambient span;
4. handling extensionally duplicate representatives when an antisymmetric
   order or strict chain is required.

No part of the Face-Stripping Theorem is implemented here.

## Verification record

- RED: `FiniteFacesExamples.v` failed because `Mell.Geometry.FiniteFaces`
  did not yet exist.
- GREEN/focused: `make audit-t10-c4-1` succeeded.
- Kernel: `coqchk -silent` accepted `Mell.Geometry.FiniteFaces` and
  `Mell.Audit.FiniteFacesExamples`.
- A first independent review found that the initial quadrant regression
  established coverage but did not yet prove the four representatives
  pairwise distinct.  The regression was strengthened with
  `quadrant_standard_faces_pairwise_distinct`.
- Final focused audit: `make audit-t10-c4-1` succeeded, including the source
  trust scan and `coqchk -silent` for `Mell.Geometry.FiniteFaces` and
  `Mell.Audit.FiniteFacesExamples`.
- Final full regression: `make -f Makefile.coq -j2` succeeded (`Nothing to be
  done for real-all` after the focused rebuild).
- Follow-up independent review confirmed the correction and reported no
  remaining Critical, Important, or Minor findings.
