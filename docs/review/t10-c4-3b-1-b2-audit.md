# T10-C4-3B-1-B2 audit

Baseline: `53d321f9c22fae7b4ecf7b0b23afef7bbce487a0`.

Scope: the common finite integer supporting-normal list corresponding to
Section 6, equation (2), and the following face characterization.  Lemma 6.5
(B3) and Corollary 6.7 (B4) are not implemented here.

## B2-0: reused interfaces

`FaceOf cone face` already exposes a finite rational-normal list:

```coq
exists normals : list (QVec d),
  List.Forall (SupportingNormal cone) normals /\
  SameSet face
    (fun point => cone point /\ NormalOrthogonal normals point)
```

The implementation reuses:

- `qnormal_clear_denominators`, `qnormal_integer_inner`, and
  `qnormal_integer_nonnegative_iff` from HRep-D;
- `polyhedral_cone_integer_hrep` for the cone H-representation;
- `polyhedral_faces_finite` for a finite list representing every face up to
  `SameSet`;
- `same_set_trans`, `face_of_cone_ext`, and `face_of_face_ext` for
  extensional transport;
- `face_self` and `face_subset` for the maximal face and forward inclusion.

`polyhedral_faces_linearized` was also type-audited.  It additionally
orders extensionally distinct representatives with the whole cone first,
but B2 needs neither that order nor deduplication, so the smaller
`polyhedral_faces_finite` interface is used.

No new V-to-H conversion is introduced.

## B2-1: integer witness for one face

The predicate is:

```coq
IntegerNormalOrthogonalToFace face normal :=
  forall point, face point ->
    qinner (zvec_to_qvec normal) point == 0
```

For every rational supporting normal `normal`,
`qnormal_clear_denominators` returns a `positive` multiplier and integer
normal.  The following bridges preserve its meaning:

```coq
qnormal_integer_supporting :
  coordinates(integer_normal) == multiplier * coordinates(normal) ->
  SupportingNormal cone normal ->
  SupportingNormal cone (zvec_to_qvec integer_normal)

qnormal_integer_zero_iff :
  coordinates(integer_normal) == multiplier * coordinates(normal) ->
  forall point,
    qinner normal point == 0 <->
    qinner (zvec_to_qvec integer_normal) point == 0
```

The second proof uses `qnormal_integer_inner` and the fact that
`inject_Z (Z.pos multiplier)` is nonzero.  Thus no zero or negative scaling
is admitted.

The public per-face theorem is:

```coq
integer_face_witness :
  forall (d : nat) (cone face : QSet d),
    FaceOf cone face ->
    exists normals : list (ZVec d),
      (forall normal,
        List.In normal normals ->
        SupportingNormal cone (zvec_to_qvec normal)) /\
      SameSet face
        (fun point =>
          cone point /\
          forall normal,
            List.In normal normals ->
            qinner (zvec_to_qvec normal) point == 0)
```

## B2-2: finite aggregation over face representatives

`polyhedral_faces_finite` supplies a finite representative list.  The proof
first applies `integer_face_witness` to each representative and concatenates
the resulting lists by ordinary list induction.  It records both:

- every aggregate normal supports the original cone; and
- each representative's witness list is included in the aggregate.

For an arbitrary face, its `SameSet` representative transports the witness
characterization.  Only finitely many existential witnesses are destructed;
there is no choice function or `ClassicalEpsilon`.

## B2-3: construction of the common list

Let:

- `E_H` be the list returned by `polyhedral_cone_integer_hrep`; and
- `E_F` be the concatenation of the integer witnesses for the finite face
  representatives.

The common list is `E_H ++ E_F`.

`E_H` gives the reverse implication of the cone H-representation.  Every
normal in both lists is supporting, so a point of the cone satisfies every
inequality in the appended list.  For a face `F`, its original witness list
is contained in `E_F`.  Additional common-list normals that are orthogonal
to all of `F` cannot remove a point of `F`; conversely the retained witness
normals prevent the reconstructed set from being larger than `F`.

The resulting public theorem is:

```coq
polyhedral_common_integer_face_normals :
  forall (d : nat) (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists normals : list (ZVec d),
      (forall point : QVec d,
        cone point <->
        forall normal,
          List.In normal normals ->
          0 <= qinner (zvec_to_qvec normal) point) /\
      (forall normal,
        List.In normal normals ->
        SupportingNormal cone (zvec_to_qvec normal)) /\
      (forall face : QSet d,
        FaceOf cone face ->
        SameSet face
          (fun point =>
            cone point /\
            forall normal,
              List.In normal normals ->
              IntegerNormalOrthogonalToFace face normal ->
              qinner (zvec_to_qvec normal) point == 0))
```

The existential list precedes the universal face quantifier, so the same
`E` is used simultaneously for every face.

## B2-4: active and inactive finite lists

Finite induction with `Classical_Prop.classic` on the proposition
`IntegerNormalOrthogonalToFace face normal` yields:

```coq
face_active_integer_normals :
  forall d E F,
    exists active,
      forall e,
        List.In e active <->
        List.In e E /\ IntegerNormalOrthogonalToFace F e

face_inactive_integer_normals :
  forall d E F,
    exists inactive,
      forall e,
        List.In e inactive <->
        List.In e E /\ ~ IntegerNormalOrthogonalToFace F e
```

No computable decision procedure for face orthogonality is postulated.

## Regression coverage

The focused examples cover dimension zero, the zero cone, full space, the
two-dimensional nonnegative orthant and both coordinate rays, minimal and
maximal faces, a nonpointed lineality cone, a low-rank ray, redundant
generators, empty/zero/duplicate normal lists, extensionally equal `QSet`
representatives, and numerically equal non-normalized `QVec` coordinates.

For the orthant, one witness list from
`polyhedral_common_integer_face_normals` is used to reconstruct all four
standard faces: the cone, each coordinate ray, and the zero face.  The
lineality regression only exercises the maximal face; it does not assume
that the zero cone is a face of a cone with lineality.

## Axiom audit

- `qnormal_integer_supporting`, `qnormal_integer_zero_iff`, and
  `integer_face_witness` are closed under the global context.
- `polyhedral_common_integer_face_normals` inherits
  `Classical_Prop.classic` from `polyhedral_faces_finite`.
- `face_active_integer_normals` and `face_inactive_integer_normals` use
  `Classical_Prop.classic` only to select a finite propositional sublist.
- No `ClassicalEpsilon`, `Admitted`, `Abort`, new `Axiom`, UIP/K,
  functional extensionality, or external oracle is used.

## Obligations deliberately left for B3 and B4

B3 must use the finite common list `E` and construct `q in Q cap F` whose
zero pattern is exactly the active list.  The missing ingredients are a
finite sum/interior-point construction for the active constraints and a
strictly positive witness for every nonactive normal; neither is proved in
B2.

B4 must turn `E` into the integer constraint list accepted by B1, combine
it with `FullPeriodic Q` and the finite generation of `Difference Q`, handle
rational inequality thresholds by integer ceilings, and handle equality
thresholds separately by an integrality test.  It must then identify the
homogeneous group solution set with `FacePeriod Q F`.
