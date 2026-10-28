# T10-C4-3B-1-B3 audit

Baseline: `04e655952a9232f90c22e4c7aadba4554c0fbda2`.

Scope: Bizière–Leroux–Sutre Lemma 6.5, providing one period vector in a
face whose zero pattern agrees with every normal in a fixed finite list.
Corollary 6.7 (B4), Lemma 6.10, and the face-stripping theorem are not
implemented here.

## B3-0: reused interfaces

The implementation reuses `IntegerNormalOrthogonalToFace`,
`face_inactive_integer_normals`, `face_subset`, `face_is_cone`,
`qinner_add_right`, `qinner_scale_right`, `periodic_cone_positive_ray`,
and the B2 common-normal theorem.  `FacePeriod period face value` is the
conjunction of `period value` and `face (zvec_to_qvec value)`.

## B3-1: positive point for an inactive normal

```coq
inactive_supporting_normal_positive_on_face :
  forall d (cone face : QSet d) (normal : ZVec d),
    FaceOf cone face ->
    SupportingNormal cone (zvec_to_qvec normal) ->
    ~ IntegerNormalOrthogonalToFace face normal ->
    exists point : QVec d,
      face point /\ 0 < qinner (zvec_to_qvec normal) point
```

Classical propositional elimination supplies a face point where the inner
product is nonzero.  `face_subset` and support make it nonnegative, hence
strictly positive.

## B3-2: finite positive sum and exact zero pattern

`inactive_normals_positive_sum` inducts over the finite inactive list.
It adds one positive point for the head normal to the tail sum.  Every
other contribution is nonnegative because all normals support the cone
and every summand lies in the face.  Thus every inactive normal is
strictly positive on the common sum, including when normals are repeated.
For an empty inactive list the sum is `qvec_zero`.

`face_normals_zero_pattern_sum` obtains the inactive sublist from B2 and
proves, for the same face point and every normal in the original list,

```coq
IntegerNormalOrthogonalToFace face normal <->
qinner (zvec_to_qvec normal) sum == 0.
```

## B3-3: conversion to a period vector

`periodic_cone_positive_ray` writes the rational face point as a strictly
positive rational multiple of a period vector.  `face_positive_ray_reflect`
uses the finite supporting-normal definition of `FaceOf` to reflect face
membership through this positive scaling.  `qinner_positive_ray_zero_iff`
uses `qinner_scale_right` and the nonzero multiplier to transfer every
zero condition.

The main theorem is:

```coq
face_zero_pattern_witness :
  forall (d : nat) (period : ZSet d) (face : QSet d)
    (normals : list (ZVec d)),
  Periodic period ->
  FaceOf (Cone period) face ->
  List.Forall
    (fun normal =>
      SupportingNormal (Cone period) (zvec_to_qvec normal))
    normals ->
  exists witness : ZVec d,
    FacePeriod period face witness /\
    forall normal : ZVec d,
      List.In normal normals ->
      (IntegerNormalOrthogonalToFace face normal <->
       qinner (zvec_to_qvec normal) (zvec_to_qvec witness) == 0)
```

No `FullPeriodic`, finite-generation, or nonnegativity premise is added.

## B3 common-list corollary

`periodic_polyhedral_common_zero_pattern_normals` applies the main theorem
to the single list supplied by `polyhedral_common_integer_face_normals`.
The existential list precedes all face quantifiers and simultaneously
retains the integer H-representation, supporting property, reconstruction
of every face, and a zero-pattern witness for every face.

## Regression coverage

Focused examples cover dimension zero, the zero period, `N`, `2N`, `N^2`,
the signed lineality period, maximal and proper faces, empty normals,
duplicate and zero normals, and a non-normalized positive scalar `2/4`.
For `N^2`, explicit witnesses `(1,1)`, `(1,0)`, and `(0,0)` are checked
against the standard two normals for the full quadrant, first coordinate
axis, and origin respectively.

## Axiom audit

- `face_positive_ray_reflect` is closed under the global context.
- `inactive_supporting_normal_positive_on_face` uses
  `Classical_Prop.classic` only to extract a witness from failed universal
  orthogonality.
- `inactive_normals_positive_sum` inherits that dependency.
- `face_zero_pattern_witness` additionally inherits classical finite
  filtering from `face_inactive_integer_normals`.
- `periodic_polyhedral_common_zero_pattern_normals` also inherits the B2
  finite-face enumeration dependency.
- There is no `ClassicalEpsilon`, new `Axiom`, `Admitted`, `Abort`, UIP/K,
  functional extensionality, or external oracle.

## Independent review

An independent read-only review found no Critical, Important, or Minor
issues and returned `READY`.  It specifically checked duplicate inactive
normals, the empty-inactive base case, strict positivity of the scaling
coefficient, both `Qmult_integral` zero branches, the direction of the
`QVecEq` transport, the common-list quantifier order, axiom dependencies,
and the absence of B4 work.

## Deliberately remaining for B4

B4 must combine the common integer H-representation and the witness zero
pattern with `FullPeriodic`, convert the active/nonactive normal conditions
into B1 integer affine inequalities, treat rational inequality thresholds
by ceilings, and handle equality thresholds separately by an integrality
test.  It must then identify the homogeneous group solution set with the
appropriate `FacePeriod` without strengthening B3's hypotheses.
