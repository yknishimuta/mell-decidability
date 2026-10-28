# T10-C4-3C1B geometric-core audit

## Scope

This checkpoint implements only the geometric core needed before the final
Lemma 6.10 assembly.  It does not prove the final `afs`/finite-basis statement,
Lemma 6.11, or the face-stripping theorem.

The implementation is in
`theories/Geometry/FaceStrippingGeometricCore.v`; focused regression and
assumption output are in
`theories/Audit/FaceStrippingGeometricCoreExamples.v`.

## Prepared-chain interface

`maximal_extract_prepared_chain_face_collapse` consumes an already reindexed
chain.  Its hypotheses explicitly retain:

- `period (sequence 0)`, so `PeriodicLe` is not incorrectly used as an
  endpoint-membership assertion;
- every `sequence n` lies in `ExtractFace ... face ...`;
- adjacent `PeriodicLe period` monotonicity;
- a finite list `unbounded` whose members are normals from `normals` with
  `NormalTailUnbounded` inner-product sequences;
- constancy from the reindexed zeroth term for every normal outside
  `unbounded`.

`finite_supporting_normals_prepared_reindex` is the explicit C4-3C1A bridge.
It consumes `finite_supporting_normals_tail_reindex`, uses the per-normal
dichotomy to show that every normal outside `unbounded` is in the returned
constant class, and exposes exactly the hypotheses above for
`tail_reindex sequence N`.  The threshold below therefore uses the reindexed
`sequence 0`, never the original sequence's zeroth term.

## K, H, and S

The proof constructs:

- `active`, the sublist of `normals` orthogonal to the whole maximal face;
- `tight = normal_list_difference active unbounded`, hence `K = L \\ U`;
- `larger = ThresholdFace (Cone period) tight`;
- `prepared_threshold sequence e = inject_Z (zinner e (sequence 0))`;
- `slice = RationalThresholdSlice period normals tight
  (prepared_threshold sequence)`.

`normal_list_difference_spec` proves both the exact `L \\ U` membership law and
`tight`'s inclusion in `normals`.  `threshold_face_is_face` proves that
`larger` is a face.  Orthogonality of every tight normal proves
`FaceSubset face larger`.  `corollary_6_7_finitary` then gives
`FinitaryQCylindric (FacePeriod period larger) slice`.

Supporting-normal monotonicity and the prepared constancy hypothesis prove
`forall n, slice (sequence n)`.

## Finite simultaneous choices

`simultaneous_unbounded_normals_threshold` takes an arbitrary lower index and
integer-vector bound.  It chooses one index for every member of a finite normal
list by induction and `Nat.max`; monotonicity transports every individually
reached bound to the common index.  The empty and duplicate-list cases are
covered by focused regression.

`inactive_normals_uniform_nsmul` takes a witness having strictly positive
integer inner product with every inactive normal.  For one normal it uses
`Z.to_nat (Z.max 0 (- zinner normal base))`; the finite-list construction takes
the maximum of these natural multipliers.  Strict integer positivity supplies
the lower bound one.  The empty inactive list permits multiplier zero.

## Corrected remainder and FullPeriodic

For a face-period increment `p`, a common unbounded index `n`, the B3
zero-pattern witness `q`, and the common multiplier `m`, the proof defines

`r = s_n - s_0 - p + m q`.

The common integer H-representation is checked normal-by-normal:

- active and unbounded: the simultaneous index supplies the lower bound and
  the B3 witness has zero inner product;
- active and not unbounded (the tight list): constancy, membership in `H`, and
  face orthogonality make the inner product exactly zero;
- inactive: `inactive_normals_uniform_nsmul` supplies nonnegativity.

Thus `r` is in `Cone period`.  Separately,
`s_n - s_0` is in `period` by the monotone chain, `m q` is in `period`, and
`p` is in `period`, so the exact difference identity proves
`r` is in `Difference period`.  Only then does
`full_periodic_member_iff_difference_cone` yield `period r`.

The exact balance

`s_n + m q = (s_0 + p) + r`

transports a hypothetical excluded point using cylindricity and contradicts
the original extraction property at `s_n`.  Therefore `s_0` belongs to the
extract set for `larger`; maximality finally gives `SameSet face larger`.

No second infinite subsequence is used before this face collapse.  It may be
extracted after transporting `FacePeriod period larger` along the resulting
`SameSet`, which is intentionally left for C4-3C2.

## Dependencies and assumptions

The proof reuses `integer_hrep_normals_supporting`,
`face_active_integer_normals`, `face_inactive_integer_normals`,
`face_zero_pattern_witness`, `corollary_6_7_finitary`,
`supporting_normal_monotone_sequence`, `periodic_le_sequence`, and
`full_periodic_member_iff_difference_cone`.

`Print Assumptions` reports:

- `simultaneous_unbounded_normals_threshold`: closed under the global context;
- `inactive_normals_uniform_nsmul`: closed under the global context;
- `finite_supporting_normals_prepared_reindex`:
  `Classical_Prop.classic` only (inherited from C1A's finite classification);
- `maximal_extract_prepared_chain_face_collapse`:
  `Classical_Prop.classic` only.

The classical dependency comes from finite proposition-level active/inactive
normal selection and the explicit finite case splits.  No choice axiom,
`ClassicalEpsilon`, functional extensionality, UIP/K, `Eq_rect_eq`, new axiom,
or admitted proof is used.

## Verification

- RED: the focused audit initially contained `Fail Check` commands for the
  three absent public declarations.
- GREEN: the source module and focused audit compile directly and through the
  generated `Makefile.coq` targets.
- Focused examples cover empty and duplicate unbounded lists, `K=L` (`U` is
  empty), `K` empty (all active normals are in `U`), empty and singleton
  inactive lists, a common correction multiplier, exact remainder balancing,
  and dimension zero.  The generic generated-period chain regression covers
  the already audited `{0}`, `N`, `2N`, `N²`, `Z`, low-rank, lineality,
  duplicate-generator, zero-generator, and empty-generator instances.
- The complete `_CoqProject` regression reports no pending or failing target.
- `coqchk -silent -Q theories Mell` succeeds for both the source and audit
  modules.
- The prohibited-token scan and target-scoped `git diff --check` succeed.

## C4-3C2 obligations left open

- instantiate this prepared-chain theorem from the first C1A monotone
  subsequence and tail classification;
- transport the finite cylindric period from `H` to `F` using `SameSet F H`;
- perform the second monotone-subsequence extraction only after that transport;
- assemble the final Lemma 6.10 `afs`/finite-basis conclusion.
