# T10-C3-2A audit: uniform small coefficients

Date: 2026-10-21

Baseline: `94a99f6605f9cdad6237c1dff2e332f1a6298b3e`

Scope: C3-2A only. This unit isolates equation (1) used in the proof of
Bizière--Leroux--Sutre (2026), Lemma 4.9. It does not begin C3-2B.

## Public theorem

With `Set Printing Implicit`, the final theorem is:

```coq
qspan_uniform_small_coefficients
     : forall (d : nat) (generators : list (ZVec d))
         (positive : Vector.t Q (List.length generators)),
       Vector.Forall (fun coefficient : Q => 0 < coefficient) positive ->
       exists epsilon : Q,
         0 < epsilon /\
         (forall w : QVec d,
          QSpan generators w ->
          (forall index : Fin.t d, - epsilon < w index < epsilon) ->
          exists delta : Vector.t Q (List.length generators),
            QVecEq w (qgroup_combination generators delta) /\
            (forall index : Fin.t (List.length generators),
             - Vector.nth positive index < Vector.nth delta index /\
             Vector.nth delta index < Vector.nth positive index))
```

The same `epsilon` works for every sufficiently small `w`. Bounds on every
coefficient are strict. The theorem assumes neither independence nor
nonzeroness and treats repeated list occurrences separately.

## Construction

The proof uses an equivalent finite-dimensional construction that avoids a
new Gaussian-elimination library.

1. `signed_coordinate_generators d` contains the positive and negative unit
   vectors. Every rational vector has a canonical nonnegative representation
   in this cone, and the sum of its coefficients is its coordinate `L1` norm.
2. The equation connecting a source coefficient vector `z` to those signed
   coordinates is expressed by the existing pullback H-matrix. C1-HL's
   `rational_hcone_finitely_generated` gives one fixed finite ray list for
   this homogeneous cone.
3. Rays whose signed-coordinate projection has zero `L1` mass are kernel
   rays. Their coefficients are set to zero. This preserves the represented
   `w` while removing unbounded kernel motion.
4. For each retained ray, the source-coordinate `L1` mass divided by its
   positive signed-coordinate mass is finite. `lifted_global_bound` is the
   sum of those finitely many ratios and uniformly bounds the retained source
   coefficients by the `L1` norm of `w`.
5. `qvector_min positive` is strictly positive. The proof takes

   ```text
   epsilon = min(positive) /
             (1 + (d + 1) * lifted_global_bound).
   ```

   Coordinate smallness bounds the `L1` norm by `(d+1)*epsilon`, so every
   reconstructed coefficient has absolute value strictly below its
   corresponding requested bound.

All numerical identities use `Qeq`; no Leibniz equality of noncanonical
rational representations is assumed.

## Main supporting lemmas

- exact signed-coordinate reconstruction and coefficient-sum lemmas;
- nonnegative `qlinear_combination` projection and `L1`-mass lemmas;
- kernel-ray pruning and preservation of the right projection;
- `pruned_left_weight_bound`, the finite-ray uniform operator bound;
- `qvector_min_positive` and `qvector_min_le_nth`;
- `qvec_abs_sum_small`, including dimension zero;
- the existing `pullback_matrix_constraints`,
  `qcone_generated_aligned_coefficients`, and
  `rational_hcone_finitely_generated`.

## Regression boundary

The audit examples cover dimension zero, an empty list in positive dimension,
a zero generator, `[1;-1]`, a rank-one system in dimension two, duplicates
with more generators than the ambient dimension, a very small positive bound,
a numerically noncanonical positive rational, and an explicit negative
direction in the span.

RED was observed before implementation: the audit module failed because
`Mell.Geometry.SpanPerturbation` did not exist.

## C3-2B handoff

C3-2B remains separate. Its planned connection is:

1. obtain a strictly positive spanning list from `center_characterization`;
2. split `ClosedLinearization P q` into `Difference P q` and
   `QClosure (Cone P) (zvec_to_qvec q)`;
3. choose a nearby `x` in `Cone P` and put `w = q - x`;
4. use `q in Difference P` and `x in Cone P` to prove `w in VecOf P`;
5. apply this unit's theorem so the coefficients of `v+w` remain positive;
6. add the nonnegative cone coefficients of `x` to obtain a positive
   representation of `v+q`.

Because `q in Difference P` supplies the required span fact, C3-2B need not
formalize the general theorem that every finite-dimensional rational
subspace is topologically closed.

## Trust boundary and verification record

The theorem inherits `Classical_Prop.classic` from C1-HL's existing finite
H-cone generation theorem. It introduces no additional axiom. In particular,
there is no ClassicalEpsilon, UIP/K, `Eq_rect_eq`, functional extensionality,
choice oracle, or admitted result.

Final verification:

- `make CORE_LOG_DIR=/tmp/mell-c3-2a-logs audit-t10-c3-2a`
  (exit 0): focused build, full public type and `Print Assumptions`, forbidden
  dependency scans, and `coqchk -silent` for both changed Coq modules.
- `make CORE_LOG_DIR=/tmp/mell-c3-2a-regression check-t10-c3-1a
  check-t10-c3-1b` (exit 0): the two immediately preceding stages.
- `opam exec --switch . -- make -f Makefile.coq -j2` (exit 0): complete Coq
  regression build.
- target-file `git diff --check` and forbidden-token scan (exit 0).

The independent reviewer returned **Ready**, with zero critical, important,
or minor findings. The reviewer separately checked the theorem's quantifier
order and uniformity, all strict coordinate bounds, the dependent/zero/
duplicate cases, the non-circular finite-ray construction, the examples,
`Print Assumptions`, and `coqchk -silent`.
