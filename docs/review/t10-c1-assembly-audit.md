# T10-C1 Assembly audit

Baseline: `eb07e699b5bad3043b3e2f8a9c3a05446b82d4fd`

Scope: C1-Assembly only.  No C1-QE2 public declaration was changed and no
T10-C2 work was started.

## Mathematical construction

- `qterm_homogeneous_row` represents every rational affine term on the
  homogenized coordinates `(t,x)`.  Variables outside the `d` natural
  coordinates retain the existing `qvec_environment` value `0`; constants are
  multiplied by `t`.
- `homogenized_cell_matrix` contains `t >= 0`, two weak rows for equality,
  one weak row for a weak inequality, and one weak row for an originally
  strict inequality.  `cell_homogenization_correct` proves its exact effect.
- `weak_cell_with_witness_normalizes` uses a genuine point of the cell and
  `epsilon > 0` to recover strict inequalities at
  `(x + epsilon*y0)/(t + epsilon)`.  No integer-style successor rewrite is
  used.
- `homogenized_cell_projection_closed` scales the normalized point by
  `t + epsilon` and uses `QClosure` with
  `epsilon = delta/(1 + sum_i |y0_i|)`.  This includes `t = 0` and dimension
  zero.
- `nonempty_cell_finitely_generated_in_cone` applies
  `rational_hcone_finitely_generated`, projects every generator from
  dimension `S d` to `d`, and proves both generator soundness and cell
  coverage.
- `finite_cells_generators` folds the finite list supplied by
  `qdefinable_finite_cells`.  It uses propositional classical case analysis
  only to skip empty cells; no choice operator or executable oracle is used.
- `rational_closed_cone_finitely_generated` combines coverage with
  `qdefinable_qvec_extensional` and the `IsCone` operations.

## Public theorem

With `Set Printing Implicit`:

```coq
rational_closed_cone_finitely_generated
     : forall (d : nat) (C : QSet d),
       @QDefinable d C ->
       @IsCone d C ->
       @TopologicallyClosed d C ->
       exists generators : list (QVec d),
         @SameSet (QVec d) C (@qcone_generated d generators)
```

The premise and conclusion are identical to the T10-P contract.

## Principal bridge types

```coq
cell_homogenization_correct
     : forall (d : nat) (cell : QAffineConjunction) (t : Q) (x : QVec d),
       @HConicalConstraints (qcell_homogenized_rows d cell)
         (S d) (homogenized_cell_matrix d cell) (@qvec_cons d t x) <->
       0 <= t /\ weak_homogenized_cell d t x cell

homogenized_cell_projection_closed
     : forall (d : nat) (C : QSet d) (cell : QAffineConjunction)
         (witness : QVec d) (t : Q) (x : QVec d),
       @IsCone d C ->
       @TopologicallyClosed d C ->
       (forall y : QVec d,
          qconjunction_semantics (@qvec_environment d y) cell -> C y) ->
       qconjunction_semantics (@qvec_environment d witness) cell ->
       @HConicalConstraints (qcell_homogenized_rows d cell)
         (S d) (homogenized_cell_matrix d cell) (@qvec_cons d t x) ->
       C x
```

The audit module also prints the complete types of
`normalized_cell_term_correct`, `weak_cell_with_witness_normalizes`,
`homogenized_cell_contains_one`, `qcone_generated_tail`,
`nonempty_cell_finitely_generated_in_cone`, and `finite_cells_generators`.

## Regression coverage

The focused examples prove:

- dimension zero and full space;
- the one-dimensional zero cone;
- the two-dimensional half-space `y >= 0`, including x-axis lineality;
- duplicated cells and redundant constraints;
- the cell `0 > 0` is empty while its weak homogenization at `t = 0` contains
  a nonzero projected point outside the zero cone, documenting why empty cells
  must be skipped;
- `{0} union {(x,y) | x>0 and y>0}` is an `IsCone` but is not
  `TopologicallyClosed`, so the closedness premise is materially necessary.

## Verification and trust boundary

- RED: before implementation, compiling
  `theories/Audit/RationalConeAssemblyExamples.v` failed because
  `Mell.Geometry.RationalConeAssembly` did not exist.
- GREEN: `make audit-t10-c1-assembly` exits 0.
- Whole-project regression: `opam exec --switch . -- make -f Makefile.coq -j2`
  exits 0.
- Kernel: the audit target runs `coqchk -silent` for
  `Mell.Geometry.RationalConeAssembly` and
  `Mell.Audit.RationalConeAssemblyExamples`; exit 0.
- Forbidden-declaration scan: no `Admitted`, `Axiom`, or `Abort` in the two
  C1-Assembly files; no UIP/K, `Eq_rect_eq`, functional extensionality,
  `constructive_indefinite_description`, or external oracle dependency.

`Print Assumptions` reports:

```text
cell_homogenization_correct: Closed under the global context
weak_cell_with_witness_normalizes: Closed under the global context
homogenized_cell_projection_closed: Closed under the global context
nonempty_cell_finitely_generated_in_cone: Classical_Prop.classic
finite_cells_generators: Classical_Prop.classic
rational_closed_cone_finitely_generated: Classical_Prop.classic
```

The sole remaining axiom is exactly the permitted propositional case split:

```text
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

No general choice principle is used.

## Independent review

An independent fresh-context review replayed both source files with `coqtop`
and checked both compiled modules with `coqchk`; all commands exited 0.  The
review found no defect in the proof or trust boundary.  It requested one
important regression improvement: the empty-cell example originally used the
zero projection, which belongs to every cone.  The example now exhibits a
nonzero projected point outside the zero cone, so it detects the spurious
enlargement caused by homogenizing an empty strict cell without filtering it.
