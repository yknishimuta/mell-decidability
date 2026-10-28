# T10-C4-3B-1-HRep-A2 audit

## Scope and baseline

- Baseline: `bf7bd5bc97eb1e4990f4bcffb7a6a0df471cf1de`.
- Scope: `Fin.t`/ordinal indices, `QVec`/MathComp `rat` row and column
  vectors, vector operations, finite linear combinations, inner products,
  coordinate order, and generator-list conversion.
- Coq-Polyhedra's installed `in_coneP` uses coefficients over
  `'cV[R]_n`; columns are therefore the primary representation. Rows are
  supplied as the transpose companion.
- Cone membership, finite-set conversion, H-representations, homogenization,
  and integer H-representations remain outside A2.

## Public index and vector API

```coq
fin_to_ord : forall {d}, Fin.t d -> 'I_d
ord_to_fin : forall {d}, 'I_d -> Fin.t d
fin_to_ordK : forall d (index : Fin.t d),
  ord_to_fin (fin_to_ord index) = index
ord_to_finK : forall d (index : 'I_d),
  fin_to_ord (ord_to_fin index) = index
fin_to_ord_val : forall d (index : Fin.t d),
  val (fin_to_ord index) = proj1_sig (Fin.to_nat index)
ord_to_fin_val : forall d (index : 'I_d),
  proj1_sig (Fin.to_nat (ord_to_fin index)) = val index

qvec_to_rat_col : forall {d}, QVec d -> 'cV[rat]_d
rat_col_to_qvec : forall {d}, 'cV[rat]_d -> QVec d
qvec_to_rat_row : forall {d}, QVec d -> 'rV[rat]_d
rat_row_to_qvec : forall {d}, 'rV[rat]_d -> QVec d

qvec_to_rat_col_eq_iff : forall d (left right : QVec d),
  qvec_to_rat_col left = qvec_to_rat_col right <-> QVecEq left right
qvec_to_rat_col_roundtrip : forall d (value : QVec d),
  QVecEq (rat_col_to_qvec (qvec_to_rat_col value)) value
rat_col_to_qvec_roundtrip : forall d (value : 'cV[rat]_d),
  qvec_to_rat_col (rat_col_to_qvec value) = value
qvec_to_rat_row_eq_iff : forall d (left right : QVec d),
  qvec_to_rat_row left = qvec_to_rat_row right <-> QVecEq left right
qvec_to_rat_row_roundtrip : forall d (value : QVec d),
  QVecEq (rat_row_to_qvec (qvec_to_rat_row value)) value
rat_row_to_qvec_roundtrip : forall d (value : 'rV[rat]_d),
  qvec_to_rat_row (rat_row_to_qvec value) = value
qvec_to_rat_row_transpose : forall d (value : QVec d),
  qvec_to_rat_row value = (qvec_to_rat_col value)^T
```

The coordinate lemmas state that column entry `[i,0]` and row entry `[0,i]`
are exactly `q_to_rat (value (ord_to_fin i))`. Standard vectors use `QVecEq`,
not Leibniz equality; matrix round trips use `matrixP` through `rowP`/`colP`.

## Operations and finite sums

```coq
qvec_to_rat_col_zero : forall d,
  qvec_to_rat_col (qvec_zero d) = 0
qvec_to_rat_col_add : forall d (left right : QVec d),
  qvec_to_rat_col (qvec_add left right) =
    qvec_to_rat_col left + qvec_to_rat_col right
qvec_to_rat_col_scale : forall d (scalar : Q) (value : QVec d),
  qvec_to_rat_col (qvec_scale scalar value) =
    q_to_rat scalar *: qvec_to_rat_col value
qvec_to_rat_col_opp : forall d (value : QVec d),
  qvec_to_rat_col (qvec_scale (-1) value) = - qvec_to_rat_col value
qvec_to_rat_col_sub : forall d (left right : QVec d),
  qvec_to_rat_col (qvec_add left (qvec_scale (-1) right)) =
    qvec_to_rat_col left - qvec_to_rat_col right
```

The row API contains the same five statements with `col` replaced by `row`.

```coq
rat_linear_combination : forall {d},
  list ('cV[rat]_d) -> list rat -> 'cV[rat]_d

qvec_to_rat_linear_combination : forall d
    (generators : list (QVec d)) (coefficients : list Q),
  length generators = length coefficients ->
  qvec_to_rat_col (qlinear_combination generators coefficients) =
    rat_linear_combination
      (List.map qvec_to_rat_col generators)
      (List.map q_to_rat coefficients)

q_to_rat_coefficients_nonnegative_iff : forall coefficients,
  List.Forall (fun coefficient : Q => Qle 0 coefficient) coefficients <->
  List.Forall (fun coefficient : rat =>
    is_true (((0 : rat) <= coefficient)%R))
    (List.map q_to_rat coefficients)

rat_linear_combination_to_qvec : forall d
    (generators : list ('cV[rat]_d)) (coefficients : list rat),
  length generators = length coefficients ->
  qvec_to_rat_col
    (qlinear_combination
      (List.map rat_col_to_qvec generators)
      (List.map rat_to_q coefficients)) =
  rat_linear_combination generators coefficients
```

`rat_linear_combination` follows the existing paired-list recursion exactly:
empty or exhausted input gives zero. The reverse theorem is the API needed to
reconstruct a standard `QVec` combination from future `in_coneP` witnesses.

## Inner product, order, and generator lists

```coq
q_to_rat_qinner : forall d (left right : QVec d),
  q_to_rat (qinner left right) =
    (qvec_to_rat_row left *m qvec_to_rat_col right) ord0 ord0
qvec_to_rat_col_nonnegative_iff : forall d
    (value : QVec d) (index : 'I_d),
  Qle 0 (value (ord_to_fin index)) <->
    is_true (((0 : rat) <= qvec_to_rat_col value index ord0)%R)
qinner_nonnegative_iff : forall d (left right : QVec d),
  Qle 0 (qinner left right) <->
    is_true (((0 : rat) <=
      (qvec_to_rat_row left *m qvec_to_rat_col right) ord0 ord0)%R)

rat_cols_of_list : forall {d}, list (QVec d) -> list ('cV[rat]_d)
rat_cols_of_list_surjective : forall d (values : list ('cV[rat]_d)),
  exists sources : list (QVec d), rat_cols_of_list sources = values
```

The installed `qdot` accepts `Vector.t Q`; the QVec-facing theorem therefore
uses the established `qinner`, which is definitionally `qdot` after
`qvec_to_vector`. The generator-list API also proves length, `nth_error`, nil,
cons, and duplicate preservation, plus single-column surjectivity.

## Proof ingredients and regression

The proofs reuse A0/A1 `q_to_rat_eq_iff`, both scalar round trips,
`q_to_rat_zero`, `q_to_rat_add`, `q_to_rat_mul`, and
`q_to_rat_nonnegative_iff`. MathComp ingredients are `rowP`, `colP`, `mxE`,
`trmx`, `big_ord0`, `big_ord_recl`, `eq_bigr`, and `scaleN1r`. Index proofs
reuse `Fin.to_nat`, `Fin.of_nat_lt`, `Fin.to_nat_inj`, `val_inj`, `lift`, and
the existing `ordinal_to_fin_lift`; no proof-irrelevance principle is used.

RED was observed first for each checkpoint: missing adapter module, missing
vector conversion API, missing operation API, missing finite-combination API,
and missing inner/list API. Focused GREEN covers dimensions 0, 1, and 2;
signed and zero vectors; large integer components; nonnormalized `1/2` and
`2/4`; empty, zero-coefficient, signed-coefficient, duplicate, dependent, and
rank-deficient generator lists; coefficient nonnegativity and a negative
coefficient; row/column transpose; and negative, zero, and positive inner
products. The dimension-zero matrix product uses MathComp's empty big sum.

## Verification and assumptions

The following commands exited zero:

```text
make OPAMEXEC= check-t10-c4-3b-1-hrep-a2
make OPAMEXEC= audit-t10-c4-3b-1-hrep-a2
make -f Makefile.coq -j2
```

The focused audit runs `coqchk -silent` on
`Mell.Geometry.QratVectorAdapter` and
`Mell.Audit.QratVectorAdapterExamples`. `Print Assumptions` was run for 37
public results; all 37 printed `Closed under the global context`. Source gates
found no `Admitted`, `Abort`, new `Axiom`, `Classical_Prop.classic`,
`ClassicalEpsilon`, UIP/K, `Eq_rect_eq`, functional extensionality,
constructive indefinite description, or external oracle.

## Independent review

An independent read-only review reported no Critical, Important, or Minor
findings. It checked the latest source in an external temporary build,
recompiled both A2 modules, reran `coqchk`, and confirmed all 37 assumption
reports were closed. It also confirmed the HRep-B scope boundary and judged
the change ready to commit.

## Boundary for HRep-B

HRep-B still owns conversion of generator lists to the finite-set format used
by Coq-Polyhedra, duplicate-insensitivity of the generated cone, use of
`in_coneP`, cone-membership equivalence, H-representations, homogenization,
and integer H-representations. None is implemented here.
