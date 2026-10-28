From Coq Require Import Fin List QArith Vector.
From mathcomp Require Import all_ssreflect all_algebra.
From Mell.Geometry Require Import Faces LatticeGordanV MathCompBridge
  QConeCore QcLinearAlgebra QratAdapter RationalHToV.

Import GRing.Theory Num.Theory.
Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Definition fin_to_ord {d} (index : Fin.t d) : 'I_d :=
  fin_to_ordinal index.

Definition ord_to_fin {d} (index : 'I_d) : Fin.t d :=
  ordinal_to_fin index.

Lemma fin_to_ordK : forall d (index : Fin.t d),
    ord_to_fin (fin_to_ord index) = index.
Proof. exact fin_to_ordinalK. Qed.

Lemma ord_to_finK : forall d (index : 'I_d),
    fin_to_ord (ord_to_fin index) = index.
Proof. exact ordinal_to_finK. Qed.

Lemma fin_to_ord_val : forall d (index : Fin.t d),
    val (fin_to_ord index) = proj1_sig (Fin.to_nat index).
Proof. reflexivity. Qed.

Lemma ord_to_fin_val : forall d (index : 'I_d),
    proj1_sig (Fin.to_nat (ord_to_fin index)) = val index.
Proof.
  intros d [index Hindex]. unfold ord_to_fin, ordinal_to_fin. cbn.
  now rewrite Fin.to_nat_of_nat.
Qed.

Definition qvec_to_rat_col {d} (value : QVec d) : 'cV[rat]_d :=
  \col_index q_to_rat (value (ord_to_fin index)).

Definition rat_col_to_qvec {d} (value : 'cV[rat]_d) : QVec d :=
  fun index => rat_to_q (value (fin_to_ord index) ord0).

Definition qvec_to_rat_row {d} (value : QVec d) : 'rV[rat]_d :=
  \row_index q_to_rat (value (ord_to_fin index)).

Definition rat_row_to_qvec {d} (value : 'rV[rat]_d) : QVec d :=
  fun index => rat_to_q (value ord0 (fin_to_ord index)).

Lemma qvec_to_rat_col_entry : forall d (value : QVec d) (index : 'I_d),
    qvec_to_rat_col value index ord0 =
      q_to_rat (value (ord_to_fin index)).
Proof. intros d value index. by rewrite /qvec_to_rat_col mxE. Qed.

Lemma qvec_to_rat_row_entry : forall d (value : QVec d) (index : 'I_d),
    qvec_to_rat_row value ord0 index =
      q_to_rat (value (ord_to_fin index)).
Proof. intros d value index. by rewrite /qvec_to_rat_row mxE. Qed.

Theorem qvec_to_rat_col_eq_iff : forall d (left right : QVec d),
    qvec_to_rat_col left = qvec_to_rat_col right <-> QVecEq left right.
Proof.
  intros d left right. split.
  - intro Heq. intro index.
    have Hentry := congr1 (fun value : 'cV[rat]_d =>
      value (fin_to_ord index) ord0) Heq.
    rewrite !qvec_to_rat_col_entry fin_to_ordK in Hentry.
    apply (proj1 (q_to_rat_eq_iff _ _)). exact Hentry.
  - intro Heq. apply/colP=> index.
    rewrite !qvec_to_rat_col_entry.
    apply (proj2 (q_to_rat_eq_iff _ _)), Heq.
Qed.

Theorem qvec_to_rat_col_roundtrip : forall d (value : QVec d),
    QVecEq (rat_col_to_qvec (qvec_to_rat_col value)) value.
Proof.
  intros d value index. unfold rat_col_to_qvec.
  rewrite qvec_to_rat_col_entry fin_to_ordK.
  apply q_to_rat_to_q.
Qed.

Theorem rat_col_to_qvec_roundtrip : forall d (value : 'cV[rat]_d),
    qvec_to_rat_col (rat_col_to_qvec value) = value.
Proof.
  intros d value. apply/colP=> index.
  rewrite qvec_to_rat_col_entry /rat_col_to_qvec ord_to_finK.
  apply rat_to_q_to_rat.
Qed.

Theorem qvec_to_rat_row_eq_iff : forall d (left right : QVec d),
    qvec_to_rat_row left = qvec_to_rat_row right <-> QVecEq left right.
Proof.
  intros d left right. split.
  - intro Heq. intro index.
    have Hentry := congr1 (fun value : 'rV[rat]_d =>
      value ord0 (fin_to_ord index)) Heq.
    rewrite !qvec_to_rat_row_entry fin_to_ordK in Hentry.
    apply (proj1 (q_to_rat_eq_iff _ _)). exact Hentry.
  - intro Heq. apply/rowP=> index.
    rewrite !qvec_to_rat_row_entry.
    apply (proj2 (q_to_rat_eq_iff _ _)), Heq.
Qed.

Theorem qvec_to_rat_row_roundtrip : forall d (value : QVec d),
    QVecEq (rat_row_to_qvec (qvec_to_rat_row value)) value.
Proof.
  intros d value index. unfold rat_row_to_qvec.
  rewrite qvec_to_rat_row_entry fin_to_ordK.
  apply q_to_rat_to_q.
Qed.

Theorem rat_row_to_qvec_roundtrip : forall d (value : 'rV[rat]_d),
    qvec_to_rat_row (rat_row_to_qvec value) = value.
Proof.
  intros d value. apply/rowP=> index.
  rewrite qvec_to_rat_row_entry /rat_row_to_qvec ord_to_finK.
  apply rat_to_q_to_rat.
Qed.

Lemma qvec_to_rat_row_transpose : forall d (value : QVec d),
    qvec_to_rat_row value = (qvec_to_rat_col value)^T.
Proof.
  intros d value. apply/rowP=> index.
  rewrite qvec_to_rat_row_entry mxE qvec_to_rat_col_entry. reflexivity.
Qed.

Theorem qvec_to_rat_col_zero : forall d,
    qvec_to_rat_col (qvec_zero d) = 0.
Proof.
  intros d. apply/colP=> index.
  rewrite qvec_to_rat_col_entry mxE /qvec_zero q_to_rat_zero.
  reflexivity.
Qed.

Theorem qvec_to_rat_col_add : forall d (left right : QVec d),
    qvec_to_rat_col (qvec_add left right) =
      qvec_to_rat_col left + qvec_to_rat_col right.
Proof.
  intros d left right. apply/colP=> index.
  rewrite qvec_to_rat_col_entry !mxE /qvec_add q_to_rat_add.
  reflexivity.
Qed.

Theorem qvec_to_rat_col_scale : forall d (scalar : Q) (value : QVec d),
    qvec_to_rat_col (qvec_scale scalar value) =
      q_to_rat scalar *: qvec_to_rat_col value.
Proof.
  intros d scalar value. apply/colP=> index.
  rewrite qvec_to_rat_col_entry !mxE /qvec_scale q_to_rat_mul.
  reflexivity.
Qed.

Theorem qvec_to_rat_col_opp : forall d (value : QVec d),
    qvec_to_rat_col (qvec_scale (-1) value) = - qvec_to_rat_col value.
Proof.
  intros d value. rewrite qvec_to_rat_col_scale.
  change (((-1 : rat) *: qvec_to_rat_col value) = - qvec_to_rat_col value).
  apply scaleN1r.
Qed.

Theorem qvec_to_rat_col_sub : forall d (left right : QVec d),
    qvec_to_rat_col (qvec_add left (qvec_scale (-1) right)) =
      qvec_to_rat_col left - qvec_to_rat_col right.
Proof. intros d left right. by rewrite qvec_to_rat_col_add qvec_to_rat_col_opp. Qed.

Theorem qvec_to_rat_row_zero : forall d,
    qvec_to_rat_row (qvec_zero d) = 0.
Proof.
  intros d. apply/rowP=> index.
  rewrite qvec_to_rat_row_entry mxE /qvec_zero q_to_rat_zero.
  reflexivity.
Qed.

Theorem qvec_to_rat_row_add : forall d (left right : QVec d),
    qvec_to_rat_row (qvec_add left right) =
      qvec_to_rat_row left + qvec_to_rat_row right.
Proof.
  intros d left right. apply/rowP=> index.
  rewrite qvec_to_rat_row_entry !mxE /qvec_add q_to_rat_add.
  reflexivity.
Qed.

Theorem qvec_to_rat_row_scale : forall d (scalar : Q) (value : QVec d),
    qvec_to_rat_row (qvec_scale scalar value) =
      q_to_rat scalar *: qvec_to_rat_row value.
Proof.
  intros d scalar value. apply/rowP=> index.
  rewrite qvec_to_rat_row_entry !mxE /qvec_scale q_to_rat_mul.
  reflexivity.
Qed.

Theorem qvec_to_rat_row_opp : forall d (value : QVec d),
    qvec_to_rat_row (qvec_scale (-1) value) = - qvec_to_rat_row value.
Proof.
  intros d value. rewrite qvec_to_rat_row_scale.
  change (((-1 : rat) *: qvec_to_rat_row value) = - qvec_to_rat_row value).
  apply scaleN1r.
Qed.

Theorem qvec_to_rat_row_sub : forall d (left right : QVec d),
    qvec_to_rat_row (qvec_add left (qvec_scale (-1) right)) =
      qvec_to_rat_row left - qvec_to_rat_row right.
Proof. intros d left right. by rewrite qvec_to_rat_row_add qvec_to_rat_row_opp. Qed.

Fixpoint rat_linear_combination {d}
    (generators : list ('cV[rat]_d)) (coefficients : list rat) :
    'cV[rat]_d :=
  match generators, coefficients with
  | generator :: generators', coefficient :: coefficients' =>
      coefficient *: generator +
        rat_linear_combination generators' coefficients'
  | _, _ => 0
  end.

Lemma qvec_to_rat_linear_combination_unconditional : forall d
    (generators : list (QVec d)) (coefficients : list Q),
    qvec_to_rat_col (qlinear_combination generators coefficients) =
      rat_linear_combination
        (List.map qvec_to_rat_col generators)
        (List.map q_to_rat coefficients).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros [|coefficient coefficients]; simpl;
    try apply qvec_to_rat_col_zero.
  rewrite qvec_to_rat_col_add qvec_to_rat_col_scale IH. reflexivity.
Qed.

Theorem qvec_to_rat_linear_combination : forall d
    (generators : list (QVec d)) (coefficients : list Q),
    List.length generators = List.length coefficients ->
    qvec_to_rat_col (qlinear_combination generators coefficients) =
      rat_linear_combination
        (List.map qvec_to_rat_col generators)
        (List.map q_to_rat coefficients).
Proof.
  intros d generators coefficients _.
  apply qvec_to_rat_linear_combination_unconditional.
Qed.

Theorem q_to_rat_coefficients_nonnegative_iff : forall coefficients,
    List.Forall (fun coefficient : Q => Qle 0 coefficient) coefficients <->
    List.Forall
      (fun coefficient : rat =>
        is_true (((0 : rat) <= coefficient)%R))
      (List.map q_to_rat coefficients).
Proof.
  intro coefficients. induction coefficients as [|coefficient coefficients IH].
  - split; intro Hall; constructor.
  - split; intro Hall.
    + inversion Hall; subst. cbn. constructor.
      * exact (proj1 (q_to_rat_nonnegative_iff coefficient) H1).
      * exact (proj1 IH H2).
    + cbn in Hall. inversion Hall; subst. constructor.
      * exact (proj2 (q_to_rat_nonnegative_iff coefficient) H1).
      * exact (proj2 IH H2).
Qed.

Theorem rat_linear_combination_to_qvec : forall d
    (generators : list ('cV[rat]_d)) (coefficients : list rat),
    List.length generators = List.length coefficients ->
    qvec_to_rat_col
      (qlinear_combination
        (List.map rat_col_to_qvec generators)
        (List.map rat_to_q coefficients)) =
      rat_linear_combination generators coefficients.
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros [|coefficient coefficients] Hlength; simpl in *;
    try apply qvec_to_rat_col_zero; try discriminate.
  inversion Hlength as [Htail].
  rewrite qvec_to_rat_col_add qvec_to_rat_col_scale.
  rewrite rat_col_to_qvec_roundtrip rat_to_q_to_rat IH; [reflexivity|assumption].
Qed.

Theorem q_to_rat_qinner : forall d (left right : QVec d),
    q_to_rat (qinner left right) =
      (qvec_to_rat_row left *m qvec_to_rat_col right) ord0 ord0.
Proof.
  intros d. induction d as [|d IH]; intros left right.
  - rewrite /qinner /qrow_apply /qvec_to_vector /qdot mxE big_ord0.
    apply q_to_rat_zero.
  - rewrite mxE big_ord_recl /=.
    rewrite /qinner /qrow_apply /= q_to_rat_add q_to_rat_mul.
    f_equal.
    + rewrite qvec_to_rat_row_entry qvec_to_rat_col_entry. reflexivity.
    + rewrite (IH (fun index => left (Fin.FS index))
        (fun index => right (Fin.FS index))).
      rewrite mxE.
      apply eq_bigr. intros index _.
      rewrite !qvec_to_rat_row_entry !qvec_to_rat_col_entry.
      unfold ord_to_fin. rewrite !ordinal_to_fin_lift. reflexivity.
Qed.

Theorem qvec_to_rat_col_nonnegative_iff : forall d
    (value : QVec d) (index : 'I_d),
    Qle 0 (value (ord_to_fin index)) <->
      is_true (((0 : rat) <= qvec_to_rat_col value index ord0)%R).
Proof.
  intros d value index. rewrite qvec_to_rat_col_entry.
  apply q_to_rat_nonnegative_iff.
Qed.

Theorem qinner_nonnegative_iff : forall d (left right : QVec d),
    Qle 0 (qinner left right) <->
      is_true (((0 : rat) <=
        (qvec_to_rat_row left *m qvec_to_rat_col right) ord0 ord0)%R).
Proof.
  intros d left right. rewrite <- q_to_rat_qinner.
  apply q_to_rat_nonnegative_iff.
Qed.

Definition rat_cols_of_list {d} (generators : list (QVec d)) :
    list ('cV[rat]_d) :=
  List.map qvec_to_rat_col generators.

Lemma rat_cols_of_list_length : forall d (generators : list (QVec d)),
    List.length (rat_cols_of_list generators) = List.length generators.
Proof.
  intros d generators. induction generators as [|generator generators IH];
    simpl; [reflexivity|now rewrite IH].
Qed.

Lemma rat_cols_of_list_nth_error : forall d (generators : list (QVec d)) n,
    List.nth_error (rat_cols_of_list generators) n =
      option_map qvec_to_rat_col (List.nth_error generators n).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros [|n]; simpl; try reflexivity.
  apply IH.
Qed.

Lemma rat_cols_of_list_nil : forall d,
    @rat_cols_of_list d List.nil = List.nil.
Proof. reflexivity. Qed.

Lemma rat_cols_of_list_cons : forall d (generator : QVec d) generators,
    rat_cols_of_list (generator :: generators) =
      qvec_to_rat_col generator :: rat_cols_of_list generators.
Proof. reflexivity. Qed.

Lemma rat_cols_of_list_duplicate : forall d (generator : QVec d) generators,
    rat_cols_of_list (generator :: generator :: generators) =
      qvec_to_rat_col generator :: qvec_to_rat_col generator ::
        rat_cols_of_list generators.
Proof. reflexivity. Qed.

Theorem qvec_to_rat_col_surjective : forall d (value : 'cV[rat]_d),
    exists source : QVec d, qvec_to_rat_col source = value.
Proof.
  intros d value. exists (rat_col_to_qvec value).
  apply rat_col_to_qvec_roundtrip.
Qed.

Theorem rat_cols_of_list_surjective : forall d
    (values : list ('cV[rat]_d)),
    exists sources : list (QVec d), rat_cols_of_list sources = values.
Proof.
  intros d values. induction values as [|value values [sources IH]].
  - exists List.nil. reflexivity.
  - exists (rat_col_to_qvec value :: sources). simpl.
    rewrite rat_col_to_qvec_roundtrip IH. reflexivity.
Qed.
