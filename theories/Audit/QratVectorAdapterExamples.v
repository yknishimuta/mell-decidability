From Coq Require Import Fin Lia List QArith.
From mathcomp Require Import all_ssreflect all_algebra.
From Mell.Geometry Require Import Faces LatticeGordanV MathCompBridge QConeCore
  QratAdapter QratVectorAdapter.

Import GRing.Theory ListNotations.
Set Printing Implicit.
Open Scope ring_scope.

Check @fin_to_ord.
Check @ord_to_fin.
Check @fin_to_ordK.
Check @ord_to_finK.
Check @fin_to_ord_val.
Check @ord_to_fin_val.

Example fin_ord_roundtrip_example : forall d (index : Fin.t d),
    ord_to_fin (fin_to_ord index) = index.
Proof. apply fin_to_ordK. Qed.

Example ord_fin_roundtrip_example : forall d (index : 'I_d),
    fin_to_ord (ord_to_fin index) = index.
Proof. apply ord_to_finK. Qed.

Example dimension_zero_fin_is_empty : forall index : Fin.t 0, False.
Proof. intro index. inversion index. Qed.

Check @qvec_to_rat_col.
Check @rat_col_to_qvec.
Check @qvec_to_rat_row.
Check @rat_row_to_qvec.
Check @qvec_to_rat_col_entry.
Check @qvec_to_rat_row_entry.
Check @qvec_to_rat_col_eq_iff.
Check @qvec_to_rat_col_roundtrip.
Check @rat_col_to_qvec_roundtrip.
Check @qvec_to_rat_row_eq_iff.
Check @qvec_to_rat_row_roundtrip.
Check @rat_row_to_qvec_roundtrip.
Check @qvec_to_rat_row_transpose.

Definition a2_vec1_half : QVec 1 := fun _ => Qmake 1 2%positive.
Definition a2_vec1_two_fourths : QVec 1 :=
  fun _ => Qmake 2 4%positive.

Example dimension_zero_column_roundtrip : forall value : 'cV[rat]_0,
    qvec_to_rat_col (rat_col_to_qvec value) = value.
Proof. apply rat_col_to_qvec_roundtrip. Qed.

Example nonnormalized_dimension_one_columns_equal :
    qvec_to_rat_col a2_vec1_half = qvec_to_rat_col a2_vec1_two_fourths.
Proof.
  apply (proj2 (qvec_to_rat_col_eq_iff _ _)).
  intro index. unfold a2_vec1_half, a2_vec1_two_fourths. reflexivity.
Qed.

Example dimension_one_qvec_roundtrip :
    QVecEq (rat_col_to_qvec (qvec_to_rat_col a2_vec1_half)) a2_vec1_half.
Proof. apply qvec_to_rat_col_roundtrip. Qed.

Example row_is_column_transpose :
    qvec_to_rat_row a2_vec1_half = (qvec_to_rat_col a2_vec1_half)^T.
Proof. apply qvec_to_rat_row_transpose. Qed.

Check @qvec_to_rat_col_zero.
Check @qvec_to_rat_col_add.
Check @qvec_to_rat_col_scale.
Check @qvec_to_rat_col_opp.
Check @qvec_to_rat_col_sub.
Check @qvec_to_rat_row_zero.
Check @qvec_to_rat_row_add.
Check @qvec_to_rat_row_scale.
Check @qvec_to_rat_row_opp.
Check @qvec_to_rat_row_sub.

Check @rat_linear_combination.
Check @qvec_to_rat_linear_combination.
Check @q_to_rat_coefficients_nonnegative_iff.
Check @rat_linear_combination_to_qvec.

Check @q_to_rat_qinner.
Check @qvec_to_rat_col_nonnegative_iff.
Check @qinner_nonnegative_iff.
Check @rat_cols_of_list.
Check @rat_cols_of_list_length.
Check @rat_cols_of_list_nth_error.
Check @rat_cols_of_list_nil.
Check @rat_cols_of_list_cons.
Check @qvec_to_rat_col_surjective.
Check @rat_cols_of_list_surjective.

Definition a2_qpair (left right : Q) : QVec 2 :=
  fun index => Fin.caseS' index (fun _ => Q) left (fun _ => right).

Definition a2_signed2 : QVec 2 :=
  a2_qpair (Qmake (Z.opp (Z.of_nat 3)) 2%positive) (Qmake 2 4%positive).

Definition a2_large2 : QVec 2 :=
  a2_qpair (inject_Z (Z.of_nat 123456789))
    (inject_Z (Z.opp (Z.of_nat 987654321))).

Example dimension_two_signed_roundtrip :
    QVecEq (rat_col_to_qvec (qvec_to_rat_col a2_signed2)) a2_signed2.
Proof. apply qvec_to_rat_col_roundtrip. Qed.

Example large_integer_components_roundtrip :
    QVecEq (rat_col_to_qvec (qvec_to_rat_col a2_large2)) a2_large2.
Proof. apply qvec_to_rat_col_roundtrip. Qed.

Example zero_vector_conversion :
    qvec_to_rat_col (qvec_zero 2) = 0.
Proof. apply qvec_to_rat_col_zero. Qed.

Example signed_vector_addition_conversion :
    qvec_to_rat_col (qvec_add a2_signed2 a2_large2) =
      qvec_to_rat_col a2_signed2 + qvec_to_rat_col a2_large2.
Proof. apply qvec_to_rat_col_add. Qed.

Example empty_linear_combination :
    qvec_to_rat_col (qlinear_combination (@nil (QVec 2)) (@nil Q)) = 0.
Proof. cbn. apply qvec_to_rat_col_zero. Qed.

Example zero_coefficients_linear_combination :
    qvec_to_rat_col
      (qlinear_combination [a2_signed2; a2_large2] [(0 : Q); (0 : Q)]) =
    rat_linear_combination
      [qvec_to_rat_col a2_signed2; qvec_to_rat_col a2_large2]
      [q_to_rat (0 : Q); q_to_rat (0 : Q)].
Proof. apply qvec_to_rat_linear_combination. reflexivity. Qed.

Example zero_coefficients_rat_sum :
    rat_linear_combination
      [qvec_to_rat_col a2_signed2; qvec_to_rat_col a2_large2]
      [(0 : rat); (0 : rat)] = 0.
Proof. cbn. apply/matrixP=> row column. by rewrite !mxE !mul0r !add0r. Qed.

Example signed_nonnormalized_linear_combination :
    qvec_to_rat_col
      (qlinear_combination [a2_signed2; a2_large2; a2_signed2]
        [Qmake 1 2%positive; Qmake (Z.opp (Z.of_nat 3)) 6%positive;
          Qmake 2 4%positive]) =
    rat_linear_combination
      [qvec_to_rat_col a2_signed2; qvec_to_rat_col a2_large2;
        qvec_to_rat_col a2_signed2]
      [q_to_rat (Qmake 1 2%positive);
        q_to_rat (Qmake (Z.opp (Z.of_nat 3)) 6%positive);
        q_to_rat (Qmake 2 4%positive)].
Proof. apply qvec_to_rat_linear_combination. reflexivity. Qed.

Example dependent_rank_deficient_generators :
    qvec_to_rat_col
      (qlinear_combination [a2_signed2; qvec_scale (2 : Q) a2_signed2]
        [(1 : Q); Qmake 1 2%positive]) =
    rat_linear_combination
      [qvec_to_rat_col a2_signed2;
        qvec_to_rat_col (qvec_scale (2 : Q) a2_signed2)]
      [q_to_rat (1 : Q); q_to_rat (Qmake 1 2%positive)].
Proof. apply qvec_to_rat_linear_combination. reflexivity. Qed.

Example nonnegative_nonnormalized_coefficients :
    List.Forall (fun coefficient : Q => Qle 0 coefficient)
      [Qmake 1 2%positive; Qmake 2 4%positive; (0 : Q)].
Proof. repeat constructor; unfold Qle; cbn; lia. Qed.

Example converted_coefficients_are_nonnegative :
    List.Forall (fun coefficient : rat =>
      is_true (((0 : rat) <= coefficient)%R))
      (List.map q_to_rat
        [Qmake 1 2%positive; Qmake 2 4%positive; (0 : Q)]).
Proof.
  apply (proj1 (q_to_rat_coefficients_nonnegative_iff _)).
  exact nonnegative_nonnormalized_coefficients.
Qed.

Example negative_coefficient_detected :
    ~ List.Forall (fun coefficient : Q => Qle 0 coefficient)
        [Qmake 1 2%positive; Qmake (Z.opp (Z.of_nat 3)) 6%positive].
Proof.
  intro Hall. inversion Hall as [|? ? _ Htail]; subst.
  inversion Htail as [|? ? Hnegative _]; subst.
  unfold Qle in Hnegative. cbn in Hnegative. lia.
Qed.

Example converted_negative_coefficient_detected :
    ~ List.Forall (fun coefficient : rat =>
        is_true (((0 : rat) <= coefficient)%R))
        (List.map q_to_rat
          [Qmake 1 2%positive; Qmake (Z.opp (Z.of_nat 3)) 6%positive]).
Proof.
  intro Hall. apply negative_coefficient_detected.
  exact (proj2 (q_to_rat_coefficients_nonnegative_iff _) Hall).
Qed.

Example duplicate_generators_preserved :
    rat_cols_of_list [a2_signed2; a2_signed2] =
      [qvec_to_rat_col a2_signed2; qvec_to_rat_col a2_signed2].
Proof. reflexivity. Qed.

Example converted_generator_list_has_preimage : forall values : list ('cV[rat]_2),
    exists sources : list (QVec 2), rat_cols_of_list sources = values.
Proof. apply rat_cols_of_list_surjective. Qed.

Example dimension_zero_inner_product : forall left right : QVec 0,
    q_to_rat (qinner left right) =
      (qvec_to_rat_row left *m qvec_to_rat_col right) ord0 ord0.
Proof. apply q_to_rat_qinner. Qed.

Example negative_inner_product :
    Qlt (qinner a2_signed2 (a2_qpair (1 : Q) (0 : Q))) (0 : Q).
Proof. vm_compute. reflexivity. Qed.

Example zero_inner_product :
    qinner (a2_qpair (1 : Q) (0 : Q)) (a2_qpair (0 : Q) (1 : Q)) ==
      (0 : Q).
Proof. vm_compute. reflexivity. Qed.

Example positive_inner_product :
    Qlt (0 : Q)
      (qinner (a2_qpair (1 : Q) (1 : Q)) (a2_qpair (1 : Q) (1 : Q))).
Proof. vm_compute. reflexivity. Qed.

Example negative_matrix_inner_product :
    is_true (((qvec_to_rat_row a2_signed2 *m
      qvec_to_rat_col (a2_qpair (1 : Q) (0 : Q))) ord0 ord0 <
      (0 : rat))%R).
Proof.
  rewrite <- q_to_rat_qinner.
  apply (proj1 (q_to_rat_negative_iff _)). exact negative_inner_product.
Qed.

Example zero_matrix_inner_product :
    (qvec_to_rat_row (a2_qpair (1 : Q) (0 : Q)) *m
      qvec_to_rat_col (a2_qpair (0 : Q) (1 : Q))) ord0 ord0 =
      (0 : rat).
Proof.
  rewrite <- q_to_rat_qinner. rewrite <- q_to_rat_zero.
  apply (proj2 (q_to_rat_eq_iff _ _)). exact zero_inner_product.
Qed.

Example positive_matrix_inner_product :
    is_true ((((0 : rat) <
      (qvec_to_rat_row (a2_qpair (1 : Q) (1 : Q)) *m
        qvec_to_rat_col (a2_qpair (1 : Q) (1 : Q))) ord0 ord0))%R).
Proof.
  rewrite <- q_to_rat_qinner.
  apply (proj1 (q_to_rat_positive_iff _)). exact positive_inner_product.
Qed.

Example coordinate_nonnegative_correspondence : forall index : 'I_2,
    Qle 0 (a2_large2 (ord_to_fin index)) <->
      is_true (((0 : rat) <= qvec_to_rat_col a2_large2 index ord0)%R).
Proof. apply qvec_to_rat_col_nonnegative_iff. Qed.

Print Assumptions fin_to_ordK.
Print Assumptions ord_to_finK.
Print Assumptions fin_to_ord_val.
Print Assumptions ord_to_fin_val.
Print Assumptions qvec_to_rat_col_entry.
Print Assumptions qvec_to_rat_row_entry.
Print Assumptions qvec_to_rat_col_eq_iff.
Print Assumptions qvec_to_rat_col_roundtrip.
Print Assumptions rat_col_to_qvec_roundtrip.
Print Assumptions qvec_to_rat_row_eq_iff.
Print Assumptions qvec_to_rat_row_roundtrip.
Print Assumptions rat_row_to_qvec_roundtrip.
Print Assumptions qvec_to_rat_row_transpose.
Print Assumptions qvec_to_rat_col_zero.
Print Assumptions qvec_to_rat_col_add.
Print Assumptions qvec_to_rat_col_scale.
Print Assumptions qvec_to_rat_col_opp.
Print Assumptions qvec_to_rat_col_sub.
Print Assumptions qvec_to_rat_row_zero.
Print Assumptions qvec_to_rat_row_add.
Print Assumptions qvec_to_rat_row_scale.
Print Assumptions qvec_to_rat_row_opp.
Print Assumptions qvec_to_rat_row_sub.
Print Assumptions qvec_to_rat_linear_combination_unconditional.
Print Assumptions qvec_to_rat_linear_combination.
Print Assumptions q_to_rat_coefficients_nonnegative_iff.
Print Assumptions rat_linear_combination_to_qvec.
Print Assumptions q_to_rat_qinner.
Print Assumptions qvec_to_rat_col_nonnegative_iff.
Print Assumptions qinner_nonnegative_iff.
Print Assumptions rat_cols_of_list_length.
Print Assumptions rat_cols_of_list_nth_error.
Print Assumptions rat_cols_of_list_nil.
Print Assumptions rat_cols_of_list_cons.
Print Assumptions rat_cols_of_list_duplicate.
Print Assumptions qvec_to_rat_col_surjective.
Print Assumptions rat_cols_of_list_surjective.
