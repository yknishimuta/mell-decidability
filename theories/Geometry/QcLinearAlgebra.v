From Coq Require Import QArith Qcanon Vector ZArith.
From mathcomp Require Import all_ssreflect all_algebra.
From Mell.Geometry Require Import Faces MathCompBridge QConeCore RationalHToV.

Module QcMathComp.

Definition qc_eqb (left right : Qc) : bool :=
  if Qc_eq_dec left right then true else false.

Lemma qc_eqb_spec : Equality.axiom qc_eqb.
Proof.
  move=> left right; rewrite /qc_eqb; case: Qc_eq_dec => Heq.
  - by constructor.
  - by constructor.
Qed.

Canonical qc_eq_mixin := EqMixin qc_eqb_spec.
Canonical qc_eq_type := Eval hnf in EqType Qc qc_eq_mixin.

Definition z_code (value : BinNums.Z) : nat + nat :=
  match value with
  | BinNums.Z0 => inl O
  | BinNums.Zpos positive => inl (Pos.to_nat positive)
  | BinNums.Zneg positive => inr (Pos.to_nat positive)
  end.

Definition z_decode (code : nat + nat) : BinNums.Z :=
  match code with
  | inl value => Z.of_nat value
  | inr value => Z.opp (Z.of_nat value)
  end.

Lemma z_code_cancel : cancel z_code z_decode.
Proof.
  case=> [|positive|positive] /=; first reflexivity.
  - exact: positive_nat_Z.
  - by rewrite positive_nat_Z.
Qed.

Definition qc_code (value : Qc) : (nat + nat) * nat :=
  (z_code (Qnum value), Pos.to_nat (Qden value)).

Definition qc_decode (code : (nat + nat) * nat) : Qc :=
  Q2Qc (Qmake (z_decode code.1) (Pos.of_nat code.2)).

Lemma qc_code_cancel : cancel qc_code qc_decode.
Proof.
  move=> [[numerator denominator] canonical].
  rewrite /qc_decode /qc_code /= z_code_cancel Pos2Nat.id.
  apply Qc_is_canon. cbn. exact: Qred_correct.
Qed.

Definition qc_choice_mixin := CanChoiceMixin qc_code_cancel.
Canonical qc_choice_type := Eval hnf in ChoiceType Qc qc_choice_mixin.

Local Open Scope Qc_scope.

Lemma qc_add_inverse_left : forall value : Qc,
    ((- value) + value)%Qc = 0%Qc.
Proof. move=> value. rewrite Qcplus_comm. apply Qcplus_opp_r. Qed.

Definition qc_zmod_mixin :=
  ZmodMixin Qcplus_assoc Qcplus_comm Qcplus_0_l qc_add_inverse_left.
Canonical qc_zmod_type := ZmodType Qc qc_zmod_mixin.

Lemma qc_one_nonzero : (1 : Qc) != 0.
Proof. apply/eqP. exact Q_apart_0_1. Qed.

Definition qc_ring_mixin :=
  ComRingMixin Qcmult_assoc Qcmult_comm Qcmult_1_l
    Qcmult_plus_distr_l qc_one_nonzero.
Canonical qc_ring_type := RingType Qc qc_ring_mixin.
Canonical qc_com_ring_type := Eval hnf in ComRingType Qc Qcmult_comm.

Lemma qc_inverse_zero : (/ (0 : Qc))%Qc = 0%Qc.
Proof. reflexivity. Qed.

Lemma qc_inverse_multiply : forall value : Qc,
    value != 0 -> ((/ value) * value)%Qc = 1%Qc.
Proof. move=> value /eqP Hnonzero. now apply Qcmult_inv_l. Qed.

Definition qc_unit_mixin :=
  FieldUnitMixin qc_inverse_multiply qc_inverse_zero.
Canonical qc_unit_ring_type := UnitRingType Qc qc_unit_mixin.
Canonical qc_com_unit_ring_type := Eval hnf in [comUnitRingType of Qc].

Fact qc_field_axiom : GRing.Field.mixin_of qc_unit_ring_type.
Proof. exact. Qed.

Definition qc_idomain_mixin := FieldIdomainMixin qc_field_axiom.
Canonical qc_idomain_type := IdomainType Qc qc_idomain_mixin.
Canonical qc_field_type :=
  FieldType Qc (FieldMixin qc_inverse_multiply qc_inverse_zero).

End QcMathComp.

Import QcMathComp.
Import GRing.Theory.

Lemma q2qc_eq : forall left right : Q,
    left == right -> Q2Qc left = Q2Qc right.
Proof. intros left right Heq. now apply Q2Qc_eq_iff. Qed.

Lemma q2qc_eq_reflect : forall left right : Q,
    Q2Qc left = Q2Qc right -> left == right.
Proof. intros left right Heq. now apply Q2Qc_eq_iff. Qed.

Lemma q2qc_this : forall value : Qc, Q2Qc value = value.
Proof.
  intros [value Hcanonical]. unfold Q2Qc. cbn.
  apply Qc_is_canon. cbn. rewrite Hcanonical. reflexivity.
Qed.

Lemma q2qc_add : forall left right : Q,
    Q2Qc (left + right) =
      (Q2Qc left + Q2Qc right : QcMathComp.qc_field_type)%R.
Proof.
  intros left right. unfold Qcplus.
  apply (proj2 (Q2Qc_eq_iff _ _)). cbn.
  now rewrite !Qred_correct.
Qed.

Lemma q2qc_mult : forall left right : Q,
    Q2Qc (left * right) =
      (Q2Qc left * Q2Qc right : QcMathComp.qc_field_type)%R.
Proof.
  intros left right. unfold Qcmult.
  apply (proj2 (Q2Qc_eq_iff _ _)). cbn.
  now rewrite !Qred_correct.
Qed.

Definition ordinal_to_fin {d} (index : 'I_d) : Fin.t d :=
  Fin.of_nat_lt (elimT ltP (ltn_ord index)).

Definition fin_to_ordinal {d} (index : Fin.t d) : 'I_d :=
  @Ordinal d (proj1_sig (Fin.to_nat index))
    (introT ltP (proj2_sig (Fin.to_nat index))).

Lemma ordinal_to_finK : forall d (index : 'I_d),
    fin_to_ordinal (ordinal_to_fin index) = index.
Proof.
  intros d index. apply val_inj.
  unfold fin_to_ordinal, ordinal_to_fin. cbn.
  now rewrite Fin.to_nat_of_nat.
Qed.

Lemma fin_to_ordinalK : forall d (index : Fin.t d),
    ordinal_to_fin (fin_to_ordinal index) = index.
Proof.
  intros d index. apply Fin.to_nat_inj.
  unfold ordinal_to_fin, fin_to_ordinal.
  now rewrite Fin.to_nat_of_nat.
Qed.

Lemma ordinal_to_fin_lift : forall d (index : 'I_d),
    ordinal_to_fin (lift ord0 index) = Fin.FS (ordinal_to_fin index).
Proof.
  intros d [index Hindex]. apply Fin.to_nat_inj.
  unfold ordinal_to_fin. cbn. now rewrite !Fin.to_nat_of_nat.
Qed.

Definition qvec_to_qcrow {d} (value : QVec d) : 'rV[Qc]_d :=
  \row_index Q2Qc (value (ordinal_to_fin index)).

Lemma qvec_to_qcrow_eq : forall d (left right : QVec d),
    QVecEq left right -> qvec_to_qcrow left = qvec_to_qcrow right.
Proof.
  intros d left right Heq. apply/rowP=> index.
  rewrite !mxE. apply q2qc_eq, Heq.
Qed.

Lemma qvec_to_qcrow_eq_reflect : forall d (left right : QVec d),
    qvec_to_qcrow left = qvec_to_qcrow right -> QVecEq left right.
Proof.
  intros d left right Heq index.
  have Hentry := congr1 (fun row : 'rV[Qc]_d =>
    row ord0 (fin_to_ordinal index)) Heq.
  rewrite !mxE /qvec_to_qcrow fin_to_ordinalK in Hentry.
  now apply q2qc_eq_reflect.
Qed.

Lemma qvec_to_qcrow_zero : forall d,
    qvec_to_qcrow (qvec_zero d) = (0 : 'rV[Qc]_d)%R.
Proof.
  intros d. apply/rowP=> index. rewrite mxE /qvec_to_qcrow mxE.
  reflexivity.
Qed.

Lemma qvec_to_qcrow_add : forall d (left right : QVec d),
    qvec_to_qcrow (qvec_add left right) =
      (qvec_to_qcrow left + qvec_to_qcrow right)%R.
Proof.
  intros d left right. apply/rowP=> index.
  rewrite /qvec_to_qcrow !mxE /qvec_add q2qc_add. reflexivity.
Qed.

Lemma qvec_to_qcrow_scale : forall d coefficient (value : QVec d),
    qvec_to_qcrow (qvec_scale coefficient value) =
      (Q2Qc coefficient *: qvec_to_qcrow value)%R.
Proof.
  intros d coefficient value. apply/rowP=> index.
  rewrite /qvec_to_qcrow !mxE /qvec_scale q2qc_mult. reflexivity.
Qed.

Definition qcrow_inner {d} (left right : 'rV[Qc]_d) : Qc :=
  (\sum_(index < d) left ord0 index * right ord0 index)%R.

Lemma qinner_to_qcrow : forall d (left right : QVec d),
    Q2Qc (qinner left right) =
      qcrow_inner (qvec_to_qcrow left) (qvec_to_qcrow right).
Proof.
  intros d. induction d as [|d IH]; intros left right.
  - rewrite /qinner /qrow_apply /qvec_to_vector /qdot
      /qcrow_inner big_ord0. reflexivity.
  - rewrite /qcrow_inner big_ord_recl /=.
    rewrite /qinner /qrow_apply /= q2qc_add q2qc_mult.
    f_equal.
    + rewrite /qvec_to_qcrow !mxE. reflexivity.
    + rewrite (IH (fun index => left (Fin.FS index))
        (fun index => right (Fin.FS index))).
      apply eq_bigr. intros index _.
      rewrite /qvec_to_qcrow !mxE ordinal_to_fin_lift. reflexivity.
Qed.

Lemma qcrow_inner_qvec_zero : forall d (normal value : QVec d),
    qinner normal value == 0 ->
    qcrow_inner (qvec_to_qcrow normal) (qvec_to_qcrow value) =
      (0%R : Qc).
Proof.
  intros d normal value Hzero.
  rewrite <- qinner_to_qcrow. apply q2qc_eq. exact Hzero.
Qed.

Lemma qcrow_inner_qvec_nonzero : forall d (normal value : QVec d),
    ~ qinner normal value == 0 ->
    qcrow_inner (qvec_to_qcrow normal) (qvec_to_qcrow value) !=
      (0%R : Qc).
Proof.
  intros d normal value Hnonzero. apply/eqP. intro Hzero.
  apply Hnonzero, q2qc_eq_reflect. now rewrite qinner_to_qcrow.
Qed.

Lemma qcrow_inner_add_right : forall d (normal left right : 'rV[Qc]_d),
    qcrow_inner normal (left + right)%R =
      (qcrow_inner normal left + qcrow_inner normal right)%R.
Proof.
  intros d normal left right. rewrite /qcrow_inner.
  under eq_bigr do rewrite mxE mulrDr.
  now rewrite big_split.
Qed.

Lemma qcrow_inner_scale_right : forall d coefficient
    (normal value : 'rV[Qc]_d),
    qcrow_inner normal (coefficient *: value)%R =
      (coefficient * qcrow_inner normal value)%R.
Proof.
  intros d coefficient normal value. rewrite /qcrow_inner.
  under eq_bigr do rewrite mxE mulrCA.
  symmetry. apply big_distrr.
Qed.
