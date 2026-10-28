From Coq Require Import Lia List QArith.
From Mell.Geometry Require Import MathCompBridge RationalDefinability
  RationalQEOne RationalQENormalForm.

Import ListNotations.
Open Scope Q_scope.

Check qformula_to_dnf_correct.
Check qformula_to_dnf_closed.
Check qdefinable_finite_cells.

Definition qe2_no_free : QEnvironment := fun _ => 0.

Example top_is_single_empty_cell :
  qformula_to_dnf QFTop = [[]].
Proof. reflexivity. Qed.

Example bottom_is_empty_dnf :
  qformula_to_dnf QFBot = [].
Proof. reflexivity. Qed.

Example equality_is_two_weak_inequalities :
  qformula_to_dnf (QFEq (QTVar 0) (QTConst 1)) =
    [[QALe (QTVar 0) (QTConst 1);
      QALe (QTConst 1) (QTVar 0)]].
Proof. reflexivity. Qed.

Example negated_equal_constants :
  qaffine_dnf_semantics qe2_no_free
    (qformula_to_dnf (QFNot (QFEq (QTConst 0) (QTConst 1)))).
Proof.
  apply (proj1 (qformula_to_dnf_correct _ _)). cbn. discriminate.
Qed.

Example negated_strict_is_weak :
  qaffine_dnf_semantics qe2_no_free
    (qformula_to_dnf (QFNot (QFLt (QTConst 1) (QTConst 0)))).
Proof.
  apply (proj1 (qformula_to_dnf_correct _ _)). cbn. unfold Qlt; cbn; lia.
Qed.

Example negated_weak_is_strict :
  qaffine_dnf_semantics qe2_no_free
    (qformula_to_dnf (QFNot (QFLe (QTConst 1) (QTConst 0)))).
Proof.
  apply (proj1 (qformula_to_dnf_correct _ _)). cbn. unfold Qle; cbn; lia.
Qed.

Definition dense_interval_formula : QFormula :=
  QFExists (QFAnd
    (QFLt (QTConst 0) (QTVar 0))
    (QFLt (QTVar 0) (QTVar 1))).

Example dense_interval_iff_positive : forall x,
  qformula_semantics (fun _ => x) dense_interval_formula <-> 0 < x.
Proof.
  intro x. cbn. split.
  - intros [z [Hz Hx]]. eapply Qlt_trans; eauto.
  - intro Hx. exists ((0 + x) / 2). apply qrational_midpoint. exact Hx.
Qed.

Definition linear_totality_formula : QFormula :=
  QFForall (QFOr
    (QFLe (QTVar 0) (QTVar 1))
    (QFLt (QTVar 1) (QTVar 0))).

Example linear_totality_normalizes_true : forall x,
  qaffine_dnf_semantics (fun _ => x)
    (qformula_to_dnf linear_totality_formula).
Proof.
  intro x. apply (proj1 (qformula_to_dnf_correct _ _)).
  cbn. intro z. destruct (Qlt_le_dec x z); auto.
Qed.

Definition nested_dense_formula : QFormula :=
  QFForall (QFExists (QFAnd
    (QFLt (QTVar 1) (QTVar 0))
    (QFLt (QTVar 0) (QTAdd (QTVar 1) (QTConst 1))))).

Example nested_dense_normalizes_true :
  qaffine_dnf_semantics qe2_no_free
    (qformula_to_dnf nested_dense_formula).
Proof.
  apply (proj1 (qformula_to_dnf_correct _ _)). cbn. intro z.
  exists ((z + (z + 1)) / 2). apply qrational_midpoint.
  apply qle_lt_plus_one. apply Qle_refl.
Qed.

Definition no_greatest_formula : QFormula :=
  QFExists (QFForall (QFLe (QTVar 0) (QTVar 1))).

Example no_greatest_normalizes_false :
  ~ qaffine_dnf_semantics qe2_no_free
      (qformula_to_dnf no_greatest_formula).
Proof.
  intro H. apply (proj2 (qformula_to_dnf_correct _ _)) in H.
  cbn in H. destruct H as [z Hz].
  specialize (Hz (z + 1)).
  assert (Hlt : z < z + 1) by (apply qle_lt_plus_one; apply Qle_refl).
  exact (Qlt_not_le _ _ Hlt Hz).
Qed.

Definition shadowing_formula : QFormula :=
  QFNot (QFExists (QFForall (QFNot
    (QFLt (QTVar 0) (QTAdd (QTVar 1) (QTConst 1)))))).

Example nested_negation_and_alternation :
  qaffine_dnf_semantics qe2_no_free
    (qformula_to_dnf shadowing_formula).
Proof.
  apply (proj1 (qformula_to_dnf_correct _ _)). cbn.
  intros [z Hz]. specialize (Hz z). apply Hz.
  apply qle_lt_plus_one. apply Qle_refl.
Qed.

Example noncanonical_rational_survives :
  qaffine_dnf_semantics qe2_no_free
    (qformula_to_dnf (QFEq (QTConst (2#2)) (QTConst 1))).
Proof.
  apply (proj1 (qformula_to_dnf_correct _ _)). cbn. reflexivity.
Qed.

Definition first_less_second : QFormula :=
  QFLt (QTVar 0) (QTVar 1).

Example two_free_variables_keep_order :
  qaffine_dnf_semantics (fun n => if Nat.eqb n 0 then 2 else 3)
    (qformula_to_dnf first_less_second).
Proof.
  apply (proj1 (qformula_to_dnf_correct _ _)).
  cbn. unfold Qlt; cbn; lia.
Qed.

Definition all_zero_dimensional : QSet 0 := fun _ => True.

Example zero_dimensional_definable_has_cells :
  exists cells : list QAffineConjunction,
    forall x : QVec 0,
      all_zero_dimensional x <->
      exists cell, List.In cell cells /\
        qconjunction_semantics (qvec_environment x) cell.
Proof.
  apply qdefinable_finite_cells.
  exists QFTop. split; [reflexivity|]. intro x. cbn. tauto.
Qed.

Set Printing Implicit.
Check @qaffine_dnf_neg_correct.
Check @qaffine_dnf_and_correct.
Check @qaffine_dnf_exists_correct.
Check @qformula_to_dnf_correct.
Check @qformula_to_dnf_closed.
Check @qdefinable_finite_cells.
Print Assumptions qaffine_atom_neg_correct.
Print Assumptions qaffine_dnf_and_correct.
Print Assumptions qaffine_dnf_neg_correct.
Print Assumptions qaffine_dnf_exists_correct.
Print Assumptions qformula_to_dnf_correct.
Print Assumptions qformula_to_dnf_closed.
Print Assumptions qdefinable_finite_cells.
