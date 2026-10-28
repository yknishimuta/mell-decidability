From Coq Require Import Lia List QArith.
From Mell.Geometry Require Import RationalDefinability RationalQEOne.

Import ListNotations.
Open Scope Q_scope.

Check separate_term_correct.
Check eliminate_one_correct.

Definition no_free : QEnvironment := fun _ => 0.

Definition open_interval : QAffineConjunction :=
  [QALt (QTConst 0) (QTVar 0);
   QALt (QTVar 0) (QTConst 1)].

Example open_interval_eliminates_true :
  qdnf_semantics no_free (eliminate_one open_interval).
Proof.
  apply (proj1 (eliminate_one_correct open_interval no_free)).
  exists (1#2). unfold qconjunction_semantics.
  repeat constructor; unfold Qlt; cbn; lia.
Qed.

Definition strict_lower_weak_zero : QAffineConjunction :=
  [QALt (QTConst 0) (QTVar 0);
   QALe (QTVar 0) (QTConst 0)].

Example strict_lower_weak_zero_eliminates_false :
  ~ qdnf_semantics no_free (eliminate_one strict_lower_weak_zero).
Proof.
  intro Helim.
  apply (proj2 (eliminate_one_correct strict_lower_weak_zero no_free)) in Helim.
  destruct Helim as [bound Hbody]. unfold qconjunction_semantics in Hbody.
  unfold strict_lower_weak_zero in Hbody.
  rewrite !Forall_cons_iff in Hbody. destruct Hbody as [Hpositive [Hnonpositive _]].
  cbn in Hpositive, Hnonpositive.
  exact (Qlt_not_le _ _ Hpositive Hnonpositive).
Qed.

Definition closed_zero : QAffineConjunction :=
  [QALe (QTConst 0) (QTVar 0);
   QALe (QTVar 0) (QTConst 0)].

Example closed_zero_eliminates_true :
  qdnf_semantics no_free (eliminate_one closed_zero).
Proof.
  apply (proj1 (eliminate_one_correct closed_zero no_free)).
  exists 0. unfold qconjunction_semantics. repeat constructor; apply Qle_refl.
Qed.

Definition strict_zero_interval : QAffineConjunction :=
  [QALt (QTConst 0) (QTVar 0);
   QALt (QTVar 0) (QTConst 0)].

Example strict_zero_interval_eliminates_false :
  ~ qdnf_semantics no_free (eliminate_one strict_zero_interval).
Proof.
  intro Helim.
  apply (proj2 (eliminate_one_correct strict_zero_interval no_free)) in Helim.
  destruct Helim as [bound Hbody]. unfold qconjunction_semantics in Hbody.
  unfold strict_zero_interval in Hbody.
  rewrite !Forall_cons_iff in Hbody. destruct Hbody as [Hpositive [Hnegative _]].
  cbn in Hpositive, Hnegative.
  exact (Qlt_not_le _ _ Hpositive (Qlt_le_weak _ _ Hnegative)).
Qed.

Definition upper_only : QAffineConjunction :=
  [QALt (QTVar 0) (QTConst 0)].

Definition lower_only : QAffineConjunction :=
  [QALt (QTConst 0) (QTVar 0)].

Example upper_only_has_witness :
  qdnf_semantics no_free (eliminate_one upper_only).
Proof.
  apply (proj1 (eliminate_one_correct upper_only no_free)).
  exists (-1). unfold qconjunction_semantics, upper_only. constructor.
  - cbn [qaffine_atom_semantics qterm_semantics qenvironment_extend].
    unfold Qlt; cbn; lia.
  - constructor.
Qed.

Example lower_only_has_witness :
  qdnf_semantics no_free (eliminate_one lower_only).
Proof.
  apply (proj1 (eliminate_one_correct lower_only no_free)).
  exists 1. unfold qconjunction_semantics, lower_only. constructor.
  - cbn [qaffine_atom_semantics qterm_semantics qenvironment_extend].
    unfold Qlt; cbn; lia.
  - constructor.
Qed.

Example no_bounds_has_witness :
  qdnf_semantics no_free (eliminate_one []).
Proof.
  apply (proj1 (eliminate_one_correct [] no_free)).
  exists 0. unfold qconjunction_semantics. constructor.
Qed.

Definition half_equation : QAffineConjunction :=
  [QAEq (QTScale 2 (QTVar 0)) (QTConst 1)].

Example half_equation_has_witness :
  qdnf_semantics no_free (eliminate_one half_equation).
Proof.
  apply (proj1 (eliminate_one_correct half_equation no_free)).
  exists (1#2). unfold qconjunction_semantics. constructor.
  - cbn. reflexivity.
  - constructor.
Qed.

Definition zero_coefficient_constraint : QAffineConjunction :=
  [QALt (QTConst 0) (QTAdd (QTScale 0 (QTVar 0)) (QTConst 1))].

Example zero_coefficient_is_residual :
  qdnf_semantics no_free (eliminate_one zero_coefficient_constraint).
Proof.
  apply (proj1 (eliminate_one_correct zero_coefficient_constraint no_free)).
  exists 37. unfold qconjunction_semantics, zero_coefficient_constraint.
  constructor; [cbn [qaffine_atom_semantics qterm_semantics
    qenvironment_extend]; unfold Qlt; cbn; lia|constructor].
Qed.

Definition two_free_environment : QEnvironment :=
  fun variable => match variable with O => 3 | S _ => 5 end.

Definition bound_below_first_free : QAffineConjunction :=
  [QALt (QTVar 0) (QTVar 1)].

Example debruijn_shift_preserves_first_free :
  qdnf_semantics two_free_environment (eliminate_one bound_below_first_free).
Proof.
  apply (proj1 (eliminate_one_correct bound_below_first_free two_free_environment)).
  exists 2. unfold qconjunction_semantics, bound_below_first_free.
  constructor; [cbn [qaffine_atom_semantics qterm_semantics
    qenvironment_extend two_free_environment]; unfold Qlt; cbn; lia|constructor].
Qed.

Definition noncanonical_open_interval : QAffineConjunction :=
  [QALt (QTConst 0) (QTVar 0);
   QALt (QTVar 0) (QTConst (2#2))].

Example qeq_noncanonical_boundary :
  qdnf_semantics no_free (eliminate_one noncanonical_open_interval).
Proof.
  apply (proj1 (eliminate_one_correct noncanonical_open_interval no_free)).
  exists (1#2). unfold qconjunction_semantics.
  repeat constructor; unfold Qlt; cbn; lia.
Qed.

Set Printing Implicit.
Check @separate_term_correct.
Check @normalize_atom_correct.
Check @finite_bounds_have_witness.
Check @eliminate_one_correct.
Print Assumptions separate_term_correct.
Print Assumptions finite_bounds_have_witness.
Print Assumptions eliminate_one_correct.
