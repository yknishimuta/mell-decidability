From Coq Require Import List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge Periodic RationalSpan.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.
Set Printing Implicit.

Check @QSpan.
Check @VecOf.
Check @qspan_zero.
Check @qspan_nil_iff.
Check @qspan_add.
Check @qspan_opp.
Check @qspan_scale.
Check @zgroup_generated_in_qspan.
Check @finite_p_spanning.

Definition span_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition span_z2 (left right : Z) : ZVec 2 :=
  @Vector.cons Z left 1 (@Vector.cons Z right 0 (@Vector.nil Z)).

Example qspan_empty_is_zero : QSpan ([] : list (ZVec 0)) (qvec_zero 0).
Proof. apply qspan_zero. Qed.

Example qspan_duplicate_generator :
    QSpan [span_z1 1; span_z1 1] (zvec_to_qvec (span_z1 1)).
Proof. apply qspan_member. simpl; auto. Qed.

Example finite_spanning_dimension_zero :
    exists generators : list (ZVec 0),
      List.Forall (@zvec_generated 0 []) generators /\
      forall value : QVec 0,
        VecOf (@zvec_generated 0 []) value <-> QSpan generators value.
Proof. apply finite_p_spanning, generated_periodic. Qed.

Example finite_spanning_zero_monoid :
    exists generators : list (ZVec 1),
      List.Forall (@zvec_generated 1 []) generators /\
      forall value : QVec 1,
        VecOf (@zvec_generated 1 []) value <-> QSpan generators value.
Proof. apply finite_p_spanning, generated_periodic. Qed.

Example finite_spanning_twoN :
    exists generators : list (ZVec 1),
      List.Forall (zvec_generated [span_z1 2]) generators /\
      forall value : QVec 1,
        VecOf (zvec_generated [span_z1 2]) value <-> QSpan generators value.
Proof. apply finite_p_spanning, generated_periodic. Qed.

Definition span_all_Z (_ : ZVec 1) : Prop := True.

Lemma span_all_Z_periodic : Periodic span_all_Z.
Proof. split; [exact I|intros; exact I]. Qed.

Example finite_spanning_all_Z :
    exists generators : list (ZVec 1),
      List.Forall span_all_Z generators /\
      forall value : QVec 1,
        VecOf span_all_Z value <-> QSpan generators value.
Proof. apply finite_p_spanning, span_all_Z_periodic. Qed.

Example finite_spanning_low_rank :
    exists generators : list (ZVec 2),
      List.Forall (zvec_generated [span_z2 1 0]) generators /\
      forall value : QVec 2,
        VecOf (zvec_generated [span_z2 1 0]) value <->
        QSpan generators value.
Proof. apply finite_p_spanning, generated_periodic. Qed.

Example finite_spanning_mixed_sign :
    exists generators : list (ZVec 1),
      List.Forall (zvec_generated [span_z1 2; span_z1 (-3)]) generators /\
      forall value : QVec 1,
        VecOf (zvec_generated [span_z1 2; span_z1 (-3)]) value <->
        QSpan generators value.
Proof. apply finite_p_spanning, generated_periodic. Qed.

Print Assumptions qspan_zero.
Print Assumptions qspan_nil_iff.
Print Assumptions qspan_add.
Print Assumptions qspan_opp.
Print Assumptions qspan_scale.
Print Assumptions zgroup_generated_in_qspan.
Print Assumptions finite_p_spanning.
