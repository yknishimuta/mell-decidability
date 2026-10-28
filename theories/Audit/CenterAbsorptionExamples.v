From Coq Require Import Fin Lia List QArith Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Center CenterAbsorption
  CenterCharacterization ClosedLinearization LatticeGordanH MathCompBridge
  Periodic QConeCore.
From Mell.Order Require Import PeriodicOrder.
From Mell.Audit Require Import CenterExamples.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.
Set Printing Implicit.

Check @periodic_cone_positive_ray.
Check @center_add_closed_linearization.
Check @center_absorbs_closed_linearization.

Definition absorption_all_z {d} (_ : ZVec d) : Prop := True.

Lemma absorption_all_z_periodic : forall d,
    Periodic (@absorption_all_z d).
Proof. intro d. split; [exact I|intros; exact I]. Qed.

Definition absorption_n2 (value : ZVec 2) : Prop :=
  (0 <= Vector.nth value Fin.F1)%Z /\
  (0 <= Vector.nth value (Fin.FS Fin.F1))%Z.

Lemma absorption_n2_periodic : Periodic absorption_n2.
Proof.
  split.
  - split; unfold zvec_zero; rewrite !const_nth; lia.
  - intros left right [Hleft1 Hleft2] [Hright1 Hright2]. split;
      unfold zvec_add;
      rewrite (nth_map2 Z.add left right _ _ _ eq_refl eq_refl); lia.
Qed.

Example absorption_dimension_zero :
    Center (@center_zero_set 0) (zvec_zero 0) ->
    ClosedLinearization (@center_zero_set 0) (zvec_zero 0) ->
    Center (@center_zero_set 0)
      (zvec_add (zvec_zero 0) (zvec_zero 0)).
Proof.
  apply center_add_closed_linearization, center_zero_set_periodic.
Qed.

Example absorption_zero_monoid_q_zero :
    Center (@center_zero_set 1) (zvec_zero 1).
Proof.
  eapply center_add_closed_linearization with
    (value := zvec_zero 1) (offset := zvec_zero 1).
  - apply center_zero_set_periodic.
  - apply center_zero_monoid_contains_zero.
  - apply closed_linearization_zero, center_zero_set_periodic.
Qed.

Example zero_approximant_has_positive_ray :
    exists value coefficient,
      (@center_zero_set 1) value /\ 0 < coefficient /\
      QVecEq (qvec_zero 1)
        (qvec_scale coefficient (zvec_to_qvec value)).
Proof.
  apply periodic_cone_positive_ray with (set := @center_zero_set 1).
  - apply center_zero_set_periodic.
  - exists (qvec_zero 1). split; [constructor|apply qvec_eq_refl].
Qed.

Example tiny_positive_coefficient_survives :
    Vector.Forall (fun coefficient : Q => 0 < coefficient)
      (Vector.map2 Qplus
        (@Vector.cons Q (1#1000000) 0 (@Vector.nil Q))
        (@Vector.cons Q 0 0 (@Vector.nil Q))).
Proof.
  apply vector_map2_plus_positive.
  - repeat constructor.
  - intro index. refine (Fin.caseS' index (fun index => _) _ _).
    + cbn. reflexivity.
    + intro tail_index. exact (Fin.case0 (fun index =>
        - Vector.nth (@Vector.cons Q (1#1000000) 0 (@Vector.nil Q))
            (Fin.FS index) <
          Vector.nth (@Vector.cons Q 0 0 (@Vector.nil Q))
            (Fin.FS index)) tail_index).
Qed.

Example noncanonical_positive_coefficient_survives_negative_perturbation :
    Vector.Forall (fun coefficient : Q => 0 < coefficient)
      (Vector.map2 Qplus
        (@Vector.cons Q (2#4) 0 (@Vector.nil Q))
        (@Vector.cons Q (-(1#4)) 0 (@Vector.nil Q))).
Proof.
  apply vector_map2_plus_positive.
  - repeat constructor.
  - intro index. refine (Fin.caseS' index (fun index => _) _ _).
    + cbn. reflexivity.
    + intro tail_index. exact (Fin.case0 (fun index =>
        - Vector.nth (@Vector.cons Q (2#4) 0 (@Vector.nil Q))
            (Fin.FS index) <
          Vector.nth (@Vector.cons Q (-(1#4)) 0 (@Vector.nil Q))
            (Fin.FS index)) tail_index).
Qed.

Example twoN_zero_still_not_center :
    ~ Center center_twoN (zvec_zero 1).
Proof. apply center_twoN_does_not_contain_zero. Qed.

Example absorption_twoN_general value offset :
    Center center_twoN value ->
    ClosedLinearization center_twoN offset ->
    Center center_twoN (zvec_add value offset).
Proof.
  apply center_add_closed_linearization, center_twoN_periodic.
Qed.

Example absorption_all_integers value offset :
    Center (@absorption_all_z 1) value ->
    ClosedLinearization (@absorption_all_z 1) offset ->
    Center (@absorption_all_z 1) (zvec_add value offset).
Proof.
  apply center_add_closed_linearization, absorption_all_z_periodic.
Qed.

Example absorption_nonnegative_quadrant value offset :
    Center absorption_n2 value ->
    ClosedLinearization absorption_n2 offset ->
    Center absorption_n2 (zvec_add value offset).
Proof.
  apply center_add_closed_linearization, absorption_n2_periodic.
Qed.

Example absorption_gap_q_zero :
    Center center_gap (center_z1 1).
Proof.
  pose proof (center_add_closed_linearization 1 center_gap
    (center_z1 1) (zvec_zero 1) center_gap_periodic
    center_gap_one_is_central
    (closed_linearization_zero 1 center_gap center_gap_periodic)) as Hcenter.
  rewrite zvec_add_zero_right in Hcenter. exact Hcenter.
Qed.

Example absorption_low_rank value offset :
    Center (zvec_generated [center_z1 2]) value ->
    ClosedLinearization (zvec_generated [center_z1 2]) offset ->
    Center (zvec_generated [center_z1 2]) (zvec_add value offset).
Proof.
  apply center_add_closed_linearization, generated_periodic.
Qed.

Example absorption_set_equality_gap :
    SameSet
      (fun result => exists value offset,
        Center center_gap value /\
        ClosedLinearization center_gap offset /\
        result = zvec_add value offset)
      (Center center_gap).
Proof. apply center_absorbs_closed_linearization, center_gap_periodic. Qed.

Print Assumptions periodic_cone_positive_ray.
Print Assumptions center_add_closed_linearization.
Print Assumptions center_absorbs_closed_linearization.
