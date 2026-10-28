From Coq Require Import Fin Lia List Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.VAS Require Import Runs Transformer Intraproductions
  IntraproductionsLemma57.
From Mell.Audit Require Import VASIntraproductionsExamples.

Import ListNotations.
Open Scope Z_scope.

Check unbounded_gamma_coordinate_witness.
Check qgamma_unbounded_strict_comparable_pair.
Check unbounded_coordinate_positive_intraproduction.
Check intraproduction_positive_on_all_unbounded.
Check lemma_5_7_bounded_coordinates_intraproduction.
Check bounded_coordinate_add_intraproduction.
Check lemma_5_7_unbounded_coordinate_growth.

Example lemma_57_dimension_zero (system : PlainVAS 0)
    (gamma : ProductionTriple 0) :
    ValidProductionTriple system gamma ->
    exists h : NVec 0,
      IntraProduction system gamma h /\
      forall index : Fin.t 0,
        BoundedGammaCoordinate system gamma index <->
        Vector.nth h index = 0%nat.
Proof. apply lemma_5_7_bounded_coordinates_intraproduction. Qed.

Definition lemma57_all_bounded_gamma : ProductionTriple 1 :=
  {| GammaInput := intra_n1 0;
     GammaCapacity := intra_n1 2;
     GammaOutput := intra_n1 0 |}.

Example lemma57_all_bounded_valid :
    ValidProductionTriple intra_empty_system lemma57_all_bounded_gamma.
Proof. unfold ValidProductionTriple, CapacityTransformer. cbn. constructor. Qed.

Lemma lemma57_all_bounded_coordinate :
    BoundedGammaCoordinate intra_empty_system
      lemma57_all_bounded_gamma Fin.F1.
Proof.
  exists 2%nat. intros configuration [multiplier [Hprefix _]].
  apply intra_empty_reach_equal in Hprefix. cbn in Hprefix.
  assert (Hcoordinate := f_equal
    (fun value : NVec 1 => Vector.nth value Fin.F1) Hprefix).
  cbn in Hcoordinate. lia.
Qed.

Example lemma57_all_bounded_zero_witness :
    IntraProduction intra_empty_system lemma57_all_bounded_gamma (intra_n1 0) /\
    (BoundedGammaCoordinate intra_empty_system lemma57_all_bounded_gamma Fin.F1
      <-> Vector.nth (intra_n1 0) Fin.F1 = 0%nat).
Proof.
  split; [apply intraproduction_zero|]. split; [intros; reflexivity|].
  intro. exact lemma57_all_bounded_coordinate.
Qed.

Lemma lemma57_unbounded_coordinate :
    ~ BoundedGammaCoordinate intra_plus_one_system
        intra_unbounded_gamma Fin.F1.
Proof.
  intros [bound Hbound].
  specialize (Hbound (intra_n1 (S bound)) (intra_unbounded_qgamma _)).
  cbn in Hbound. lia.
Qed.

Example lemma57_all_unbounded_one_witness :
    IntraProduction intra_plus_one_system intra_unbounded_gamma (intra_n1 1) /\
    ~ BoundedGammaCoordinate intra_plus_one_system
        intra_unbounded_gamma Fin.F1 /\
    (0 < Vector.nth (intra_n1 1) Fin.F1)%nat.
Proof. repeat split; try apply intra_unbounded_hgamma;
  try exact lemma57_unbounded_coordinate; cbn; lia.
Qed.

Lemma lemma57_vertical_second_unbounded :
    ~ BoundedGammaCoordinate intra_vertical_system
        intra_vertical_gamma (Fin.FS Fin.F1).
Proof.
  intros [bound Hbound].
  specialize (Hbound (intra_n2 1 (S bound)) (intra_vertical_qgamma _)).
  cbn in Hbound. lia.
Qed.

Example lemma57_mixed_coordinate_witness :
    IntraProduction intra_vertical_system intra_vertical_gamma (intra_n2 0 1) /\
    Vector.nth (intra_n2 0 1) Fin.F1 = 0%nat /\
    (0 < Vector.nth (intra_n2 0 1) (Fin.FS Fin.F1))%nat.
Proof. repeat split; try apply intra_vertical_hgamma; cbn; lia. Qed.

Example lemma57_mixed_classification :
    BoundedGammaCoordinate intra_vertical_system intra_vertical_gamma Fin.F1 /\
    ~ BoundedGammaCoordinate intra_vertical_system
        intra_vertical_gamma (Fin.FS Fin.F1).
Proof. split; [exact intra_vertical_first_bounded|].
  exact lemma57_vertical_second_unbounded.
Qed.

Example lemma57_strict_comparable_pair :
    exists lower upper,
      QGamma intra_plus_one_system intra_unbounded_gamma lower /\
      QGamma intra_plus_one_system intra_unbounded_gamma upper /\
      nvec_le lower upper /\
      (Vector.nth lower Fin.F1 < Vector.nth upper Fin.F1)%nat.
Proof. apply qgamma_unbounded_strict_comparable_pair.
  exact lemma57_unbounded_coordinate.
Qed.

Definition lemma57_two_axis_system : PlainVAS 2 :=
  [intra_z2 1 0; intra_z2 0 1].

Lemma lemma57_horizontal_step : forall first second,
    List.In (StepAction (intra_n2 first second)
      (intra_n2 (S first) second)) lemma57_two_axis_system.
Proof.
  intros first second. left. apply (proj1 (Vector.eq_nth_iff Z 2 _ _)).
  intros index index' Heq. subst index'.
  refine (Fin.caseS' index (fun index => _) _ _).
  - change (1 = Z.of_nat (S first) - Z.of_nat first)%Z. lia.
  - intro tail. refine (Fin.caseS' tail (fun tail => _) _ _).
    + change (0 = Z.of_nat second - Z.of_nat second)%Z. lia.
    + intro impossible. exact (Fin.case0 (fun index => _) impossible).
Qed.

Lemma lemma57_vertical_step : forall first second,
    List.In (StepAction (intra_n2 first second)
      (intra_n2 first (S second))) lemma57_two_axis_system.
Proof.
  intros first second. right. left.
  apply (proj1 (Vector.eq_nth_iff Z 2 _ _)).
  intros index index' Heq. subst index'.
  refine (Fin.caseS' index (fun index => _) _ _).
  - change (0 = Z.of_nat first - Z.of_nat first)%Z. lia.
  - intro tail. refine (Fin.caseS' tail (fun tail => _) _ _).
    + change (1 = Z.of_nat (S second) - Z.of_nat second)%Z. lia.
    + intro impossible. exact (Fin.case0 (fun index => _) impossible).
Qed.

Lemma lemma57_horizontal_reach : forall value,
    PlainVASReach lemma57_two_axis_system (intra_n2 0 0)
      (intra_n2 value 0).
Proof.
  intro value. induction value as [|value IH]; [constructor|].
  eapply PlainVASReach_trans; [exact IH|].
  apply plain_vas_reach_step with (target := intra_n2 (S value) 0);
    [apply lemma57_horizontal_step|constructor].
Qed.

Lemma lemma57_vertical_reach_from : forall first value,
    PlainVASReach lemma57_two_axis_system (intra_n2 first 0)
      (intra_n2 first value).
Proof.
  intros first value. induction value as [|value IH]; [constructor|].
  eapply PlainVASReach_trans; [exact IH|].
  apply plain_vas_reach_step with (target := intra_n2 first (S value));
    [apply lemma57_vertical_step|constructor].
Qed.

Lemma lemma57_two_axis_reach : forall value,
    PlainVASReach lemma57_two_axis_system (intra_n2 0 0)
      (intra_n2 value value).
Proof. intro value. eapply PlainVASReach_trans.
  - apply lemma57_horizontal_reach.
  - apply lemma57_vertical_reach_from.
Qed.

Definition lemma57_two_axis_gamma : ProductionTriple 2 :=
  {| GammaInput := intra_n2 0 0;
     GammaCapacity := intra_n2 0 0;
     GammaOutput := intra_n2 1 1 |}.

Example lemma57_two_axis_valid :
    ValidProductionTriple lemma57_two_axis_system lemma57_two_axis_gamma.
Proof. unfold ValidProductionTriple, CapacityTransformer. cbn.
  apply lemma57_two_axis_reach.
Qed.

Example lemma57_two_axis_intraproduction :
    IntraProduction lemma57_two_axis_system lemma57_two_axis_gamma
      (intra_n2 1 1).
Proof. exists 1%nat. cbn. split.
  - apply lemma57_two_axis_reach.
  - apply plain_vas_reach_refl.
Qed.

Lemma lemma57_two_axis_qgamma : forall value,
    QGamma lemma57_two_axis_system lemma57_two_axis_gamma
      (intra_n2 value value).
Proof. intro value. exists value. cbn. split.
  - replace (value * 0)%nat with 0%nat by lia.
    apply lemma57_two_axis_reach.
  - replace (value * 1)%nat with value by lia.
    apply plain_vas_reach_refl.
Qed.

Example lemma57_two_axis_both_unbounded :
    ~ BoundedGammaCoordinate lemma57_two_axis_system
        lemma57_two_axis_gamma Fin.F1 /\
    ~ BoundedGammaCoordinate lemma57_two_axis_system
        lemma57_two_axis_gamma (Fin.FS Fin.F1).
Proof.
  split; intros [bound Hbound];
    specialize (Hbound (intra_n2 (S bound) (S bound))
      (lemma57_two_axis_qgamma _)); cbn in Hbound; lia.
Qed.

Example lemma57_capacity_dip_preserved :
    QGamma intra_dip_system intra_dip_gamma (intra_n1 0).
Proof. exact intra_below_capacity_qgamma. Qed.

Print Assumptions qgamma_unbounded_strict_comparable_pair.
Print Assumptions unbounded_coordinate_positive_intraproduction.
Print Assumptions intraproduction_positive_on_all_unbounded.
Print Assumptions lemma_5_7_bounded_coordinates_intraproduction.
