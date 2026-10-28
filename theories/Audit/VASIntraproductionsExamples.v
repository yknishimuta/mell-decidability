From Coq Require Import Fin Lia List Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Semilinear Require Import LinearEquations Presentation.
From Mell.VAS Require Import Runs Transformer Intraproductions.

Import ListNotations.
Open Scope Z_scope.

Check ProductionTriple.
Check OmegaGamma.
Check QGamma.
Check IntraProduction.
Check omega_gamma_empty_at_capacity.
Check qgamma_iff_occurs_in_omega.
Check intraproduction_periodic.
Check lemma_5_5_qgamma_add_intraproduction.
Check lemma_5_6_intraproduction_dominates.
Check finite_gamma_coordinate_values_iff_bounded.
Check bounded_coordinate_intraproduction_zero.

Definition intra_n1 (value : nat) : NVec 1 :=
  @Vector.cons nat value 0 (@Vector.nil nat).

Definition intra_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition intra_n2 (first second : nat) : NVec 2 :=
  @Vector.cons nat first 1
    (@Vector.cons nat second 0 (@Vector.nil nat)).

Definition intra_z2 (first second : Z) : ZVec 2 :=
  @Vector.cons Z first 1
    (@Vector.cons Z second 0 (@Vector.nil Z)).

Definition intra_plus_one_system : PlainVAS 1 := [intra_z1 1].

Lemma intra_plus_one_step : forall start,
    List.In (StepAction (intra_n1 start) (intra_n1 (S start)))
      intra_plus_one_system.
Proof.
  intro start. cbn. left. apply (proj1 (Vector.eq_nth_iff Z 1 _ _)).
  intros index index' Hindex. subst index'.
  refine (Fin.caseS' index (fun index => _) _ _).
  - change (1 = Z.of_nat (S start) - Z.of_nat start)%Z. lia.
  - intros tail. exact (Fin.case0 (fun index => _) tail).
Qed.

Lemma intra_plus_one_reach : forall start steps,
    PlainVASReach intra_plus_one_system
      (intra_n1 start) (intra_n1 (start + steps)).
Proof.
  intros start steps. revert start.
  induction steps as [|steps IH]; intro start.
  - replace (start + 0)%nat with start by lia. constructor.
  - apply plain_vas_reach_step with (target := intra_n1 (S start)).
    + apply intra_plus_one_step.
    + replace (start + S steps)%nat with (S start + steps)%nat by lia.
      apply IH.
Qed.

Definition intra_unbounded_gamma : ProductionTriple 1 :=
  {| GammaInput := intra_n1 0;
     GammaCapacity := intra_n1 0;
     GammaOutput := intra_n1 1 |}.

Example intra_omega_zero_run :
    OmegaGamma intra_plus_one_system intra_unbounded_gamma
      (EmptyVASRun (GammaCapacity intra_unbounded_gamma)).
Proof. apply omega_gamma_empty_at_capacity. Qed.

Example intra_unbounded_gamma_valid :
    ValidProductionTriple intra_plus_one_system intra_unbounded_gamma.
Proof. unfold ValidProductionTriple, CapacityTransformer. cbn.
  exact (intra_plus_one_reach 0 1).
Qed.

Example intra_unbounded_qgamma : forall value,
    QGamma intra_plus_one_system intra_unbounded_gamma (intra_n1 value).
Proof.
  intro value. exists value. cbn. split.
  - replace (value * 0)%nat with 0%nat by lia.
    exact (intra_plus_one_reach 0 value).
  - unfold intra_n1. replace (value * 1)%nat with value by lia.
    apply plain_vas_reach_refl.
Qed.

Example intra_unbounded_hgamma : forall value,
    IntraProduction intra_plus_one_system intra_unbounded_gamma (intra_n1 value).
Proof.
  intro value. exists value. cbn. split.
  - replace (value * 0)%nat with 0%nat by lia.
    exact (intra_plus_one_reach 0 value).
  - unfold intra_n1. replace (value * 1)%nat with value by lia.
    apply plain_vas_reach_refl.
Qed.

Example intra_one_two_and_sum :
    IntraProduction intra_plus_one_system intra_unbounded_gamma (intra_n1 1) /\
    IntraProduction intra_plus_one_system intra_unbounded_gamma (intra_n1 2) /\
    IntraProduction intra_plus_one_system intra_unbounded_gamma (intra_n1 3).
Proof. repeat split; apply intra_unbounded_hgamma. Qed.

Definition intra_plus_one_run : VASRun 1 :=
  {| RunSource := intra_n1 0; RunTargets := [intra_n1 1] |}.

Example intra_omega_common_multiplier :
    OmegaGamma intra_plus_one_system intra_unbounded_gamma intra_plus_one_run.
Proof.
  split.
  - cbn. auto.
  - exists 1%nat. cbn. split; reflexivity.
Qed.

Example intra_omega_source_target_in_qgamma :
    QGamma intra_plus_one_system intra_unbounded_gamma
      (RunSource intra_plus_one_run) /\
    QGamma intra_plus_one_system intra_unbounded_gamma
      (RunTarget intra_plus_one_run).
Proof. split; [apply omega_source_qgamma|apply omega_target_qgamma];
  exact intra_omega_common_multiplier.
Qed.

Definition intra_plus_two_run : VASRun 1 :=
  {| RunSource := intra_n1 0;
     RunTargets := [intra_n1 1; intra_n1 2] |}.

Example intra_omega_intermediate_configuration :
    QGamma intra_plus_one_system intra_unbounded_gamma (intra_n1 1).
Proof.
  eapply omega_occurrence_qgamma with (run := intra_plus_two_run).
  - split.
    + change (List.In (StepAction (intra_n1 0) (intra_n1 1))
          intra_plus_one_system /\
        List.In (StepAction (intra_n1 1) (intra_n1 2))
          intra_plus_one_system /\ True).
      repeat split; apply intra_plus_one_step.
    + exists 2%nat. cbn. unfold intra_n1. split; f_equal; lia.
  - cbn. auto.
Qed.

Definition intra_zero_system : PlainVAS 1 := [intra_z1 0].
Definition intra_zero_gamma : ProductionTriple 1 :=
  {| GammaInput := intra_n1 0;
     GammaCapacity := intra_n1 2;
     GammaOutput := intra_n1 0 |}.
Definition intra_zero_action_run : VASRun 1 :=
  {| RunSource := intra_n1 2; RunTargets := [intra_n1 2] |}.

Example intra_zero_action_omega :
    OmegaGamma intra_zero_system intra_zero_gamma intra_zero_action_run.
Proof.
  split.
  - cbn. split.
    + left. apply (proj1 (Vector.eq_nth_iff Z 1 _ _)).
      intros index index' Hindex. subst index'.
      refine (Fin.caseS' index (fun index => _) _ _).
      * change (0 = Z.of_nat 2 - Z.of_nat 2)%Z. lia.
      * intros impossible. exact (Fin.case0 (fun index => _) impossible).
    + exact I.
  - exists 0%nat. cbn. split; reflexivity.
Qed.

Definition intra_empty_system : PlainVAS 1 := [].
Definition intra_invalid_gamma : ProductionTriple 1 :=
  {| GammaInput := intra_n1 0;
     GammaCapacity := intra_n1 0;
     GammaOutput := intra_n1 1 |}.

Lemma intra_empty_reach_equal : forall source target,
    PlainVASReach intra_empty_system source target -> source = target.
Proof.
  intros source target Hreach. induction Hreach.
  - reflexivity.
  - cbn in H. contradiction.
Qed.

Example intra_invalid_gamma_rejected :
    ~ ValidProductionTriple intra_empty_system intra_invalid_gamma.
Proof.
  unfold ValidProductionTriple, CapacityTransformer. cbn.
  intro Hreach. apply intra_empty_reach_equal in Hreach. discriminate.
Qed.

Definition intra_vertical_system : PlainVAS 2 := [intra_z2 0 1].

Lemma intra_vertical_reach : forall first start steps,
    PlainVASReach intra_vertical_system
      (intra_n2 first start) (intra_n2 first (start + steps)).
Proof.
  intros first start steps. revert start.
  induction steps as [|steps IH]; intro start.
  - replace (start + 0)%nat with start by lia. constructor.
  - apply plain_vas_reach_step with (target := intra_n2 first (S start)).
    + cbn. left. apply (proj1 (Vector.eq_nth_iff Z 2 _ _)).
      intros index index' Hindex. subst index'.
      refine (Fin.caseS' index (fun index => _) _ _).
      * change (0 = Z.of_nat first - Z.of_nat first)%Z. lia.
      * intros tail. refine (Fin.caseS' tail (fun tail => _) _ _).
        -- change (1 = Z.of_nat (S start) - Z.of_nat start)%Z. lia.
        -- intros impossible. exact (Fin.case0 (fun index => _) impossible).
    + replace (start + S steps)%nat with (S start + steps)%nat by lia.
      apply IH.
Qed.

Lemma intra_vertical_reach_first : forall source target,
    PlainVASReach intra_vertical_system source target ->
    Vector.nth target Fin.F1 = Vector.nth source Fin.F1.
Proof.
  intros source target Hreach. induction Hreach.
  - reflexivity.
  - cbn in H. destruct H as [Haction|[]].
    assert (Hcoordinate := f_equal
      (fun value : ZVec 2 => Vector.nth value Fin.F1) Haction).
    unfold StepAction, zvec_sub_run, nvec_to_zvec in Hcoordinate.
    repeat rewrite (nth_map2 Z.sub _ _ Fin.F1 Fin.F1 Fin.F1
      eq_refl eq_refl) in Hcoordinate.
    repeat rewrite (nth_map Z.of_nat _ Fin.F1 Fin.F1 eq_refl)
      in Hcoordinate.
    cbn in Hcoordinate. lia.
Qed.

Definition intra_vertical_gamma : ProductionTriple 2 :=
  {| GammaInput := intra_n2 0 0;
     GammaCapacity := intra_n2 1 0;
     GammaOutput := intra_n2 0 1 |}.

Example intra_vertical_gamma_valid :
    ValidProductionTriple intra_vertical_system intra_vertical_gamma.
Proof. unfold ValidProductionTriple, CapacityTransformer. cbn.
  exact (intra_vertical_reach 1 0 1).
Qed.

Example intra_vertical_qgamma : forall value,
    QGamma intra_vertical_system intra_vertical_gamma (intra_n2 1 value).
Proof.
  intro value. exists value. cbn. split.
  - replace (value * 0)%nat with 0%nat by lia.
    exact (intra_vertical_reach 1 0 value).
  - unfold intra_n2. replace (value * 0)%nat with 0%nat by lia.
    replace (value * 1)%nat with value by lia.
    apply plain_vas_reach_refl.
Qed.

Example intra_vertical_hgamma : forall value,
    IntraProduction intra_vertical_system intra_vertical_gamma (intra_n2 0 value).
Proof.
  intro value. exists value. cbn. split.
  - replace (value * 0)%nat with 0%nat by lia.
    exact (intra_vertical_reach 1 0 value).
  - unfold intra_n2. replace (value * 0)%nat with 0%nat by lia.
    replace (value * 1)%nat with value by lia.
    apply plain_vas_reach_refl.
Qed.

Example intra_vertical_first_bounded :
    BoundedGammaCoordinate intra_vertical_system intra_vertical_gamma Fin.F1.
Proof.
  exists 1%nat. intros configuration
    [multiplier [Hprefix _]].
  pose proof (intra_vertical_reach_first _ _ Hprefix) as Hfirst.
  cbn in Hfirst. lia.
Qed.

Example intra_vertical_h_first_zero : forall h,
    IntraProduction intra_vertical_system intra_vertical_gamma h ->
    Vector.nth h Fin.F1 = 0%nat.
Proof.
  intros h Hh. eapply bounded_coordinate_intraproduction_zero;
    eauto using intra_vertical_first_bounded.
Qed.

Example intra_vertical_lemma_5_6 :
    exists h,
      IntraProduction intra_vertical_system intra_vertical_gamma h /\
      nvec_le (intra_n2 1 2) (nvec_add (intra_n2 1 1) h).
Proof.
  eapply lemma_5_6_intraproduction_dominates.
  - exact intra_vertical_gamma_valid.
  - apply intra_vertical_qgamma.
  - apply intra_vertical_qgamma.
  - intro index. refine (Fin.caseS' index (fun index =>
      Vector.nth (intra_n2 1 1) index <=
      Vector.nth (intra_n2 1 2) index)%nat _ _).
    + cbn. lia.
    + intro tail. refine (Fin.caseS' tail (fun tail =>
        Vector.nth (intra_n2 1 1) (Fin.FS tail) <=
        Vector.nth (intra_n2 1 2) (Fin.FS tail))%nat _ _).
      * cbn. lia.
      * intro impossible. exact (Fin.case0 (fun impossible =>
          (Vector.nth (intra_n2 1 1) (Fin.FS (Fin.FS impossible)) <=
           Vector.nth (intra_n2 1 2) (Fin.FS (Fin.FS impossible)))%nat)
          impossible).
Qed.

Definition intra_dip_system : PlainVAS 1 := [intra_z1 (-1); intra_z1 1].
Definition intra_dip_gamma : ProductionTriple 1 :=
  {| GammaInput := intra_n1 0;
     GammaCapacity := intra_n1 1;
     GammaOutput := intra_n1 0 |}.

Example intra_below_capacity_qgamma :
    QGamma intra_dip_system intra_dip_gamma (intra_n1 0).
Proof.
  exists 0%nat. cbn. split.
  - apply plain_vas_reach_step with (target := intra_n1 0); [cbn; auto|constructor].
  - apply plain_vas_reach_step with (target := intra_n1 1); [cbn; auto|constructor].
Qed.

Example intra_dimension_zero_periodic (system : PlainVAS 0)
    (gamma : ProductionTriple 0) :
    PeriodicNSet (IntraProduction system gamma).
Proof. apply intraproduction_periodic. Qed.

Example intra_lemma_5_6_reflexive_case :
    exists h,
      IntraProduction intra_plus_one_system intra_unbounded_gamma h /\
      nvec_le (intra_n1 2) (nvec_add (intra_n1 2) h).
Proof.
  eapply lemma_5_6_intraproduction_dominates.
  - exact intra_unbounded_gamma_valid.
  - apply intra_unbounded_qgamma.
  - apply intra_unbounded_qgamma.
  - apply nvec_le_refl.
Qed.

Print Assumptions qgamma_iff_occurs_in_omega.
Print Assumptions intraproduction_periodic.
Print Assumptions lemma_5_5_qgamma_add_intraproduction.
Print Assumptions lemma_5_6_intraproduction_dominates.
Print Assumptions finite_gamma_coordinate_values_iff_bounded.
Print Assumptions bounded_coordinate_intraproduction_zero.
