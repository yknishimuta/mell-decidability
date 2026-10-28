From Coq Require Import Fin Lia List Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Semilinear Require Import LinearEquations Presentation.
From Mell.VAS Require Import Runs Transformer.

Import ListNotations.

Record ProductionTriple (d : nat) := {
  GammaInput : NVec d;
  GammaCapacity : NVec d;
  GammaOutput : NVec d
}.

Arguments GammaInput {d} _.
Arguments GammaCapacity {d} _.
Arguments GammaOutput {d} _.

Definition ValidProductionTriple {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) : Prop :=
  CapacityTransformer system (GammaCapacity gamma)
    (GammaInput gamma) (GammaOutput gamma).

Definition RunOccurs {d} (configuration : NVec d) (run : VASRun d) : Prop :=
  List.In configuration (RunSource run :: RunTargets run).

Definition OmegaGamma {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (run : VASRun d) : Prop :=
  ValidVASRun system run /\
  exists multiplier : nat,
    RunSource run = nvec_add (GammaCapacity gamma)
      (nvec_scale multiplier (GammaInput gamma)) /\
    RunTarget run = nvec_add (GammaCapacity gamma)
      (nvec_scale multiplier (GammaOutput gamma)).

Definition QGamma {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (configuration : NVec d) : Prop :=
  exists multiplier : nat,
    PlainVASReach system
      (nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaInput gamma))) configuration /\
    PlainVASReach system configuration
      (nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaOutput gamma))).

Definition IntraProduction {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (value : NVec d) : Prop :=
  exists multiplier : nat,
    PlainVASReach system
      (nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaInput gamma)))
      (nvec_add (GammaCapacity gamma) value) /\
    PlainVASReach system
      (nvec_add (GammaCapacity gamma) value)
      (nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier (GammaOutput gamma))).

Definition PeriodicNSet {d} (set : NVec d -> Prop) : Prop :=
  set (nvec_zero d) /\
  forall left right, set left -> set right -> set (nvec_add left right).

Lemma omega_gamma_empty_at_capacity : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d),
    OmegaGamma system gamma (EmptyVASRun (GammaCapacity gamma)).
Proof.
  intros d system gamma. split.
  - apply empty_vas_run_valid.
  - exists 0%nat. rewrite !nvec_scale_zero, !nvec_add_zero_right_local.
    split; reflexivity.
Qed.

Ltac nvec_arith :=
  apply (proj1 (Vector.eq_nth_iff nat _ _ _));
  intros index index' Hindex; subst index';
  unfold nvec_add, nvec_scale, nvec_zero;
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl);
  repeat rewrite (nth_map _ _ index index eq_refl);
  repeat rewrite (const_nth nat 0 _ index);
  nia.

Lemma nvec_scale_add_vector : forall d multiplier (left right : NVec d),
    nvec_scale multiplier (nvec_add left right) =
      nvec_add (nvec_scale multiplier left) (nvec_scale multiplier right).
Proof.
  intros d multiplier left right.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Hindex. subst index'.
  unfold nvec_scale, nvec_add.
  repeat rewrite (nth_map _ _ index index eq_refl).
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  repeat rewrite (nth_map _ _ index index eq_refl).
  apply Nat.mul_add_distr_l.
Qed.

Lemma valid_targets_occurrence_reach : forall d (system : PlainVAS d)
    source targets configuration,
    ValidVASTargets system source targets ->
    List.In configuration (source :: targets) ->
    PlainVASReach system source configuration /\
    PlainVASReach system configuration (targets_target source targets).
Proof.
  intros d system source targets. revert source.
  induction targets as [|target tail IH]; intros source configuration Hvalid Hin.
  - cbn in Hin. destruct Hin as [->|[]]. split; constructor.
  - cbn in Hvalid. destruct Hvalid as [Hstep Htail].
    cbn in Hin. destruct Hin as [->|[->|Hin]].
    + split; [constructor|].
      apply plain_vas_reach_step with (target := target).
      * exact Hstep.
      * exact (valid_targets_reach d system target tail Htail).
    + split.
      * apply plain_vas_reach_step with (target := configuration).
        -- exact Hstep.
        -- constructor.
      * exact (valid_targets_reach d system configuration tail Htail).
    + destruct (IH target configuration Htail (or_intror Hin))
        as [Hprefix Hsuffix]. split; [|exact Hsuffix].
      apply plain_vas_reach_step with (target := target); assumption.
Qed.

Lemma valid_run_occurrence_reach : forall d (system : PlainVAS d) run configuration,
    ValidVASRun system run -> RunOccurs configuration run ->
    PlainVASReach system (RunSource run) configuration /\
    PlainVASReach system configuration (RunTarget run).
Proof.
  intros d system [source targets] configuration Hvalid Hoccurs.
  exact (valid_targets_occurrence_reach d system source targets
    configuration Hvalid Hoccurs).
Qed.

Lemma run_target_occurs : forall d (run : VASRun d),
    RunOccurs (RunTarget run) run.
Proof.
  intros d [source targets]. unfold RunOccurs. cbn.
  revert source. induction targets as [|target tail IH]; intro source; cbn.
  - now left.
  - right. apply IH.
Qed.

Lemma run_occurs_concat_left : forall d (left right : VASRun d) configuration,
    RunOccurs configuration left ->
    RunOccurs configuration (VASRunConcat left right).
Proof.
  intros d [left_source left_targets] [right_source right_targets]
    configuration Hoccurs. cbn in *.
  destruct Hoccurs as [Hsource|Htargets].
  - now left.
  - right. apply in_or_app. now left.
Qed.

Lemma run_concat_target : forall d (left right : VASRun d),
    RunTarget left = RunSource right ->
    RunTarget (VASRunConcat left right) = RunTarget right.
Proof.
  intros d [left_source left_targets] [right_source right_targets] Hconnect.
  cbn in *. rewrite targets_target_app, Hconnect. reflexivity.
Qed.

Theorem qgamma_iff_occurs_in_omega : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d) configuration,
    QGamma system gamma configuration <->
    exists run, OmegaGamma system gamma run /\ RunOccurs configuration run.
Proof.
  intros d system gamma configuration. split.
  - intros [multiplier [Hprefix Hsuffix]].
    apply vas_reach_run_iff in Hprefix as
      [prefix [Hprefix_valid [Hprefix_source Hprefix_target]]].
    apply vas_reach_run_iff in Hsuffix as
      [suffix [Hsuffix_valid [Hsuffix_source Hsuffix_target]]].
    assert (Hconnect : RunTarget prefix = RunSource suffix) by congruence.
    exists (VASRunConcat prefix suffix). split.
    + split.
      * now apply vas_run_concat_valid.
      * exists multiplier. split.
        -- cbn. exact Hprefix_source.
        -- rewrite run_concat_target by exact Hconnect. exact Hsuffix_target.
    + apply run_occurs_concat_left. rewrite <- Hprefix_target.
      apply run_target_occurs.
  - intros [run [[Hvalid [multiplier [Hsource Htarget]]] Hoccurs]].
    destruct (valid_run_occurrence_reach d system run configuration
      Hvalid Hoccurs) as [Hprefix Hsuffix].
    exists multiplier. now rewrite <- Hsource, <- Htarget.
Qed.

Lemma qgamma_capacity : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d),
    QGamma system gamma (GammaCapacity gamma).
Proof.
  intros d system gamma. exists 0%nat. rewrite !nvec_scale_zero,
    !nvec_add_zero_right_local. split; constructor.
Qed.

Lemma omega_source_qgamma : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d) run,
    OmegaGamma system gamma run -> QGamma system gamma (RunSource run).
Proof.
  intros d system gamma run Homega. apply qgamma_iff_occurs_in_omega.
  exists run. split; [exact Homega|]. unfold RunOccurs. now left.
Qed.

Lemma omega_target_qgamma : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d) run,
    OmegaGamma system gamma run -> QGamma system gamma (RunTarget run).
Proof.
  intros d system gamma run Homega. apply qgamma_iff_occurs_in_omega.
  exists run. split; [exact Homega|apply run_target_occurs].
Qed.

Lemma omega_occurrence_qgamma : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d) run configuration,
    OmegaGamma system gamma run -> RunOccurs configuration run ->
    QGamma system gamma configuration.
Proof.
  intros d system gamma run configuration Homega Hoccurs.
  apply qgamma_iff_occurs_in_omega. now exists run.
Qed.

Theorem intraproduction_iff_qgamma_offset : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d) value,
    IntraProduction system gamma value <->
    QGamma system gamma (nvec_add (GammaCapacity gamma) value).
Proof. reflexivity. Qed.

Lemma intraproduction_zero : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d),
    IntraProduction system gamma (nvec_zero d).
Proof.
  intros d system gamma. exists 0%nat. rewrite !nvec_scale_zero,
    !nvec_add_zero_right_local. split; constructor.
Qed.

Lemma intraproduction_add : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d) left right,
    IntraProduction system gamma left ->
    IntraProduction system gamma right ->
    IntraProduction system gamma (nvec_add left right).
Proof.
  intros d system gamma left right
    [left_multiplier [Hleft_prefix Hleft_suffix]]
    [right_multiplier [Hright_prefix Hright_suffix]].
  pose proof (capacity_transformer_periodic d system (GammaCapacity gamma))
    as [_ Hadd].
  exists (left_multiplier + right_multiplier)%nat. split.
  - change (CapacityTransformer system (GammaCapacity gamma)
      (nvec_scale (left_multiplier + right_multiplier)%nat (GammaInput gamma))
      (nvec_add left right)).
    rewrite nvec_scale_add_coeff. eapply Hadd; eauto.
  - change (CapacityTransformer system (GammaCapacity gamma)
      (nvec_add left right)
      (nvec_scale (left_multiplier + right_multiplier)%nat (GammaOutput gamma))).
    rewrite nvec_scale_add_coeff. eapply Hadd; eauto.
Qed.

Lemma intraproduction_nsmul : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d) multiplier value,
    IntraProduction system gamma value ->
    IntraProduction system gamma (nvec_scale multiplier value).
Proof.
  intros d system gamma multiplier value Hvalue.
  induction multiplier as [|multiplier IH].
  - rewrite nvec_scale_zero. apply intraproduction_zero.
  - rewrite nvec_scale_succ. now apply intraproduction_add.
Qed.

Theorem intraproduction_periodic : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d),
    PeriodicNSet (IntraProduction system gamma).
Proof.
  intros d system gamma. split.
  - apply intraproduction_zero.
  - intros left right. apply intraproduction_add.
Qed.

Lemma qgamma_add_intraproduction : forall d (system : PlainVAS d)
    (gamma : ProductionTriple d) q h,
    QGamma system gamma q -> IntraProduction system gamma h ->
    QGamma system gamma (nvec_add q h).
Proof.
  intros d system gamma q h
    [q_multiplier [Hq_prefix Hq_suffix]]
    [h_multiplier [Hh_prefix Hh_suffix]].
  exists (q_multiplier + h_multiplier)%nat. split.
  - pose proof (vas_reach_monotone d system _ _
      (nvec_scale q_multiplier (GammaInput gamma)) Hh_prefix) as Hfirst.
    pose proof (vas_reach_monotone d system _ _ h Hq_prefix) as Hsecond.
    assert (Hfirst' : PlainVASReach system
        (nvec_add (GammaCapacity gamma)
          (nvec_scale (q_multiplier + h_multiplier)%nat (GammaInput gamma)))
        (nvec_add (nvec_add (GammaCapacity gamma) h)
          (nvec_scale q_multiplier (GammaInput gamma)))).
    { replace (nvec_add (GammaCapacity gamma)
          (nvec_scale (q_multiplier + h_multiplier)%nat (GammaInput gamma)))
        with (nvec_add
          (nvec_add (GammaCapacity gamma)
            (nvec_scale h_multiplier (GammaInput gamma)))
          (nvec_scale q_multiplier (GammaInput gamma))) by nvec_arith.
      exact Hfirst. }
    assert (Hsecond' : PlainVASReach system
        (nvec_add (nvec_add (GammaCapacity gamma) h)
          (nvec_scale q_multiplier (GammaInput gamma)))
        (nvec_add q h)).
    { replace (nvec_add (nvec_add (GammaCapacity gamma) h)
          (nvec_scale q_multiplier (GammaInput gamma)))
        with (nvec_add
          (nvec_add (GammaCapacity gamma)
            (nvec_scale q_multiplier (GammaInput gamma))) h) by nvec_arith.
      exact Hsecond. }
    eapply PlainVASReach_trans; eauto.
  - pose proof (vas_reach_monotone d system _ _ h Hq_suffix) as Hfirst.
    pose proof (vas_reach_monotone d system _ _
      (nvec_scale q_multiplier (GammaOutput gamma)) Hh_suffix) as Hsecond.
    assert (Hfirst' : PlainVASReach system (nvec_add q h)
        (nvec_add (nvec_add (GammaCapacity gamma)
          (nvec_scale q_multiplier (GammaOutput gamma))) h)) by exact Hfirst.
    assert (Hsecond' : PlainVASReach system
        (nvec_add (nvec_add (GammaCapacity gamma)
          (nvec_scale q_multiplier (GammaOutput gamma))) h)
        (nvec_add (GammaCapacity gamma)
          (nvec_scale (q_multiplier + h_multiplier)%nat (GammaOutput gamma)))).
    { replace (nvec_add (nvec_add (GammaCapacity gamma)
          (nvec_scale q_multiplier (GammaOutput gamma))) h)
        with (nvec_add (nvec_add (GammaCapacity gamma) h)
          (nvec_scale q_multiplier (GammaOutput gamma))) by nvec_arith.
      replace (nvec_add (GammaCapacity gamma)
          (nvec_scale (q_multiplier + h_multiplier)%nat (GammaOutput gamma)))
        with (nvec_add
          (nvec_add (GammaCapacity gamma)
            (nvec_scale h_multiplier (GammaOutput gamma)))
          (nvec_scale q_multiplier (GammaOutput gamma))) by nvec_arith.
      exact Hsecond. }
    eapply PlainVASReach_trans; eauto.
Qed.

Theorem lemma_5_5_qgamma_add_intraproduction : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d) (q h : NVec d),
    ValidProductionTriple system gamma ->
    QGamma system gamma q -> IntraProduction system gamma h ->
    QGamma system gamma (nvec_add q h).
Proof. intros; now apply qgamma_add_intraproduction. Qed.

Corollary lemma_5_5_qgamma_add_intraproduction_nsmul : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d) q h multiplier,
    ValidProductionTriple system gamma ->
    QGamma system gamma q -> IntraProduction system gamma h ->
    QGamma system gamma (nvec_add q (nvec_scale multiplier h)).
Proof.
  intros d system gamma q h multiplier Hvalid Hq Hh.
  eapply lemma_5_5_qgamma_add_intraproduction; eauto.
  now apply intraproduction_nsmul.
Qed.

Theorem lemma_5_6_intraproduction_dominates : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d) (q q' : NVec d),
    ValidProductionTriple system gamma ->
    QGamma system gamma q -> QGamma system gamma q' ->
    nvec_le q q' ->
    exists h : NVec d,
      IntraProduction system gamma h /\ nvec_le q' (nvec_add q h).
Proof.
  intros d system gamma q q' _
    [multiplier [Hq_prefix Hq_suffix]]
    [other_multiplier [Hq'_prefix Hq'_suffix]] Hle.
  set (delta := nvec_sub q' q).
  assert (Hdelta : q' = nvec_add q delta).
  { unfold delta. now apply nvec_sub_exact. }
  set (h := nvec_add delta
    (nvec_scale multiplier
      (nvec_add (GammaInput gamma) (GammaOutput gamma)))).
  exists h. split.
  - exists (multiplier + other_multiplier)%nat. split.
    + pose proof (vas_reach_monotone d system _ _
        (nvec_scale multiplier (GammaInput gamma)) Hq'_prefix) as Hfirst.
      pose proof (vas_reach_monotone d system _ _
        (nvec_add delta (nvec_scale multiplier (GammaInput gamma)))
        Hq_suffix) as Hsecond.
      eapply PlainVASReach_trans with
        (y := nvec_add q' (nvec_scale multiplier (GammaInput gamma))).
      * replace (nvec_add (GammaCapacity gamma)
            (nvec_scale (multiplier + other_multiplier)%nat (GammaInput gamma)))
          with (nvec_add
            (nvec_add (GammaCapacity gamma)
              (nvec_scale other_multiplier (GammaInput gamma)))
            (nvec_scale multiplier (GammaInput gamma))) by nvec_arith.
        exact Hfirst.
      * replace (nvec_add q'
            (nvec_scale multiplier (GammaInput gamma)))
          with (nvec_add q
            (nvec_add delta
              (nvec_scale multiplier (GammaInput gamma))))
          by (rewrite Hdelta; nvec_arith).
        replace (nvec_add (GammaCapacity gamma) h)
          with (nvec_add
            (nvec_add (GammaCapacity gamma)
              (nvec_scale multiplier (GammaOutput gamma)))
            (nvec_add delta
              (nvec_scale multiplier (GammaInput gamma))))
          by (unfold h; rewrite nvec_scale_add_vector; nvec_arith).
        exact Hsecond.
    + pose proof (vas_reach_monotone d system _ _
        (nvec_add delta (nvec_scale multiplier (GammaOutput gamma)))
        Hq_prefix) as Hfirst.
      pose proof (vas_reach_monotone d system _ _
        (nvec_scale multiplier (GammaOutput gamma)) Hq'_suffix) as Hsecond.
      eapply PlainVASReach_trans with
        (y := nvec_add q' (nvec_scale multiplier (GammaOutput gamma))).
      * replace (nvec_add (GammaCapacity gamma) h)
          with (nvec_add
            (nvec_add (GammaCapacity gamma)
              (nvec_scale multiplier (GammaInput gamma)))
            (nvec_add delta
              (nvec_scale multiplier (GammaOutput gamma))))
          by (unfold h; rewrite nvec_scale_add_vector; nvec_arith).
        assert (Hmiddle : nvec_add q
            (nvec_add delta (nvec_scale multiplier (GammaOutput gamma))) =
            nvec_add q' (nvec_scale multiplier (GammaOutput gamma))).
        { rewrite Hdelta. nvec_arith. }
        rewrite <- Hmiddle.
        exact Hfirst.
      * replace (nvec_add (GammaCapacity gamma)
            (nvec_scale (multiplier + other_multiplier)%nat (GammaOutput gamma)))
          with (nvec_add
            (nvec_add (GammaCapacity gamma)
              (nvec_scale other_multiplier (GammaOutput gamma)))
            (nvec_scale multiplier (GammaOutput gamma))) by nvec_arith.
        exact Hsecond.
  - assert (Hequality : nvec_add q h = nvec_add q'
        (nvec_scale multiplier
          (nvec_add (GammaInput gamma) (GammaOutput gamma)))).
    { unfold h. rewrite Hdelta. nvec_arith. }
    rewrite Hequality. apply nvec_le_add_right.
Qed.

Definition BoundedGammaCoordinate {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (index : Fin.t d) : Prop :=
  exists bound : nat, forall configuration,
    QGamma system gamma configuration ->
    (Vector.nth configuration index <= bound)%nat.

Definition FiniteGammaCoordinateValues {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (index : Fin.t d) : Prop :=
  exists values : list nat, forall configuration,
    QGamma system gamma configuration ->
    List.In (Vector.nth configuration index) values.

Lemma in_fold_right_max : forall value values,
    List.In value values ->
    (value <= List.fold_right Nat.max 0%nat values)%nat.
Proof.
  intros value values Hin. induction values as [|head tail IH]; cbn in *.
  - contradiction.
  - destruct Hin as [->|Hin]; [apply Nat.le_max_l|].
    eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Theorem finite_gamma_coordinate_values_iff_bounded : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d) index,
    FiniteGammaCoordinateValues system gamma index <->
    BoundedGammaCoordinate system gamma index.
Proof.
  intros d system gamma index. split.
  - intros [values Hvalues]. exists (List.fold_right Nat.max 0%nat values).
    intros configuration Hconfiguration. apply in_fold_right_max, Hvalues.
    exact Hconfiguration.
  - intros [bound Hbound]. exists (List.seq 0%nat (S bound)).
    intros configuration Hconfiguration. apply in_seq. split; [lia|].
    specialize (Hbound configuration Hconfiguration). lia.
Qed.

Theorem bounded_coordinate_intraproduction_zero : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d) index h,
    BoundedGammaCoordinate system gamma index ->
    IntraProduction system gamma h ->
    Vector.nth h index = 0%nat.
Proof.
  intros d system gamma index h [bound Hbound] Hh.
  pose proof (intraproduction_nsmul d system gamma (S bound) h Hh) as Hscaled.
  pose proof (qgamma_add_intraproduction d system gamma
    (GammaCapacity gamma) (nvec_scale (S bound) h)
    (qgamma_capacity d system gamma) Hscaled) as Hmember.
  specialize (Hbound _ Hmember).
  unfold nvec_add, nvec_scale in Hbound.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (nth_map _ _ index index eq_refl) in Hbound.
  nia.
Qed.
