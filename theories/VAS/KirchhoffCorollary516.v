From Coq Require Import Arith Fin Lia List Vector ZArith QArith Qring.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore
  RationalDefinability RationalHToV.
From Mell.VAS Require Import Runs Transformer RelationCone
  Intraproductions ProductionGraph KirchhoffRelation KirchhoffDefinability
  KirchhoffLemma514 KirchhoffLemma515 AsymptoticRelation
  FiniteKirchhoffRelations.

Import ListNotations.
Open Scope Q_scope.

Theorem capacity_cone_union_kirchhoff : forall d (system : PlainVAS d)
    (capacity : NVec d) (input output : QVec d),
    CapacityTransformerCone system capacity input output <->
    exists gamma : ProductionTriple d,
      ValidProductionTriple system gamma /\
      GammaCapacity gamma = capacity /\
      ProductionKirchhoffRelation system gamma input output.
Proof.
  intros d system capacity input output. split.
  - intro Hcone.
    unfold CapacityTransformerCone in Hcone.
    pose proof (periodic_nrelation_as_z d
      (CapacityTransformer system capacity)
      (capacity_transformer_periodic d system capacity)) as Hperiodic.
    apply (proj1 (periodic_relation_cone_positive_multiple_iff d
      (NRelationAsZ (CapacityTransformer system capacity))
      input output Hperiodic)) in Hcone.
    destruct Hcone as [multiplier [integer_input [integer_output
      [Hpositive [Hmember [Hinput Houtput]]]]]].
    destruct Hmember as [natural_input [natural_output
      [-> [-> Htransformer]]]].
    set (gamma :=
      {| GammaInput := natural_input;
         GammaCapacity := capacity;
         GammaOutput := natural_output |}).
    assert (Hvalid : ValidProductionTriple system gamma).
    { exact Htransformer. }
    pose proof (lemma_5_14_gamma_in_kirchhoff_relation
      d system gamma Hvalid) as Hgamma.
    assert (Hmultiplier_q : 0 < q_of_nat multiplier).
    { unfold q_of_nat, Qlt, inject_Z. cbn. lia. }
    pose proof (production_kirchhoff_positive_scale d system gamma
      (/ q_of_nat multiplier)
      (nvec_to_qvec natural_input) (nvec_to_qvec natural_output)
      (Qinv_lt_0_compat _ Hmultiplier_q) Hgamma) as Hscaled.
    assert (Hinput_nat : QVecEq
        (qvec_scale (q_of_nat multiplier) input)
        (nvec_to_qvec natural_input)).
    { eapply qvec_eq_trans; [exact Hinput|apply nvec_zvec_qvec_commute]. }
    assert (Houtput_nat : QVecEq
        (qvec_scale (q_of_nat multiplier) output)
        (nvec_to_qvec natural_output)).
    { eapply qvec_eq_trans; [exact Houtput|apply nvec_zvec_qvec_commute]. }
    assert (Hscaled_input : QVecEq
        (qvec_scale (/ q_of_nat multiplier) (nvec_to_qvec natural_input))
        input).
    { eapply qvec_eq_trans.
      - apply qvec_eq_scale; [reflexivity|apply qvec_eq_sym; exact Hinput_nat].
      - intro index. unfold qvec_scale. field.
        apply q_of_nat_nonzero_hl. exact Hpositive. }
    assert (Hscaled_output : QVecEq
        (qvec_scale (/ q_of_nat multiplier) (nvec_to_qvec natural_output))
        output).
    { eapply qvec_eq_trans.
      - apply qvec_eq_scale; [reflexivity|apply qvec_eq_sym; exact Houtput_nat].
      - intro index. unfold qvec_scale. field.
        apply q_of_nat_nonzero_hl. exact Hpositive. }
    exists gamma. split; [exact Hvalid|]. split; [reflexivity|].
    apply (proj1 (production_kirchhoff_qvec_ext d system gamma _ input
      _ output Hscaled_input Hscaled_output)). exact Hscaled.
  - intros [gamma [Hvalid [Hcapacity Hrelation]]].
    rewrite <- Hcapacity.
    now apply lemma_5_15_kirchhoff_in_capacity_cone.
Qed.

Lemma qdefinable_empty : forall d,
    QDefinable (fun _ : QVec d => False).
Proof.
  intro d. exists QFBot. split; [reflexivity|]. intro value. reflexivity.
Qed.

Lemma qdefinable_union : forall d (left right : QSet d),
    QDefinable left -> QDefinable right ->
    QDefinable (fun value => left value \/ right value).
Proof.
  intros d left right [left_formula [Hleft_closed Hleft]]
    [right_formula [Hright_closed Hright]].
  exists (QFOr left_formula right_formula). split.
  - cbn. now rewrite Hleft_closed, Hright_closed.
  - intro value. cbn. rewrite <- Hleft, <- Hright. reflexivity.
Qed.

Definition FiniteProductionKirchhoffUnion {d} (system : PlainVAS d)
    (representatives : list (ProductionTriple d)) : QSet (d + d) :=
  fun pair =>
    exists gamma,
      List.In gamma representatives /\
      ProductionKirchhoffRelation system gamma
        (qpair_left pair) (qpair_right pair).

Theorem finite_production_kirchhoff_union_qdefinable : forall d system
    (representatives : list (ProductionTriple d)),
    (forall gamma, List.In gamma representatives ->
      ValidProductionTriple system gamma) ->
    QDefinable (FiniteProductionKirchhoffUnion system representatives).
Proof.
  intros d system representatives. induction representatives as [|gamma tail IH];
    intro Hvalid.
  - exists QFBot. split; [reflexivity|]. intro pair. cbn.
    unfold FiniteProductionKirchhoffUnion. split.
    + intro Hfalse. destruct Hfalse as [gamma Hbody]. exact (proj1 Hbody).
    + intro Hfalse. exact (False_rect _ Hfalse).
  - assert (Hgamma : ValidProductionTriple system gamma).
    { apply Hvalid. now left. }
    assert (Htail : forall gamma0, List.In gamma0 tail ->
        ValidProductionTriple system gamma0).
    { intros gamma0 Hin. apply Hvalid. now right. }
    pose proof (production_kirchhoff_relation_qdefinable
      d system gamma Hgamma) as Hhead.
    pose proof (IH Htail) as Hrest.
    eapply qdefinable_congr; [|apply (qdefinable_union (d + d)
      (fun pair => ProductionKirchhoffRelation system gamma
        (qpair_left pair) (qpair_right pair))
      (FiniteProductionKirchhoffUnion system tail) Hhead Hrest)].
    intro pair. unfold FiniteProductionKirchhoffUnion. split.
    + intros [Hrelation|[gamma0 [Hin Hrelation]]].
      * exists gamma. split; [now left|exact Hrelation].
      * exists gamma0. split; [now right|exact Hrelation].
    + intro Hall. destruct Hall as [gamma0 Hall].
      destruct Hall as [Hin Hrelation]. destruct Hin as [Heq|Hin].
      * subst gamma0. now left.
      * right. exists gamma0. now split.
Qed.

Theorem capacity_transformer_cone_qdefinable : forall d
    (system : PlainVAS d) (capacity : NVec d),
    QDefinable (fun pair : QVec (d + d) =>
      CapacityTransformerCone system capacity
        (qpair_left pair) (qpair_right pair)).
Proof.
  intros d system capacity.
  destruct (finite_production_kirchhoff_relation_representatives
    d system capacity) as [representatives [Hsound Hcover]].
  assert (Hvalid : forall gamma, List.In gamma representatives ->
      ValidProductionTriple system gamma).
  { intros gamma Hin. now destruct (Hsound gamma Hin). }
  pose proof (finite_production_kirchhoff_union_qdefinable
    d system representatives Hvalid) as Hunion.
  eapply qdefinable_congr; [|exact Hunion]. intro pair.
  rewrite capacity_cone_union_kirchhoff. unfold FiniteProductionKirchhoffUnion.
  split.
  - intros [gamma0 [Hin Hrelation]].
    destruct (Hsound gamma0 Hin) as [Hgamma_valid Hcapacity].
    exists gamma0. split; [exact Hgamma_valid|]. split; assumption.
  - intros [gamma [Hgamma_valid [Hcapacity Hrelation]]].
    destruct (Hcover gamma Hgamma_valid Hcapacity)
      as [gamma0 [Hin Hequivalent]].
    exists gamma0. split; [exact Hin|].
    now apply (proj1 (Hequivalent (qpair_left pair) (qpair_right pair))).
Qed.

Theorem corollary_5_16_capacity_transformer_asymptotically_definable :
    forall d (system : PlainVAS d) (capacity : NVec d),
      AsymptoticallyDefinableNRelation
        (CapacityTransformer system capacity).
Proof.
  intros d system capacity. split.
  - apply capacity_transformer_periodic.
  - eapply qdefinable_congr.
    + intro pair. symmetry. apply relation_cone_pairs_unpack.
    + apply capacity_transformer_cone_qdefinable.
Qed.

Theorem transformer_along_run_asymptotically_definable : forall d
    (system : PlainVAS d) (run : VASRun d),
    AsymptoticallyDefinableNRelation
      (TransformerAlongRun system run).
Proof.
  intros d system run.
  apply transformer_along_run_asymptotic_of_capacities.
  intros capacity _. now apply
    corollary_5_16_capacity_transformer_asymptotically_definable.
Qed.
