From Coq Require Import Lia QArith Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import LatticeGordanH MathCompBridge Periodic.
From Mell.VAS Require Import RelationCone AsymptoticRelation.

Open Scope Z_scope.

Set Printing Implicit.
Check ZRelationPairs.
Check PeriodicZRelation.
Check RationalRelationCone.
Check periodic_cone_positive_multiple_iff.
Check periodic_relation_cone_compose.
Check qdefinable_relation_compose.
Check lemma_5_1_asymptotic_relation_compose.
Check lemma_5_1_nrelation_compose.
Check transformer_along_run_asymptotic_of_capacities.
Unset Printing Implicit.

Definition asym_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition asym_singleton_relation (value : Z) : ZRelation 1 :=
  fun input output => input = asym_z1 value /\ output = asym_z1 value.

Example nonperiodic_singleton_relation :
    ~ PeriodicZRelation (asym_singleton_relation 1).
Proof.
  intros [Hzero _]. destruct Hzero as [Hzero _].
  pose proof (f_equal (fun vector => Vector.nth vector Fin.F1) Hzero).
  cbn in H. lia.
Qed.

Example mismatched_singletons_do_not_compose : forall input output,
    ~ ZRelCompose (asym_singleton_relation 1)
        (asym_singleton_relation 2) input output.
Proof.
  intros input output [middle [[_ Hmiddle_one] [Hmiddle_two _]]].
  pose proof (eq_trans (eq_sym Hmiddle_one) Hmiddle_two) as Heq.
  pose proof (f_equal (fun vector => Vector.nth vector Fin.F1) Heq).
  cbn in H. lia.
Qed.

Definition asym_scale_relation {d} (factor : Z) : ZRelation d :=
  fun input output => forall index,
    Vector.nth output index = factor * Vector.nth input index.

Lemma asym_scale_relation_periodic : forall d factor,
    PeriodicZRelation (@asym_scale_relation d factor).
Proof.
  intros d factor. split.
  - intro index. unfold zvec_zero. rewrite !const_nth. ring.
  - intros x1 y1 x2 y2 H1 H2 index. unfold zvec_add.
    repeat rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl).
    rewrite H1, H2. ring.
Qed.

Example scale_two_then_three_is_scale_six : forall d input output,
    ZRelCompose (@asym_scale_relation d 2)
      (@asym_scale_relation d 3) input output <->
    @asym_scale_relation d 6 input output.
Proof.
  intros d input output. split.
  - intros [middle [Htwo Hthree]] index. rewrite Hthree, Htwo. ring.
  - intros Hsix. exists (zvec_zsmul 2 input). split; intro index.
    + rewrite zvec_zsmul_nth. ring.
    + rewrite Hsix, zvec_zsmul_nth. ring.
Qed.

Example signed_scale_regression :
    asym_scale_relation 2 (asym_z1 (-3)) (asym_z1 (-6)).
Proof.
  intro index.
  refine (Fin.caseS' index
    (fun index =>
      Vector.nth (asym_z1 (-6)) index =
      2 * Vector.nth (asym_z1 (-3)) index) _ _).
  - cbn. ring.
  - intro impossible.
    exact (Fin.case0
      (fun impossible =>
        Vector.nth (asym_z1 (-6)) (Fin.FS impossible) =
        2 * Vector.nth (asym_z1 (-3)) (Fin.FS impossible))
      impossible).
Qed.

Definition asym_q1 (value : Q) : QVec 1 := fun _ => value.

Example nonnormalized_rational_regression :
    QConeCore.QVecEq (asym_q1 (1 # 2)) (asym_q1 (2 # 4)).
Proof. intro index. reflexivity. Qed.

Example dimension_zero_cone_compose
    (R S : ZRelation 0)
    (HR : PeriodicZRelation R) (HS : PeriodicZRelation S)
    (input output : QVec 0) :
    RationalRelationCone (ZRelCompose R S) input output <->
    exists middle, RationalRelationCone R input middle /\
      RationalRelationCone S middle output.
Proof. apply periodic_relation_cone_compose; assumption. Qed.

Example multiple_capacity_run_transformer_regression : forall d
    (system : Runs.PlainVAS d) (source middle target : NVec d),
    AsymptoticallyDefinableNRelation
      (Transformer.CapacityTransformer system source) ->
    AsymptoticallyDefinableNRelation
      (Transformer.CapacityTransformer system middle) ->
    AsymptoticallyDefinableNRelation
      (Transformer.CapacityTransformer system target) ->
    AsymptoticallyDefinableNRelation
      (Transformer.TransformerAlongRun system
        (@Runs.Build_VASRun d source (middle :: target :: List.nil))).
Proof.
  intros d system source middle target Hsource Hmiddle Htarget.
  apply transformer_along_run_asymptotic_of_capacities.
  intros capacity Hcapacity. cbn in Hcapacity.
  destruct Hcapacity as [Hcapacity|[Hcapacity|[Hcapacity|Hcapacity]]].
  - subst capacity. exact Hsource.
  - subst capacity. exact Hmiddle.
  - subst capacity. exact Htarget.
  - contradiction.
Qed.

Print Assumptions periodic_cone_positive_multiple_iff.
Print Assumptions periodic_relation_cone_compose.
Print Assumptions qdefinable_relation_compose.
Print Assumptions lemma_5_1_asymptotic_relation_compose.
Print Assumptions lemma_5_1_nrelation_compose.
Print Assumptions transformer_along_run_asymptotic_of_capacities.
