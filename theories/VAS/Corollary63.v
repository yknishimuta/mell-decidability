From Coq Require Import List.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Closure.
From Mell.VAS Require Import Runs Transformer SemilinearRelationDecomposition
  AlmostSemilinearProjection.

Definition SemilinearNSet {d} (set : NVec d -> Prop) : Prop := Semilinear set.

Definition NSetProductRelation {d} (source_set target_set : NVec d -> Prop)
    : NRelation d :=
  fun source target => source_set source /\ target_set target.

Lemma semilinear_nset_product_relation : forall d
    (source_set target_set : NVec d -> Prop),
    SemilinearNSet source_set -> SemilinearNSet target_set ->
    SemilinearNRelation (NSetProductRelation source_set target_set).
Proof.
  intros d source_set target_set Hsource Htarget.
  unfold SemilinearNRelation, NSetProductRelation.
  change (Semilinear (fun pair : NVec (d + d) =>
    source_set (Mell.Semilinear.Closure.Vector.shiftin_left d d pair) /\
    target_set (Mell.Semilinear.Closure.Vector.shiftin_right d d pair))).
  exact (semilinear_product d d source_set target_set Hsource Htarget).
Qed.

Lemma almost_semilinear_nset_congr : forall d
    (left right : NVec d -> Prop),
    (forall value, left value <-> right value) ->
    AlmostSemilinearNSet left -> AlmostSemilinearNSet right.
Proof.
  intros d left right Heq [components [Hasym Hcomponents]].
  exists components. split; [exact Hasym|]. intro value.
  rewrite <- Heq. apply Hcomponents.
Qed.

Definition PlainVASPostIntersect {d} (system : PlainVAS d)
    (source_set target_set : NVec d -> Prop) : NVec d -> Prop :=
  fun target => target_set target /\ exists source,
    source_set source /\ PlainVASReach system source target.

Definition PlainVASPreIntersect {d} (system : PlainVAS d)
    (source_set target_set : NVec d -> Prop) : NVec d -> Prop :=
  fun source => source_set source /\ exists target,
    target_set target /\ PlainVASReach system source target.

Theorem corollary_6_3_plain_post_inter_almost_semilinear : forall d
    (system : PlainVAS d) (source_set target_set : NVec d -> Prop),
    SemilinearNSet source_set -> SemilinearNSet target_set ->
    AlmostSemilinearNSet
      (PlainVASPostIntersect system source_set target_set).
Proof.
  intros d system source_set target_set Hsource Htarget.
  pose proof (plain_vas_reach_inter_semilinear d system
    (NSetProductRelation source_set target_set)
    (semilinear_nset_product_relation d source_set target_set Hsource Htarget))
    as Hrelation.
  pose proof (almost_semilinear_nrelation_target_projection d _ Hrelation)
    as Hprojection.
  eapply almost_semilinear_nset_congr; [|exact Hprojection].
  intro target. unfold NRelationTargetProjection, PlainVASPostIntersect,
    NSetProductRelation. split.
  - intros [source [[Hsource' Htarget'] Hreach]].
    split; [exact Htarget'|]. exists source. now split.
  - intros [Htarget' [source [Hsource' Hreach]]].
    exists source. repeat split; assumption.
Qed.

Theorem corollary_6_3_plain_pre_inter_almost_semilinear : forall d
    (system : PlainVAS d) (source_set target_set : NVec d -> Prop),
    SemilinearNSet source_set -> SemilinearNSet target_set ->
    AlmostSemilinearNSet
      (PlainVASPreIntersect system source_set target_set).
Proof.
  intros d system source_set target_set Hsource Htarget.
  pose proof (plain_vas_reach_inter_semilinear d system
    (NSetProductRelation source_set target_set)
    (semilinear_nset_product_relation d source_set target_set Hsource Htarget))
    as Hrelation.
  pose proof (almost_semilinear_nrelation_source_projection d _ Hrelation)
    as Hprojection.
  eapply almost_semilinear_nset_congr; [|exact Hprojection].
  intro source. unfold NRelationSourceProjection, PlainVASPreIntersect,
    NSetProductRelation. split.
  - intros [target [[Hsource' Htarget'] Hreach]].
    split; [exact Hsource'|]. exists target. now split.
  - intros [Hsource' [target [Htarget' Hreach]]].
    exists target. repeat split; assumption.
Qed.
