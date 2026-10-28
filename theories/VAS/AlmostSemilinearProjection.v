From Coq Require Import Lia List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge Periodic Cone QConeCore RationalDefinability
  ClosedLinearization LatticeGordanPullback.
From Mell.Order Require Import PeriodicOrder.
From Mell.BVAS Require Import RunOrder.
From Mell.VAS Require Import Transformer Intraproductions RelationCone AsymptoticRelation
  PeriodicIntersection AlmostSemilinear.

Import ListNotations.
Open Scope Q_scope.

Definition NSetAsZ {d} (set : NVec d -> Prop) : ZSet d :=
  fun integer => exists natural,
    integer = nvec_to_zvec natural /\ set natural.

Definition AsymptoticallyDefinableNSet {d} (set : NVec d -> Prop) : Prop :=
  PeriodicNSet set /\ QDefinable (Cone (NSetAsZ set)).

Definition NRelationSourceProjection {d} (relation : NRelation d) : NVec d -> Prop :=
  fun source => exists target, relation source target.

Definition NRelationTargetProjection {d} (relation : NRelation d) : NVec d -> Prop :=
  fun target => exists source, relation source target.

Lemma periodic_nset_as_z : forall d (set : NVec d -> Prop),
    PeriodicNSet set -> Periodic (NSetAsZ set).
Proof.
  intros d set [Hzero Hadd]. split.
  - exists (nvec_zero d). split; [symmetry; apply nvec_zero_to_zvec|exact Hzero].
  - intros left right [nleft [Hleft Hnleft]] [nright [Hright Hnright]].
    exists (nvec_add nleft nright). split.
    + subst left right. symmetry. apply nvec_to_zvec_add.
    + now apply Hadd.
Qed.

Lemma periodic_source_projection : forall d (relation : NRelation d),
    PeriodicNRelation relation ->
    PeriodicNSet (NRelationSourceProjection relation).
Proof.
  intros d relation [Hzero Hadd]. split.
  - exists (nvec_zero d). exact Hzero.
  - intros left right [left' Hleft] [right' Hright].
    exists (nvec_add left' right'). now apply Hadd.
Qed.

Lemma periodic_target_projection : forall d (relation : NRelation d),
    PeriodicNRelation relation ->
    PeriodicNSet (NRelationTargetProjection relation).
Proof.
  intros d relation [Hzero Hadd]. split.
  - exists (nvec_zero d). exact Hzero.
  - intros left right [left' Hleft] [right' Hright].
    exists (nvec_add left' right'). now apply Hadd.
Qed.

Lemma positive_nat_inverse_scale : forall d multiplier (value : NVec d),
    (0 < multiplier)%nat ->
    QVecEq
      (qvec_scale (q_of_nat multiplier)
        (qvec_scale (/ q_of_nat multiplier) (nvec_to_qvec value)))
      (zvec_to_qvec (nvec_to_zvec value)).
Proof.
  intros d multiplier value Hpositive index.
  unfold qvec_scale, nvec_to_qvec, zvec_to_qvec, nvec_to_zvec.
  rewrite (Vector.nth_map _ _ index index eq_refl).
  unfold q_of_nat.
  field. intro Hzero.
  apply (proj1 (inject_Z_injective (Z.of_nat multiplier) 0%Z)) in Hzero.
  lia.
Qed.

Theorem source_projection_cone : forall d (relation : NRelation d)
    (point : QVec d),
    PeriodicNRelation relation ->
    (Cone (NSetAsZ (NRelationSourceProjection relation)) point <->
     exists target,
       RationalRelationCone (NRelationAsZ relation) point target).
Proof.
  intros d relation point Hperiodic. split.
  - intro Hcone.
    apply (proj1 (periodic_cone_positive_multiple_iff d
      (NSetAsZ (NRelationSourceProjection relation)) point
      (periodic_nset_as_z d _ (periodic_source_projection d relation Hperiodic))))
      in Hcone.
    destruct Hcone as [multiplier [integer_source
      [Hpositive [[source [Hsource [target Hrelation]]] Hpoint]]]].
    subst integer_source.
    exists (qvec_scale (/ q_of_nat multiplier) (nvec_to_qvec target)).
    apply (proj2 (periodic_relation_cone_positive_multiple_iff d
      (NRelationAsZ relation) point _
      (periodic_nrelation_as_z d relation Hperiodic))).
    exists multiplier, (nvec_to_zvec source), (nvec_to_zvec target).
    repeat split; try assumption.
    + exists source, target. repeat split; try reflexivity. exact Hrelation.
    + apply positive_nat_inverse_scale. exact Hpositive.
  - intros [target Hcone].
    apply (proj2 (periodic_cone_positive_multiple_iff d
      (NSetAsZ (NRelationSourceProjection relation)) point
      (periodic_nset_as_z d _ (periodic_source_projection d relation Hperiodic)))).
    apply (proj1 (periodic_relation_cone_positive_multiple_iff d
      (NRelationAsZ relation) point target
      (periodic_nrelation_as_z d relation Hperiodic))) in Hcone.
    destruct Hcone as [multiplier [integer_source [integer_target
      [Hpositive [Hrelation [Hsource Htarget]]]]]].
    destruct Hrelation as [source [target' [Esource [Etarget Hrelation]]]].
    exists multiplier, integer_source. repeat split; try assumption.
    exists source. split; [exact Esource|]. exists target'. exact Hrelation.
Qed.

Theorem target_projection_cone : forall d (relation : NRelation d)
    (point : QVec d),
    PeriodicNRelation relation ->
    (Cone (NSetAsZ (NRelationTargetProjection relation)) point <->
     exists source,
       RationalRelationCone (NRelationAsZ relation) source point).
Proof.
  intros d relation point Hperiodic. split.
  - intro Hcone.
    apply (proj1 (periodic_cone_positive_multiple_iff d
      (NSetAsZ (NRelationTargetProjection relation)) point
      (periodic_nset_as_z d _ (periodic_target_projection d relation Hperiodic))))
      in Hcone.
    destruct Hcone as [multiplier [integer_target
      [Hpositive [[target [Htarget [source Hrelation]]] Hpoint]]]].
    subst integer_target.
    exists (qvec_scale (/ q_of_nat multiplier) (nvec_to_qvec source)).
    apply (proj2 (periodic_relation_cone_positive_multiple_iff d
      (NRelationAsZ relation) _ point
      (periodic_nrelation_as_z d relation Hperiodic))).
    exists multiplier, (nvec_to_zvec source), (nvec_to_zvec target).
    repeat split; try assumption.
    + exists source, target. repeat split; try reflexivity. exact Hrelation.
    + apply positive_nat_inverse_scale. exact Hpositive.
  - intros [source Hcone].
    apply (proj2 (periodic_cone_positive_multiple_iff d
      (NSetAsZ (NRelationTargetProjection relation)) point
      (periodic_nset_as_z d _ (periodic_target_projection d relation Hperiodic)))).
    apply (proj1 (periodic_relation_cone_positive_multiple_iff d
      (NRelationAsZ relation) source point
      (periodic_nrelation_as_z d relation Hperiodic))) in Hcone.
    destruct Hcone as [multiplier [integer_source [integer_target
      [Hpositive [Hrelation [Hsource Htarget]]]]]].
    destruct Hrelation as [source' [target [Esource [Etarget Hrelation]]]].
    exists multiplier, integer_target. repeat split; try assumption.
    exists target. split; [exact Etarget|]. exists source'. exact Hrelation.
Qed.

Lemma qpair_left_coordinate : forall d (pair : QVec (d + d)) index,
    qpair_left pair index == pair (Fin.L d index).
Proof.
  intros d pair index. unfold qpair_left. apply qvec_left_nth.
Qed.

Lemma qpair_right_coordinate : forall d (pair : QVec (d + d)) index,
    qpair_right pair index == pair (Fin.R d index).
Proof.
  intros d pair index. unfold qpair_right. apply qvec_right_nth.
Qed.

Theorem asymptotically_definable_nrelation_source_projection : forall d
    (relation : NRelation d),
    AsymptoticallyDefinableNRelation relation ->
    AsymptoticallyDefinableNSet (NRelationSourceProjection relation).
Proof.
  intros d relation [Hperiodic Hdef]. split.
  - now apply periodic_source_projection.
  - pose proof (qdefinable_projection (d + d) d (fun index => Fin.L d index)
      (RelationConePairs (NRelationAsZ relation)) Hdef) as Hprojection.
    eapply qdefinable_congr; [|exact Hprojection]. intro point.
    rewrite source_projection_cone by exact Hperiodic. split.
    + intros [pair [Hpair Hcoordinates]].
      exists (qpair_right pair). unfold RelationConePairs in Hpair.
      unfold RationalRelationCone.
      assert (Heq : QVecEq pair (qpair_pack point (qpair_right pair))).
      { eapply qvec_eq_trans; [apply qpair_pack_split|].
        apply qpair_pack_ext.
        - intro index. transitivity (pair (Fin.L d index)).
          + apply qpair_left_coordinate.
          + symmetry. exact (Hcoordinates index).
        - apply qvec_eq_refl. }
      exact (proj1 (cone_qvec_ext_relation (d + d)
        (ZRelationPairs (NRelationAsZ relation)) pair
        (qpair_pack point (qpair_right pair)) Heq) Hpair).
    + intros [target Hrelation]. exists (qpair_pack point target). split.
      * unfold RelationConePairs. exact Hrelation.
      * intro index. transitivity (qpair_left (qpair_pack point target) index).
        -- symmetry. apply qpair_left_pack.
        -- apply qpair_left_coordinate.
Qed.

Theorem asymptotically_definable_nrelation_target_projection : forall d
    (relation : NRelation d),
    AsymptoticallyDefinableNRelation relation ->
    AsymptoticallyDefinableNSet (NRelationTargetProjection relation).
Proof.
  intros d relation [Hperiodic Hdef]. split.
  - now apply periodic_target_projection.
  - pose proof (qdefinable_projection (d + d) d (fun index => Fin.R d index)
      (RelationConePairs (NRelationAsZ relation)) Hdef) as Hprojection.
    eapply qdefinable_congr; [|exact Hprojection]. intro point.
    rewrite target_projection_cone by exact Hperiodic. split.
    + intros [pair [Hpair Hcoordinates]].
      exists (qpair_left pair). unfold RelationConePairs in Hpair.
      unfold RationalRelationCone.
      assert (Heq : QVecEq pair (qpair_pack (qpair_left pair) point)).
      { eapply qvec_eq_trans; [apply qpair_pack_split|].
        apply qpair_pack_ext.
        - apply qvec_eq_refl.
        - intro index. transitivity (pair (Fin.R d index)).
          + apply qpair_right_coordinate.
          + symmetry. exact (Hcoordinates index). }
      exact (proj1 (cone_qvec_ext_relation (d + d)
        (ZRelationPairs (NRelationAsZ relation)) pair
        (qpair_pack (qpair_left pair) point) Heq) Hpair).
    + intros [source Hrelation]. exists (qpair_pack source point). split.
      * unfold RelationConePairs. exact Hrelation.
      * intro index. transitivity (qpair_right (qpair_pack source point) index).
        -- symmetry. apply qpair_right_pack.
        -- apply qpair_right_coordinate.
Qed.

Record AlmostSemilinearNComponentSet (d : nat) := {
  AlmostSetBase : NVec d;
  AlmostSetPeriod : NVec d -> Prop
}.

Arguments AlmostSetBase {d} _.
Arguments AlmostSetPeriod {d} _ _.

Definition AlmostSemilinearNSet {d} (set : NVec d -> Prop) : Prop :=
  exists components : list (AlmostSemilinearNComponentSet d),
    List.Forall (fun component =>
      AsymptoticallyDefinableNSet (AlmostSetPeriod component)) components /\
    forall value,
      set value <-> exists component,
        List.In component components /\
        exists offset,
          AlmostSetPeriod component offset /\
          value = nvec_add (AlmostSetBase component) offset.

Definition project_source_component {d} (component : AlmostSemilinearNComponent d)
    : AlmostSemilinearNComponentSet d :=
  {| AlmostSetBase := AlmostBaseInput component;
     AlmostSetPeriod := NRelationSourceProjection (AlmostPeriodRelation component) |}.

Definition project_target_component {d} (component : AlmostSemilinearNComponent d)
    : AlmostSemilinearNComponentSet d :=
  {| AlmostSetBase := AlmostBaseOutput component;
     AlmostSetPeriod := NRelationTargetProjection (AlmostPeriodRelation component) |}.

Theorem almost_semilinear_nrelation_source_projection : forall d
    (relation : NRelation d),
    AlmostSemilinearNRelation relation ->
    AlmostSemilinearNSet (NRelationSourceProjection relation).
Proof.
  intros d relation [components [Hasym Hrelation]].
  exists (List.map project_source_component components). split.
  - apply List.Forall_forall. intros projected Hin.
    apply in_map_iff in Hin as [component [<- Hin]]. cbn.
    apply asymptotically_definable_nrelation_source_projection.
    exact (proj1 (List.Forall_forall _ _) Hasym component Hin).
  - intro source. split.
    + intros [target Hrel]. apply Hrelation in Hrel.
      destruct Hrel as [component [Hin [oi [oo [Hp [Hs Ht]]]]]].
      exists (project_source_component component). split; [now apply in_map|].
      exists oi. split; [exists oo; exact Hp|exact Hs].
    + intros [projected [Hin [offset [Hp Hs]]]].
      apply in_map_iff in Hin as [component [<- Hin]]. cbn in *.
      destruct Hp as [output Hp]. exists (nvec_add (AlmostBaseOutput component) output).
      apply Hrelation. exists component. split; [exact Hin|].
      exists offset, output. repeat split; assumption.
Qed.

Theorem almost_semilinear_nrelation_target_projection : forall d
    (relation : NRelation d),
    AlmostSemilinearNRelation relation ->
    AlmostSemilinearNSet (NRelationTargetProjection relation).
Proof.
  intros d relation [components [Hasym Hrelation]].
  exists (List.map project_target_component components). split.
  - apply List.Forall_forall. intros projected Hin.
    apply in_map_iff in Hin as [component [<- Hin]]. cbn.
    apply asymptotically_definable_nrelation_target_projection.
    exact (proj1 (List.Forall_forall _ _) Hasym component Hin).
  - intro target. split.
    + intros [source Hrel]. apply Hrelation in Hrel.
      destruct Hrel as [component [Hin [oi [oo [Hp [Hs Ht]]]]]].
      exists (project_target_component component). split; [now apply in_map|].
      exists oo. split; [exists oi; exact Hp|exact Ht].
    + intros [projected [Hin [offset [Hp Ht]]]].
      apply in_map_iff in Hin as [component [<- Hin]]. cbn in *.
      destruct Hp as [input Hp]. exists (nvec_add (AlmostBaseInput component) input).
      apply Hrelation. exists component. split; [exact Hin|].
      exists input, offset. repeat split; assumption.
Qed.

Theorem almost_semilinear_nset_finite_union : forall d
    (sets : list (NVec d -> Prop)),
    List.Forall AlmostSemilinearNSet sets ->
    AlmostSemilinearNSet (fun value => exists set,
      List.In set sets /\ set value).
Proof.
  intros d sets Hsets. induction Hsets as [|head rest Hhead Hrest IHrest].
  - exists []. split; [constructor|]. intro value. split.
    + intros [set [Hin _]]. inversion Hin.
    + intros [component [Hin _]]. inversion Hin.
  - destruct Hhead as [head_components [Hhead_asym Hhead]].
    destruct IHrest as [tail_components [Htail_asym Htail]].
    exists (head_components ++ tail_components). split.
    + now apply List.Forall_app.
    + intro value. split.
      * intros [chosen [[<-|Hin] Hvalue]].
        -- apply Hhead in Hvalue.
           destruct Hvalue as [component [Hcomponent Hoffset]].
           exists component. split; [now apply in_or_app; left|exact Hoffset].
        -- assert (Hunion : exists chosen,
              List.In chosen rest /\ chosen value).
           { exists chosen. now split. }
           apply Htail in Hunion.
           destruct Hunion as [component [Hcomponent Hoffset]].
           exists component. split; [now apply in_or_app; right|exact Hoffset].
      * intros [component [Hcomponent Hoffset]].
        apply in_app_or in Hcomponent as [Hcomponent|Hcomponent].
        -- exists head. split; [now left|]. apply Hhead.
           now exists component.
        -- assert (Hcomponent' : exists component,
              List.In component tail_components /\
              exists offset,
                AlmostSetPeriod component offset /\
                value = nvec_add (AlmostSetBase component) offset).
           { exists component. now split. }
           apply Htail in Hcomponent' as Hvalue.
           destruct Hvalue as [chosen [Hin Hchosen]].
           exists chosen. split; [now right|exact Hchosen].
Qed.
