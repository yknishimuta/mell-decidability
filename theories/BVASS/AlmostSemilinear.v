From Coq Require Import Fin Lia List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation Closure LinearEquations.
From Mell.Geometry Require Import MathCompBridge Cone QConeCore
  RationalDefinability.
From Mell.VAS Require Import StatefulVAS Intraproductions RelationCone
  AsymptoticRelation AlmostSemilinearProjection Corollary63
  StatefulAlmostSemilinear.
From Mell.BVASS Require Import Stateful Extend BoundedBranching
  VASSSection BoundedVASSSection.

Import ListNotations.
Module StdVector := Coq.Vectors.Vector.
Open Scope Q_scope.

Definition VASSSectionOf {d q} (B : SBVAS d q)
    (W : VASSSection d q) : Prop :=
  forall state counters,
    SReach B state counters <-> VASSSectionReach W state counters.

Theorem bvass_reach_is_vass_section :
  forall d q (B : SBVAS d q),
    exists W : VASSSection d q,
      VASSSectionOf B W.
Proof.
  intros d q B.
  destruct (lemma_9_reach_bounded_branching_iff d q B)
    as [F [bound [Hreachable Hbounded]]].
  exists (compile_bounded_vass_section (extend_bvass B F) bound).
  intros state counters.
  rewrite Hbounded.
  symmetry. apply lemma_11_bounded_depth_vass_section.
Qed.

(** Coordinate projection for natural periodic sets.  This is the set-valued
    counterpart of [ProjectNRelation] and retains the natural-number witness
    rather than truncating an integer vector. *)
Definition ProjectNSet {big small}
    (selection : Fin.t small -> Fin.t big) (set : NVec big -> Prop) :
    NVec small -> Prop :=
  fun value => exists source,
    set source /\
    forall index, StdVector.nth value index =
      StdVector.nth source (selection index).

Lemma project_nset_periodic : forall big small
    (selection : Fin.t small -> Fin.t big) (set : NVec big -> Prop),
    PeriodicNSet set -> PeriodicNSet (ProjectNSet selection set).
Proof.
  intros big small selection set [Hzero Hadd]. split.
  - exists (nvec_zero big). split; [exact Hzero|]. intro index.
    unfold nvec_zero. now rewrite !StdVector.const_nth.
  - intros left right [big_left [Hleft Eleft]]
      [big_right [Hright Eright]].
    exists (nvec_add big_left big_right). split; [now apply Hadd|].
    intro index. unfold nvec_add.
    rewrite (StdVector.nth_map2 _ _ _ index index index eq_refl eq_refl),
      (StdVector.nth_map2 _ _ _ (selection index) (selection index)
        (selection index) eq_refl eq_refl), Eleft, Eright. reflexivity.
Qed.

Definition qvec_project_set {big small}
    (selection : Fin.t small -> Fin.t big) (value : QVec big) : QVec small :=
  fun index => value (selection index).

Theorem project_nset_cone : forall big small
    (selection : Fin.t small -> Fin.t big) (set : NVec big -> Prop)
    (point : QVec small),
    PeriodicNSet set ->
    (Cone (NSetAsZ (ProjectNSet selection set)) point <->
     exists big_point,
       Cone (NSetAsZ set) big_point /\
       QVecEq point (qvec_project_set selection big_point)).
Proof.
  intros big small selection set point Hperiodic. split.
  - intro Hcone.
    apply (proj1 (periodic_cone_positive_multiple_iff small
      (NSetAsZ (ProjectNSet selection set)) point
      (periodic_nset_as_z small _
        (project_nset_periodic big small selection set Hperiodic)))) in Hcone.
    destruct Hcone as [multiplier [integer [Hpositive
      [[natural [Einteger [source [Hset Hcoordinates]]]] Hpoint]]]].
    subst integer.
    exists (qvec_scale (/ q_of_nat multiplier) (nvec_to_qvec source)). split.
    + apply (proj2 (periodic_cone_positive_multiple_iff big
        (NSetAsZ set) _ (periodic_nset_as_z big set Hperiodic))).
      exists multiplier, (nvec_to_zvec source). repeat split; try assumption.
      * exists source. auto.
      * apply positive_nat_inverse_scale. exact Hpositive.
    + intro index. unfold qvec_project_set, qvec_scale, nvec_to_qvec.
      assert (Hcoord := Hpoint index).
      unfold qvec_scale, zvec_to_qvec, nvec_to_zvec in Hcoord.
      rewrite (StdVector.nth_map _ _ index index eq_refl) in Hcoord.
      assert (Hnonzero : ~ q_of_nat multiplier == 0).
      { unfold q_of_nat. intro Hz.
        apply (proj1 (inject_Z_injective (Z.of_nat multiplier) 0%Z)) in Hz.
        lia. }
      transitivity (/ q_of_nat multiplier *
        (q_of_nat multiplier * point index)).
      * field. exact Hnonzero.
      * apply Qmult_comp; [reflexivity|].
        transitivity (inject_Z (Z.of_nat (StdVector.nth natural index))).
        -- exact Hcoord.
        -- rewrite Hcoordinates. reflexivity.
  - intros [big_point [Hcone Hcoordinates]].
    apply (proj2 (periodic_cone_positive_multiple_iff small
      (NSetAsZ (ProjectNSet selection set)) point
      (periodic_nset_as_z small _
        (project_nset_periodic big small selection set Hperiodic)))).
    apply (proj1 (periodic_cone_positive_multiple_iff big
      (NSetAsZ set) big_point
      (periodic_nset_as_z big set Hperiodic))) in Hcone.
    destruct Hcone as [multiplier [integer [Hpositive
      [[source [Einteger Hset]] Hpoint]]]]. subst integer.
    exists multiplier, (nvec_to_zvec (nvec_project selection source)).
    repeat split; try assumption.
    + exists (nvec_project selection source). split; [reflexivity|].
      exists source. split; [exact Hset|]. apply nvec_project_nth.
    + intro index. unfold qvec_scale, zvec_to_qvec, nvec_to_zvec.
      rewrite (StdVector.nth_map _ _ index index eq_refl), nvec_project_nth.
      transitivity (q_of_nat multiplier * big_point (selection index)).
      * apply Qmult_comp; [reflexivity|exact (Hcoordinates index)].
      * specialize (Hpoint (selection index)).
        unfold qvec_scale, zvec_to_qvec, nvec_to_zvec in Hpoint.
        rewrite (StdVector.nth_map _ _ (selection index) (selection index)
          eq_refl) in Hpoint. exact Hpoint.
Qed.

Theorem asymptotically_definable_nset_coordinate_projection :
  forall big small (selection : Fin.t small -> Fin.t big)
    (set : NVec big -> Prop),
    AsymptoticallyDefinableNSet set ->
    AsymptoticallyDefinableNSet (ProjectNSet selection set).
Proof.
  intros big small selection set [Hperiodic Hdef]. split.
  - now apply project_nset_periodic.
  - pose proof (qdefinable_projection big small selection
      (Cone (NSetAsZ set)) Hdef) as Hprojection.
    eapply qdefinable_congr; [|exact Hprojection]. intro point.
    symmetry. apply project_nset_cone. exact Hperiodic.
Qed.

Definition project_almost_set_component {big small}
    (selection : Fin.t small -> Fin.t big)
    (component : AlmostSemilinearNComponentSet big) :
    AlmostSemilinearNComponentSet small :=
  {| AlmostSetBase := nvec_project selection (AlmostSetBase component);
     AlmostSetPeriod := ProjectNSet selection (AlmostSetPeriod component) |}.

Theorem almost_semilinear_nset_coordinate_projection : forall big small
    (selection : Fin.t small -> Fin.t big) (set : NVec big -> Prop),
    AlmostSemilinearNSet set ->
    AlmostSemilinearNSet (ProjectNSet selection set).
Proof.
  intros big small selection set [components [Hasym Hset]].
  exists (List.map (project_almost_set_component selection) components). split.
  - apply List.Forall_forall. intros projected Hin.
    apply in_map_iff in Hin as [component [<- Hin]]. cbn.
    apply asymptotically_definable_nset_coordinate_projection.
    exact (proj1 (List.Forall_forall _ _) Hasym component Hin).
  - intro value. split.
    + intros [source [Hsource Hcoordinates]]. apply Hset in Hsource.
      destruct Hsource as [component [Hin [offset [Hperiod Esource]]]].
      exists (project_almost_set_component selection component). split;
        [now apply in_map|].
      exists (nvec_project selection offset). cbn. split.
      * exists offset. split; [exact Hperiod|]. apply nvec_project_nth.
      * apply StdVector.eq_nth_iff. intros index index' <-.
        unfold nvec_add.
        rewrite (StdVector.nth_map2 _ _ _ index index index eq_refl eq_refl),
          !nvec_project_nth, Hcoordinates.
        pose proof (f_equal (fun vector : NVec big =>
          StdVector.nth vector (selection index)) Esource) as Ecoordinate.
        unfold nvec_add in Ecoordinate.
        rewrite (StdVector.nth_map2 _ _ _ (selection index)
          (selection index) (selection index) eq_refl eq_refl) in Ecoordinate.
        exact Ecoordinate.
    + intros [projected [Hin [offset [Hperiod Evalue]]]].
      apply in_map_iff in Hin as [component [<- Hin]]. cbn in *.
      destruct Hperiod as [big_offset [Hperiod Hoffset]].
      exists (nvec_add (AlmostSetBase component) big_offset). split.
      * apply Hset. exists component. split; [exact Hin|].
        exists big_offset. auto.
      * intro index. subst value. unfold nvec_add.
        rewrite (StdVector.nth_map2 _ _ _ index index index eq_refl eq_refl),
          !nvec_project_nth, Hoffset.
        unfold nvec_add.
        rewrite (StdVector.nth_map2 _ _ _ (selection index)
          (selection index) (selection index) eq_refl eq_refl). reflexivity.
Qed.

Lemma finite_nvec_set_semilinear : forall d (values : list (NVec d)),
    Semilinear (fun value => List.In value values).
Proof.
  intros d values.
  exists (List.map (fun value : NVec d =>
    (value, ([] : list (NVec d)))) values).
  intro value. split.
  - intro Hin. exists (value, ([] : list (NVec d))). split.
    + apply in_map_iff. exists value. auto.
    +
    exists [], (nvec_zero d). split; [reflexivity|].
    symmetry. apply nvec_add_zero_right_local.
  - intros [[base periods] [Hin [coefficients [contribution [Hsum Evalue]]]]].
    apply in_map_iff in Hin as [listed [Heq Hin]].
    injection Heq as Ebase Eperiods. subst base periods.
    destruct coefficients as [|coefficient coefficients]; cbn in Hsum;
      [injection Hsum as Econtribution|discriminate].
    subst contribution value. rewrite nvec_add_zero_right_local. exact Hin.
Qed.

Definition SectionInitialSet {d q} (W : VASSSection d q) :
    Mell.VAS.StatefulVAS.SConfig
      (d + section_aux_dimension W) (section_state_count W) -> Prop :=
  fun config => List.In config (section_initial_configs W).

Theorem section_initial_set_semilinear : forall d q (W : VASSSection d q),
    StatefulSemilinear (SectionInitialSet W).
Proof.
  intros d q W state.
  set (values := List.map snd
    (List.filter (fun config => if Fin.eq_dec (fst config) state
      then true else false) (section_initial_configs W))).
  destruct (finite_nvec_set_semilinear
    (d + section_aux_dimension W) values) as [code Hcode].
  exists code. intro counters. rewrite <- Hcode. unfold values,
    SectionInitialSet. split.
  - intro Hin. apply in_map_iff. exists (state, counters). split;
      [reflexivity|]. apply filter_In. split; [exact Hin|]. cbn.
    destruct (Fin.eq_dec state state); [reflexivity|contradiction].
  - intro Hin. apply in_map_iff in Hin as [[listed_state listed_counters]
      [Ecounter Hfilter]]. cbn in Ecounter. subst listed_counters.
    apply filter_In in Hfilter as [Hin Hstate]. cbn in Hstate.
    destruct (Fin.eq_dec listed_state state) as [->|Hneq];
      [exact Hin|discriminate].
Qed.

Definition SectionTargetSet {d q} (W : VASSSection d q)
    (R : SConfig d q -> Prop) (original_state : Fin.t q) :
    Mell.VAS.StatefulVAS.SConfig
      (d + section_aux_dimension W) (section_state_count W) -> Prop :=
  fun config =>
    fst config = section_accept_state W original_state /\
    exists counters,
      R (original_state, counters) /\
      snd config = section_target_vector W counters.

Lemma semilinear_embed_left_exact : forall d auxiliary (set : NVec d -> Prop),
    Semilinear set ->
    Semilinear (fun value : NVec (d + auxiliary) => exists source,
      set source /\ value = embed_left_vector source).
Proof.
  intros d auxiliary set [code Hcode].
  exists (map_semicode (@embed_left_vector d auxiliary) code). intro value.
  rewrite map_semicode_embed_left_correct. split.
  - intros [source [Hset Evalue]]. exists source. split;
      [now apply Hcode|exact Evalue].
  - intros [source [Hdenote Evalue]]. exists source. split;
      [now apply Hcode|exact Evalue].
Qed.

Theorem section_target_set_semilinear : forall d q (W : VASSSection d q)
    (R : SConfig d q -> Prop),
    StatefulSemilinear R ->
    forall original_state,
      StatefulSemilinear (SectionTargetSet W R original_state).
Proof.
  intros d q W R HR original_state internal_state.
  destruct (Fin.eq_dec internal_state
    (section_accept_state W original_state)) as [Estate|Hstate].
  - subst internal_state.
    destruct (semilinear_embed_left_exact d (section_aux_dimension W)
      (fun counters => R (original_state, counters)) (HR original_state))
      as [code Hcode].
    exists code. intro value. rewrite <- Hcode.
    unfold SectionTargetSet, section_target_vector, embed_left_vector. cbn.
    split.
    + intros [_ [counters [HRvalue Evalue]]]. exists counters. auto.
    + intros [counters [HRvalue Evalue]]. split; [reflexivity|].
      exists counters. auto.
  - exists []. intro value. split.
    + intros [Hsame _]. contradiction.
    + intro Hdenote. exfalso. exact (denote_empty _ _ Hdenote).
Qed.

Definition section_visible_selection {d q} (W : VASSSection d q) :
    Fin.t d -> Fin.t (d + section_aux_dimension W) :=
  fun index => Fin.L (section_aux_dimension W) index.

Lemma section_target_visible : forall d q (W : VASSSection d q)
    (counters : NVec d) index,
    StdVector.nth counters index =
      StdVector.nth (section_target_vector W counters)
        (section_visible_selection W index).
Proof.
  intros. unfold section_target_vector, section_visible_selection.
  now rewrite VectorSpec.nth_append_L.
Qed.

Theorem vass_section_inter_semilinear : forall d q (W : VASSSection d q)
    (R : SConfig d q -> Prop),
    StatefulSemilinear R ->
    StatefulAlmostSemilinear (fun config =>
      R config /\ VASSSectionReach W (fst config) (snd config)).
Proof.
  intros d q W R HR original_state.
  pose proof (vas_post_inter_semilinear
    (d + section_aux_dimension W) (section_state_count W)
    (section_system W) (SectionInitialSet W)
    (SectionTargetSet W R original_state)
    (section_initial_set_semilinear d q W)
    (section_target_set_semilinear d q W R HR original_state)) as Hpost.
  specialize (Hpost (section_accept_state W original_state)).
  pose proof (almost_semilinear_nset_coordinate_projection
    (d + section_aux_dimension W) d (section_visible_selection W)
    (fun counters =>
      (SectionTargetSet W R original_state
        (section_accept_state W original_state, counters) /\
       exists source,
         SectionInitialSet W source /\
         VASReach (section_system W) (fst source) (snd source)
           (section_accept_state W original_state) counters)) Hpost) as Hproject.
  eapply almost_semilinear_nset_congr; [|exact Hproject]. intro counters.
  symmetry. unfold ProjectNSet. split.
  - intros [HRvalue Hsection].
    destruct Hsection as [initial_state [initial_counters [Hinitial Hreach]]].
    exists (section_target_vector W counters). split.
    + split.
      * unfold SectionTargetSet. cbn. split; [reflexivity|].
        exists counters. auto.
      * exists (initial_state, initial_counters). cbn.
        split; [exact Hinitial|exact Hreach].
    + apply section_target_visible.
  - intros [big_target [Hbig Hcoordinates]].
    destruct Hbig as [Htarget Hpostreach].
    destruct Htarget as [Haccept [visible [HRvalue Ebig]]].
    destruct Hpostreach as [[initial_state initial_counters]
      [Hinitial Hreach]].
    cbn in Haccept, Ebig, Hreach. subst big_target.
    assert (Ecounters : counters = visible).
    { apply StdVector.eq_nth_iff. intros index index' <-.
      rewrite (Hcoordinates index). unfold section_target_vector,
        section_visible_selection. now rewrite VectorSpec.nth_append_L. }
    subst visible. split; [exact HRvalue|].
    exists initial_state, initial_counters. auto.
Qed.

Theorem bvass_reach_inter_semilinear :
  forall d q (B : SBVAS d q)
    (R : SConfig d q -> Prop),
    StatefulSemilinear R ->
    StatefulAlmostSemilinear
      (fun config =>
        R config /\
        SReach B (fst config) (snd config)).
Proof.
  intros d q B R HR.
  destruct (bvass_reach_is_vass_section d q B) as [W HW].
  pose proof (vass_section_inter_semilinear d q W R HR) as Hsection.
  intro state.
  eapply almost_semilinear_nset_congr; [|apply Hsection].
  intro counters. cbn. rewrite <- (HW state counters). reflexivity.
Qed.
