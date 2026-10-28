From Coq Require Import Lia List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Closure.
From Mell.Geometry Require Import MathCompBridge QConeCore RationalDefinability.
From Mell.VAS Require Import Transformer RelationCone AsymptoticRelation
  PeriodicIntersection AlmostSemilinear AlmostSemilinearProjection.

Open Scope Q_scope.

Definition ProjectNRelation {big small}
    (selection : Fin.t small -> Fin.t big) (relation : NRelation big) :
    NRelation small :=
  fun input output => exists big_input big_output,
    relation big_input big_output /\
    (forall index, Vector.nth input index =
      Vector.nth big_input (selection index)) /\
    (forall index, Vector.nth output index =
      Vector.nth big_output (selection index)).

Lemma project_nrelation_periodic : forall (big small : nat)
    (selection : Fin.t small -> Fin.t big)
    (relation : NRelation big),
    PeriodicNRelation relation ->
    PeriodicNRelation (ProjectNRelation selection relation).
Proof.
  intros big small selection relation [Hzero Hadd]. split.
  - exists (nvec_zero big), (nvec_zero big). split; [exact Hzero|]. split;
      intro index; unfold nvec_zero; rewrite !Vector.const_nth; reflexivity.
  - intros x1 y1 x2 y2
      [bx1 [by1 [HR1 [Hx1 Hy1]]]] [bx2 [by2 [HR2 [Hx2 Hy2]]]].
    exists (nvec_add bx1 bx2), (nvec_add by1 by2). split.
    + now apply Hadd.
    + split; intro index; unfold nvec_add.
      * rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
          (Vector.nth_map2 _ _ _ (selection index) (selection index)
            (selection index) eq_refl eq_refl), Hx1, Hx2. reflexivity.
      * rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
          (Vector.nth_map2 _ _ _ (selection index) (selection index)
            (selection index) eq_refl eq_refl), Hy1, Hy2. reflexivity.
Qed.

Definition qvec_project {big small} (selection : Fin.t small -> Fin.t big)
    (value : QVec big) : QVec small := fun index => value (selection index).

Lemma scale_inverse_embed_project : forall (big small : nat)
    (selection : Fin.t small -> Fin.t big) multiplier
    (value : NVec big),
    (0 < multiplier)%nat ->
    QVecEq
      (qvec_project selection
        (qvec_scale (/ q_of_nat multiplier) (nvec_to_qvec value)))
      (qvec_scale (/ q_of_nat multiplier)
        (nvec_to_qvec (nvec_project selection value))).
Proof.
  intros big small selection multiplier value Hpositive index.
  unfold qvec_project, qvec_scale, nvec_to_qvec.
  rewrite nvec_project_nth. reflexivity.
Qed.

Theorem project_nrelation_cone : forall (big small : nat)
    (selection : Fin.t small -> Fin.t big)
    (relation : NRelation big) input output,
    PeriodicNRelation relation ->
    (RationalRelationCone
       (NRelationAsZ (ProjectNRelation selection relation)) input output <->
     exists big_input big_output,
       RationalRelationCone (NRelationAsZ relation) big_input big_output /\
       QVecEq input (qvec_project selection big_input) /\
       QVecEq output (qvec_project selection big_output)).
Proof.
  intros big small selection relation input output Hperiodic. split.
  - intro Hcone.
    apply (proj1 (periodic_relation_cone_positive_multiple_iff small
      (NRelationAsZ (ProjectNRelation selection relation)) input output
      (periodic_nrelation_as_z small _
        (project_nrelation_periodic big small selection relation Hperiodic))))
      in Hcone.
    destruct Hcone as [multiplier [zi [zo [Hpositive
      [Hmember [Hinput Houtput]]]]]].
    destruct Hmember as [ni [no [Ezi [Ezo
      [bi [bo [HR [Hni Hno]]]]]]]].
    subst zi zo.
    exists (qvec_scale (/ q_of_nat multiplier) (nvec_to_qvec bi)),
      (qvec_scale (/ q_of_nat multiplier) (nvec_to_qvec bo)). split.
    + apply (proj2 (periodic_relation_cone_positive_multiple_iff big
        (NRelationAsZ relation) _ _
        (periodic_nrelation_as_z big relation Hperiodic))).
      exists multiplier, (nvec_to_zvec bi), (nvec_to_zvec bo).
      repeat split; try assumption.
      * exists bi, bo. repeat split; try reflexivity. exact HR.
      * apply positive_nat_inverse_scale. exact Hpositive.
      * apply positive_nat_inverse_scale. exact Hpositive.
    + split; intro index.
      * assert (Hcoord := Hinput index). unfold qvec_scale in Hcoord.
        unfold zvec_to_qvec, nvec_to_zvec in Hcoord.
        rewrite (Vector.nth_map _ _ index index eq_refl) in Hcoord.
        unfold qvec_project, qvec_scale, nvec_to_qvec.
        assert (Hnonzero : ~ q_of_nat multiplier == 0).
        { unfold q_of_nat. intro Hz.
          apply (proj1 (inject_Z_injective (Z.of_nat multiplier) 0%Z)) in Hz.
          lia. }
        transitivity (/ q_of_nat multiplier *
          (q_of_nat multiplier * input index)).
        -- field. exact Hnonzero.
        -- apply Qmult_comp; [reflexivity|].
           transitivity (inject_Z (Z.of_nat (Vector.nth ni index))).
           ++ exact Hcoord.
           ++ rewrite Hni. reflexivity.
      * assert (Hcoord := Houtput index). unfold qvec_scale in Hcoord.
        unfold zvec_to_qvec, nvec_to_zvec in Hcoord.
        rewrite (Vector.nth_map _ _ index index eq_refl) in Hcoord.
        unfold qvec_project, qvec_scale, nvec_to_qvec.
        assert (Hnonzero : ~ q_of_nat multiplier == 0).
        { unfold q_of_nat. intro Hz.
          apply (proj1 (inject_Z_injective (Z.of_nat multiplier) 0%Z)) in Hz.
          lia. }
        transitivity (/ q_of_nat multiplier *
          (q_of_nat multiplier * output index)).
        -- field. exact Hnonzero.
        -- apply Qmult_comp; [reflexivity|].
           transitivity (inject_Z (Z.of_nat (Vector.nth no index))).
           ++ exact Hcoord.
           ++ rewrite Hno. reflexivity.
  - intros [big_input [big_output [Hcone [Hinput Houtput]]]].
    apply (proj2 (periodic_relation_cone_positive_multiple_iff small
      (NRelationAsZ (ProjectNRelation selection relation)) input output
      (periodic_nrelation_as_z small _
        (project_nrelation_periodic big small selection relation Hperiodic)))).
    apply (proj1 (periodic_relation_cone_positive_multiple_iff big
      (NRelationAsZ relation) big_input big_output
      (periodic_nrelation_as_z big relation Hperiodic))) in Hcone.
    destruct Hcone as [multiplier [zi [zo [Hpositive
      [Hmember [Hbi Hbo]]]]]].
    destruct Hmember as [bi [bo [Ezi [Ezo HR]]]]. subst zi zo.
    exists multiplier,
      (nvec_to_zvec (nvec_project selection bi)),
      (nvec_to_zvec (nvec_project selection bo)). repeat split; try assumption.
    + exists (nvec_project selection bi), (nvec_project selection bo).
      repeat split; try reflexivity.
      exists bi, bo. repeat split; try assumption; apply nvec_project_nth.
    + intro index. unfold qvec_scale, zvec_to_qvec, nvec_to_zvec.
      rewrite (Vector.nth_map _ _ index index eq_refl), nvec_project_nth.
      transitivity (q_of_nat multiplier * big_input (selection index)).
      * apply Qmult_comp; [reflexivity|exact (Hinput index)].
      * specialize (Hbi (selection index)).
        unfold qvec_scale, zvec_to_qvec, nvec_to_zvec in Hbi.
        rewrite (Vector.nth_map _ _ (selection index) (selection index) eq_refl)
          in Hbi. exact Hbi.
    + intro index. unfold qvec_scale, zvec_to_qvec, nvec_to_zvec.
      rewrite (Vector.nth_map _ _ index index eq_refl), nvec_project_nth.
      transitivity (q_of_nat multiplier * big_output (selection index)).
      * apply Qmult_comp; [reflexivity|exact (Houtput index)].
      * specialize (Hbo (selection index)).
        unfold qvec_scale, zvec_to_qvec, nvec_to_zvec in Hbo.
        rewrite (Vector.nth_map _ _ (selection index) (selection index) eq_refl)
          in Hbo. exact Hbo.
Qed.

Lemma qpair_right_bound : forall small (index : Fin.t (small + small)),
    ~ (proj1_sig (Fin.to_nat index) < small)%nat ->
    (proj1_sig (Fin.to_nat index) - small < small)%nat.
Proof.
  intros small index Hnot. destruct (Fin.to_nat index) as [position Hbound].
  cbn in *. lia.
Qed.

Definition qpair_selection {big small}
    (selection : Fin.t small -> Fin.t big) :
    Fin.t (small + small) -> Fin.t (big + big) :=
  fun index =>
    let position := proj1_sig (Fin.to_nat index) in
    match lt_dec position small with
    | left Hleft => Fin.L big (selection (Fin.of_nat_lt Hleft))
    | right Hright =>
        Fin.R big (selection (Fin.of_nat_lt (p := position - small)
          (qpair_right_bound small index Hright)))
    end.

Lemma qpair_selection_left : forall big small selection (index : Fin.t small),
    @qpair_selection big small selection (Fin.L small index) =
    Fin.L big (selection index).
Proof.
  intros big small selection index.
  unfold qpair_selection.
  set (position := proj1_sig (Fin.to_nat (Fin.L small index))).
  destruct (lt_dec position small) as [Hlt|Hlt] eqn:Hdecision.
  - assert (Heq : Fin.of_nat_lt Hlt = index).
    { apply Fin.to_nat_inj. unfold position in *.
      pose proof (@Fin.to_nat_of_nat
        (proj1_sig (Fin.to_nat (Fin.L small index))) small Hlt) as Hof.
      rewrite Hof. cbn. rewrite Fin.L_sanity. reflexivity. }
    rewrite Heq. reflexivity.
  - exfalso. apply Hlt. unfold position. rewrite Fin.L_sanity.
    exact (proj2_sig (Fin.to_nat index)).
Qed.

Lemma qpair_selection_right : forall big small selection (index : Fin.t small),
    @qpair_selection big small selection (Fin.R small index) =
    Fin.R big (selection index).
Proof.
  intros big small selection index.
  unfold qpair_selection.
  set (position := proj1_sig (Fin.to_nat (Fin.R small index))).
  destruct (lt_dec position small) as [Hlt|Hlt] eqn:Hdecision.
  - assert (Hposition : position = (small + proj1_sig (Fin.to_nat index))%nat).
    { unfold position. apply Fin.R_sanity. }
    lia.
  - assert (Heq : Fin.of_nat_lt
        (qpair_right_bound small (Fin.R small index) Hlt) = index).
    { apply Fin.to_nat_inj.
      pose proof (@Fin.to_nat_of_nat
        (proj1_sig (Fin.to_nat (Fin.R small index)) - small) small
        (qpair_right_bound small (Fin.R small index) Hlt)) as Hof.
      rewrite Hof. cbn. rewrite Fin.R_sanity. lia. }
    f_equal. exact (f_equal selection Heq).
Qed.

Theorem asymptotically_definable_nrelation_coordinate_projection :
  forall (big small : nat) (selection : Fin.t small -> Fin.t big)
    (relation : NRelation big),
    AsymptoticallyDefinableNRelation relation ->
    AsymptoticallyDefinableNRelation (ProjectNRelation selection relation).
Proof.
  intros big small selection relation [Hperiodic Hdef]. split.
  - now apply project_nrelation_periodic.
  - pose proof (qdefinable_projection (big + big) (small + small)
      (qpair_selection selection)
      (RelationConePairs (NRelationAsZ relation)) Hdef) as Hprojected.
    eapply qdefinable_congr; [|exact Hprojected]. intro pair.
    rewrite relation_cone_pairs_unpack.
    rewrite project_nrelation_cone by exact Hperiodic.
    split.
    + intros [big_pair [Hbig Hcoordinates]].
      exists (qpair_left big_pair), (qpair_right big_pair). split.
      * rewrite <- relation_cone_pairs_unpack. exact Hbig.
      * split; intro index.
        -- transitivity (pair (Fin.L small index)).
           ++ apply qpair_left_coordinate.
           ++ transitivity (big_pair (Fin.L big (selection index))).
              ** pose proof (Hcoordinates (Fin.L small index)) as Hcoordinate.
                 rewrite qpair_selection_left in Hcoordinate. exact Hcoordinate.
              ** symmetry. apply qpair_left_coordinate.
        -- transitivity (pair (Fin.R small index)).
           ++ apply qpair_right_coordinate.
           ++ transitivity (big_pair (Fin.R big (selection index))).
              ** pose proof (Hcoordinates (Fin.R small index)) as Hcoordinate.
                 rewrite qpair_selection_right in Hcoordinate. exact Hcoordinate.
              ** symmetry. apply qpair_right_coordinate.
    + intros [big_input [big_output [Hbig [Hinput Houtput]]]].
      exists (qpair_pack big_input big_output). split.
      * unfold RelationConePairs, RationalRelationCone in *. exact Hbig.
      * intro combined. refine (Fin.case_L_R' (fun index =>
          pair index == qpair_pack big_input big_output
            (qpair_selection selection index)) combined _ _).
        -- intro index. cbn. transitivity (qpair_left pair index).
           ++ symmetry. apply qpair_left_coordinate.
           ++ transitivity (qvec_project selection big_input index).
              ** exact (Hinput index).
              ** unfold qvec_project. rewrite qpair_selection_left.
                 transitivity (qpair_left (qpair_pack big_input big_output)
                   (selection index)).
                 --- symmetry. apply qpair_left_pack.
                 --- apply qpair_left_coordinate.
        -- intro index. cbn. transitivity (qpair_right pair index).
           ++ symmetry. apply qpair_right_coordinate.
           ++ transitivity (qvec_project selection big_output index).
              ** exact (Houtput index).
              ** unfold qvec_project. rewrite qpair_selection_right.
                 transitivity (qpair_right (qpair_pack big_input big_output)
                   (selection index)).
                 --- symmetry. apply qpair_right_pack.
                 --- apply qpair_right_coordinate.
Qed.

Definition project_almost_component {big small}
    (selection : Fin.t small -> Fin.t big)
    (component : AlmostSemilinearNComponent big) :
    AlmostSemilinearNComponent small :=
  {| AlmostBaseInput := nvec_project selection (AlmostBaseInput component);
     AlmostBaseOutput := nvec_project selection (AlmostBaseOutput component);
     AlmostPeriodRelation :=
       ProjectNRelation selection (AlmostPeriodRelation component) |}.

Theorem almost_semilinear_nrelation_coordinate_projection : forall (big small : nat)
    (selection : Fin.t small -> Fin.t big) (relation : NRelation big),
    AlmostSemilinearNRelation relation ->
    AlmostSemilinearNRelation (ProjectNRelation selection relation).
Proof.
  intros big small selection relation [components [Hasym Hrelation]].
  exists (List.map (project_almost_component selection) components). split.
  - apply List.Forall_forall. intros projected Hin.
    apply in_map_iff in Hin as [component [<- Hin]]. cbn.
    apply asymptotically_definable_nrelation_coordinate_projection.
    exact (proj1 (List.Forall_forall _ _) Hasym component Hin).
  - intros input output. split.
    + intros [big_input [big_output [HR [Hinput Houtput]]]].
      apply Hrelation in HR.
      destruct HR as [component [Hin [oi [oo [HP [Einput Eoutput]]]]]].
      exists (project_almost_component selection component). split;
        [now apply in_map|].
      exists (nvec_project selection oi), (nvec_project selection oo).
      cbn [project_almost_component]. split.
      * exists oi, oo. repeat split; try assumption; apply nvec_project_nth.
      * split.
        -- change (input = nvec_add
             (nvec_project selection (AlmostBaseInput component))
             (nvec_project selection oi)).
           apply Vector.eq_nth_iff. intros index index' <-.
           unfold nvec_add. rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
             !nvec_project_nth, (Hinput index).
           pose proof (f_equal (fun value : NVec big =>
             Vector.nth value (selection index)) Einput) as Hcoordinate.
           unfold nvec_add in Hcoordinate.
           rewrite (Vector.nth_map2 _ _ _ (selection index)
             (selection index) (selection index) eq_refl eq_refl) in Hcoordinate.
           exact Hcoordinate.
        -- change (output = nvec_add
             (nvec_project selection (AlmostBaseOutput component))
             (nvec_project selection oo)).
           apply Vector.eq_nth_iff. intros index index' <-.
           unfold nvec_add. rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
             !nvec_project_nth, (Houtput index).
           pose proof (f_equal (fun value : NVec big =>
             Vector.nth value (selection index)) Eoutput) as Hcoordinate.
           unfold nvec_add in Hcoordinate.
           rewrite (Vector.nth_map2 _ _ _ (selection index)
             (selection index) (selection index) eq_refl eq_refl) in Hcoordinate.
           exact Hcoordinate.
    + intros [projected [Hin [oi [oo [HP [Einput Eoutput]]]]]].
      apply in_map_iff in Hin as [component [<- Hin]]. cbn in *.
      destruct HP as [big_oi [big_oo [HP [Hoi Hoo]]]].
      exists (nvec_add (AlmostBaseInput component) big_oi),
        (nvec_add (AlmostBaseOutput component) big_oo). split.
      * apply Hrelation. exists component. split; [exact Hin|].
        exists big_oi, big_oo. repeat split; try assumption.
      * split; intro index.
        -- subst input. unfold nvec_add.
           rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
             !nvec_project_nth, Hoi.
           unfold nvec_add. rewrite (Vector.nth_map2 _ _ _ (selection index)
             (selection index) (selection index) eq_refl eq_refl). reflexivity.
        -- subst output. unfold nvec_add.
           rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
             !nvec_project_nth, Hoo.
           unfold nvec_add. rewrite (Vector.nth_map2 _ _ _ (selection index)
             (selection index) (selection index) eq_refl eq_refl). reflexivity.
Qed.
