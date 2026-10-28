From Coq Require Import Arith.PeanoNat Bool Lia List QArith Vector.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone LatticeGordanPullback MathCompBridge Periodic QConeCore
  RationalDefinability RationalHToV.
From Mell.Semilinear Require Import Closure LinearEquations.
From Mell.Order Require Import PeriodicOrder.
From Mell.BVAS Require Import System Runs Contexts RunOrder Amalgamation.
From Mell.BVASS Require Import AlmostSemilinear.
From Mell.Separator Require Import DoubledRelation.
From Mell.VAS Require Import Transformer SemilinearRelationDecomposition
  AlmostSemilinear AlmostSemilinearProjection AsymptoticRelation RelationCone
  KirchhoffDefinability Intraproductions.

Import ListNotations.
Module StdVector := Coq.Vectors.Vector.

Combined Scheme ValidIRun_ValidIRuns_mutind_local
  from ValidIRun_ind', ValidIRuns_ind'.

Definition SpecialTransformer {d} (system : IBVAS d) (base : NVec d) :
    NRelation d :=
  fun input output => SpecialLeafReach system
    (nvec_add base input) (nvec_add base output).

Lemma special_leaf_reach_trans : forall d (system : IBVAS d) x y z,
    SpecialLeafReach system x y ->
    SpecialLeafReach system y z ->
    SpecialLeafReach system x z.
Proof.
  intros d system x y z Hxy Hyz. revert x Hxy.
  induction Hyz as
    [y|y action prefix middle suffix z Haction Hprefix Hmiddle IH
      Hsuffix Happly]; intros x Hxy.
  - exact Hxy.
  - eapply special_action with (action := action) (prefix := prefix)
      (middle := middle) (suffix := suffix); eauto.
Qed.

Lemma nvec_add_cancel_left_local : forall d
    (base left right : NVec d),
    nvec_add base left = nvec_add base right -> left = right.
Proof.
  intros d base left right Heq. apply StdVector.eq_nth_iff.
  intros index index' <-.
  apply (f_equal (fun value => StdVector.nth value index)) in Heq.
  unfold nvec_add in Heq.
  repeat rewrite (StdVector.nth_map2 _ _ _ index index index
    eq_refl eq_refl) in Heq. lia.
Qed.

Lemma special_transformer_refl : forall d (system : IBVAS d) base value,
    SpecialTransformer system base value value.
Proof. intros; constructor. Qed.

Lemma special_transformer_trans : forall d (system : IBVAS d) base x y z,
    SpecialTransformer system base x y ->
    SpecialTransformer system base y z ->
    SpecialTransformer system base x z.
Proof. intros; eapply special_leaf_reach_trans; eauto. Qed.

Lemma special_transformer_periodic : forall d (system : IBVAS d) base,
    PeriodicNRelation (SpecialTransformer system base).
Proof.
  intros d system base. split.
  - unfold SpecialTransformer. rewrite nvec_add_zero_right_local. constructor.
  - intros x1 y1 x2 y2 H1 H2. unfold SpecialTransformer in *.
    pose proof (special_leaf_reach_shift d system _ _ H1 x2) as H1'.
    pose proof (special_leaf_reach_shift d system _ _ H2 y1) as H2'.
    eapply special_leaf_reach_trans.
    + rewrite !nvec_add_assoc_local in H1'. exact H1'.
    + rewrite !nvec_add_assoc_local in H2'.
      rewrite (nvec_add_comm d x2 y1), (nvec_add_comm d y2 y1) in H2'.
      exact H2'.
Qed.

Definition AbovePair {d} (base : NVec d) : NRelation d :=
  fun input output =>
    exists input_offset output_offset,
      input = nvec_add base input_offset /\
      output = nvec_add base output_offset.

Lemma semilinear_universal : forall d,
    Semilinear (fun _ : NVec d => True).
Proof.
  intro d.
  pose proof (finite_nvec_set_semilinear d []) as Hempty.
  pose proof (semilinear_complement d (fun value : NVec d => List.In value [])
    Hempty) as Hall.
  destruct Hall as [code Hcode]. exists code. intro value.
  rewrite <- Hcode. cbn. tauto.
Qed.

Lemma above_pair_semilinear : forall d (base : NVec d),
    SemilinearNRelation (AbovePair base).
Proof.
  intros d base. unfold SemilinearNRelation.
  pose proof (finite_nvec_set_semilinear (d + d)
    [npair_pack base base]) as Hbase.
  pose proof (semilinear_universal (d + d)) as Hall.
  pose proof (semilinear_minkowski_sum (d + d)
    (fun value => List.In value [npair_pack base base])
    (fun _ => True) Hbase Hall) as Hsum.
  destruct Hsum as [code Hcode]. exists code. intro pair.
  rewrite <- Hcode. split.
  - intros [input_offset [output_offset [Hinput Houtput]]].
    exists (npair_pack base base), (npair_pack input_offset output_offset).
    split; [now left|]. split; [exact I|].
    rewrite <- (npair_pack_split d pair), Hinput, Houtput.
    symmetry. apply npair_pack_add.
  - intros [base_pair [offset [[Hbase_pair | Hfalse] [_ Heq]]]].
    + subst base_pair. exists (npair_left offset), (npair_right offset).
      split.
      * pose proof (f_equal (@npair_left d) Heq) as Hleft.
        now rewrite npair_left_add, npair_left_pack in Hleft.
      * pose proof (f_equal (@npair_right d) Heq) as Hright.
        now rewrite npair_right_add, npair_right_pack in Hright.
    + contradiction.
Qed.

Lemma special_transformer_restricted_almost_semilinear : forall d
    (system : IBVAS d) base,
    AlmostSemilinearNRelation
      (fun input output => AbovePair base input output /\
        SpecialLeafReach system input output).
Proof.
  intros. apply lemma_4_6_special_leaf_inter_semilinear.
  apply above_pair_semilinear.
Qed.

Definition unshift_almost_component {d} (base : NVec d)
    (component : AlmostSemilinearNComponent d) :
    AlmostSemilinearNComponent d :=
  {| AlmostBaseInput := nvec_sub (AlmostBaseInput component) base;
     AlmostBaseOutput := nvec_sub (AlmostBaseOutput component) base;
     AlmostPeriodRelation := AlmostPeriodRelation component |}.

Lemma almost_component_base_member : forall d (relation : NRelation d)
    components (Hcomponents :
      forall source target,
        relation source target <->
        exists component,
          List.In component components /\
          exists offset_input offset_output,
            AlmostPeriodRelation component offset_input offset_output /\
            source = nvec_add (AlmostBaseInput component) offset_input /\
            target = nvec_add (AlmostBaseOutput component) offset_output)
    component,
    List.In component components ->
    AsymptoticallyDefinableNRelation (AlmostPeriodRelation component) ->
    relation (AlmostBaseInput component) (AlmostBaseOutput component).
Proof.
  intros d relation components Hcomponents component Hin [Hperiodic _].
  apply Hcomponents. exists component. split; [exact Hin|].
  exists (nvec_zero d), (nvec_zero d). split; [exact (proj1 Hperiodic)|].
  split; symmetry; apply nvec_add_zero_right_local.
Qed.

Lemma above_pair_base_exact : forall d (base input output : NVec d),
    AbovePair base input output ->
    input = nvec_add base (nvec_sub input base) /\
    output = nvec_add base (nvec_sub output base).
Proof.
  intros d base input output [oi [oo [Hin Hout]]]. split.
  - apply nvec_sub_exact. rewrite Hin. apply nvec_le_add_right.
  - apply nvec_sub_exact. rewrite Hout. apply nvec_le_add_right.
Qed.

Lemma almost_semilinear_unshift_relation : forall d base
    (relation : NRelation d),
    AlmostSemilinearNRelation
      (fun input output => AbovePair base input output /\ relation input output) ->
    AlmostSemilinearNRelation
      (fun input output => relation (nvec_add base input) (nvec_add base output)).
Proof.
  intros d base relation [components [Hasym Hrelation]].
  exists (List.map (unshift_almost_component base) components). split.
  - apply List.Forall_forall. intros shifted Hin.
    apply in_map_iff in Hin as [component [<- Hin]]. cbn.
    exact (proj1 (List.Forall_forall _ _) Hasym component Hin).
  - intros input output. split.
    + intro Hreach.
      assert (Habove : AbovePair base (nvec_add base input)
        (nvec_add base output)).
      { exists input, output. auto. }
      pose proof (proj1 (Hrelation (nvec_add base input)
        (nvec_add base output)) (conj Habove Hreach)) as Hdecomp.
      destruct Hdecomp as
        [component [Hin [oi [oo [Hperiod [Hinput Houtput]]]]]].
      assert (Hbase_member :
        AbovePair base (AlmostBaseInput component)
          (AlmostBaseOutput component) /\
        relation (AlmostBaseInput component) (AlmostBaseOutput component)).
      { eapply almost_component_base_member; eauto.
        exact (proj1 (List.Forall_forall _ _) Hasym component Hin). }
      destruct (above_pair_base_exact d base _ _ (proj1 Hbase_member))
        as [Hbase_input Hbase_output].
      exists (unshift_almost_component base component). split;
        [now apply in_map|]. exists oi, oo. cbn. split; [exact Hperiod|]. split.
      * apply nvec_add_cancel_left_local with (base := base).
        rewrite <- nvec_add_assoc_local, <- Hbase_input. exact Hinput.
      * apply nvec_add_cancel_left_local with (base := base).
        rewrite <- nvec_add_assoc_local, <- Hbase_output. exact Houtput.
    + intros [shifted [Hin [oi [oo [Hperiod [Hinput Houtput]]]]]].
      apply in_map_iff in Hin as [component [Heq Hin]]. subst shifted. cbn in *.
      assert (Hbase_member :
        AbovePair base (AlmostBaseInput component)
          (AlmostBaseOutput component) /\
        relation (AlmostBaseInput component) (AlmostBaseOutput component)).
      { eapply almost_component_base_member; eauto.
        exact (proj1 (List.Forall_forall _ _) Hasym component Hin). }
      destruct (above_pair_base_exact d base _ _ (proj1 Hbase_member))
        as [Hbase_input Hbase_output].
      apply (proj2 (Hrelation (nvec_add base input) (nvec_add base output))).
      exists component. split; [exact Hin|]. exists oi, oo.
      split; [exact Hperiod|]. split.
      * rewrite Hinput, <- nvec_add_assoc_local, <- Hbase_input. reflexivity.
      * rewrite Houtput, <- nvec_add_assoc_local, <- Hbase_output. reflexivity.
Qed.

Theorem special_transformer_almost_semilinear : forall d
    (system : IBVAS d) base,
    AlmostSemilinearNRelation (SpecialTransformer system base).
Proof.
  intros d system base. unfold SpecialTransformer.
  apply almost_semilinear_unshift_relation.
  apply special_transformer_restricted_almost_semilinear.
Qed.

(** Rational definability is closed under Minkowski sum.  This is the
    quantifier-elimination-free closure step used in the proof of Lemma 4.5. *)
Definition qadd_coordinate_formula (d coordinate : nat) : QFormula :=
  QFEq (QTVar (2 * d + coordinate))
    (QTAdd (QTVar coordinate) (QTVar (d + coordinate))).

Fixpoint qadd_constraints (d count : nat) : QFormula :=
  match count with
  | O => QFTop
  | S count' =>
      QFAnd (qadd_coordinate_formula d count')
        (qadd_constraints d count')
  end.

Lemma qadd_constraints_closed : forall d count,
    (count <= d)%nat ->
    qformula_closed ((d + d) + d) (qadd_constraints d count) = true.
Proof.
  intros d count. induction count as [|count IH]; intro Hle; cbn.
  - reflexivity.
  - apply andb_true_iff. split.
    + unfold qadd_coordinate_formula. cbn. repeat rewrite andb_true_iff.
      repeat split; apply Nat.ltb_lt; lia.
    + apply IH. lia.
Qed.

Lemma qfirst_selection_bound : forall d (index : Fin.t d),
    (proj1_sig (Fin.to_nat index) < (d + d) + d)%nat.
Proof. intros d index. destruct (Fin.to_nat index) as [coordinate Hcoordinate].
  cbn. nia. Qed.

Lemma qsecond_selection_bound : forall d (index : Fin.t d),
    (d + proj1_sig (Fin.to_nat index) < (d + d) + d)%nat.
Proof. intros d index. destruct (Fin.to_nat index) as [coordinate Hcoordinate].
  cbn. nia. Qed.

Lemma qthird_selection_bound : forall d (index : Fin.t d),
    (2 * d + proj1_sig (Fin.to_nat index) < (d + d) + d)%nat.
Proof. intros d index. destruct (Fin.to_nat index) as [coordinate Hcoordinate].
  cbn. nia. Qed.

Definition qfirst_selection (d : nat) : Fin.t d -> Fin.t ((d + d) + d) :=
  fun index => Fin.L d (Fin.L d index).

Definition qsecond_selection (d : nat) : Fin.t d -> Fin.t ((d + d) + d) :=
  fun index => Fin.L d (Fin.R d index).

Definition qthird_selection (d : nat) : Fin.t d -> Fin.t ((d + d) + d) :=
  fun index => Fin.R (d + d) index.

Lemma qfirst_selection_nat : forall d (index : Fin.t d),
    proj1_sig (Fin.to_nat (qfirst_selection d index)) =
    proj1_sig (Fin.to_nat index).
Proof. intros; unfold qfirst_selection; cbn.
  now rewrite !Fin.L_sanity. Qed.

Lemma qsecond_selection_nat : forall d (index : Fin.t d),
    proj1_sig (Fin.to_nat (qsecond_selection d index)) =
    (d + proj1_sig (Fin.to_nat index))%nat.
Proof. intros; unfold qsecond_selection; cbn.
  rewrite Fin.L_sanity, Fin.R_sanity. reflexivity. Qed.

Lemma qthird_selection_nat : forall d (index : Fin.t d),
    proj1_sig (Fin.to_nat (qthird_selection d index)) =
    (2 * d + proj1_sig (Fin.to_nat index))%nat.
Proof. intros; unfold qthird_selection; cbn.
  rewrite Fin.R_sanity. lia. Qed.

Lemma qfirst_selection_environment : forall d (value : QVec ((d + d) + d))
    (index : Fin.t d),
    qvec_environment value (proj1_sig (Fin.to_nat index)) =
    value (qfirst_selection d index).
Proof.
  intros. rewrite <- qvec_environment_inside.
  now rewrite qfirst_selection_nat.
Qed.

Lemma qsecond_selection_environment : forall d (value : QVec ((d + d) + d))
    (index : Fin.t d),
    qvec_environment value (d + proj1_sig (Fin.to_nat index))%nat =
    value (qsecond_selection d index).
Proof.
  intros. rewrite <- qvec_environment_inside.
  now rewrite qsecond_selection_nat.
Qed.

Lemma qthird_selection_environment : forall d (value : QVec ((d + d) + d))
    (index : Fin.t d),
    qvec_environment value (2 * d + proj1_sig (Fin.to_nat index))%nat =
    value (qthird_selection d index).
Proof.
  intros. rewrite <- qvec_environment_inside.
  now rewrite qthird_selection_nat.
Qed.

Lemma qadd_constraints_correct : forall d count environment,
    (qformula_semantics environment (qadd_constraints d count) <->
      forall coordinate, (coordinate < count)%nat ->
        (environment (2 * d + coordinate)%nat ==
          environment coordinate + environment (d + coordinate)%nat)%Q).
Proof.
  intros d count. induction count as [|count IH]; intro environment; cbn.
  - split; [intros _ coordinate Hlt; lia|intro; exact I].
  - rewrite IH. split.
    + intros [Hhead Htail] coordinate Hlt.
      destruct (Nat.eq_dec coordinate count) as [->|Hneq]; [exact Hhead|].
      apply Htail. lia.
    + intro Hall. split.
      * apply Hall. lia.
      * intros coordinate Hlt. apply Hall. lia.
Qed.

Lemma qadd_constraints_vector : forall d (value : QVec ((d + d) + d)),
    qformula_semantics (qvec_environment value) (qadd_constraints d d) <->
    forall index : Fin.t d,
      (value (qthird_selection d index) ==
        value (qfirst_selection d index) + value (qsecond_selection d index))%Q.
Proof.
  intros d value. rewrite qadd_constraints_correct. split.
  - intros Hall index.
    specialize (Hall (proj1_sig (Fin.to_nat index))
      (proj2_sig (Fin.to_nat index))).
    now rewrite qfirst_selection_environment, qsecond_selection_environment,
      qthird_selection_environment in Hall.
  - intros Hall coordinate Hcoordinate.
    pose (index := Fin.of_nat_lt Hcoordinate).
    specialize (Hall index).
    replace coordinate with (proj1_sig (Fin.to_nat index)) by
      (unfold index; now rewrite Fin.to_nat_of_nat).
    now rewrite qfirst_selection_environment, qsecond_selection_environment,
      qthird_selection_environment.
Qed.

Definition QAddGraph {d} (triple : QVec ((d + d) + d)) : Prop :=
  qvec_eq (qtriple_third triple)
    (qvec_add (qtriple_first triple) (qtriple_second triple)).

Lemma qadd_graph_formula : forall d (triple : QVec ((d + d) + d)),
    QAddGraph triple <->
    qformula_semantics (qvec_environment triple) (qadd_constraints d d).
Proof.
  intros d triple. rewrite qadd_constraints_vector.
  unfold QAddGraph, qtriple_first, qtriple_second, qtriple_third, qvec_add,
    qfirst_selection, qsecond_selection, qthird_selection. reflexivity.
Qed.

Lemma qdefinable_add_graph : forall d,
    QDefinable (@QAddGraph d).
Proof.
  intro d. exists (qadd_constraints d d). split.
  - apply qadd_constraints_closed. lia.
  - intro triple. apply qadd_graph_formula.
Qed.

Lemma qtriple_pack_first_local : forall d (first second third : QVec d),
    qvec_eq (qtriple_first (qtriple_pack first second third)) first.
Proof.
  intros d first second third index.
  pose proof (qtriple_pack_xy d first second third (Fin.L d index)) as Hxy.
  unfold qtriple_first, qtriple_xy_selection.
  transitivity (qpair_pack first second (Fin.L d index)).
  - exact Hxy.
  - unfold qpair_pack, qvec_join, qvec_of_vector.
    rewrite VectorSpec.nth_append_L, qvec_to_vector_nth. reflexivity.
Qed.

Lemma qtriple_pack_second_local : forall d (first second third : QVec d),
    qvec_eq (qtriple_second (qtriple_pack first second third)) second.
Proof.
  intros d first second third index.
  pose proof (qtriple_pack_xy d first second third (Fin.R d index)) as Hxy.
  unfold qtriple_second, qtriple_xy_selection.
  transitivity (qpair_pack first second (Fin.R d index)).
  - exact Hxy.
  - unfold qpair_pack, qvec_join, qvec_of_vector.
    rewrite VectorSpec.nth_append_R, qvec_to_vector_nth. reflexivity.
Qed.

Lemma qtriple_pack_third_local : forall d (first second third : QVec d),
    qvec_eq (qtriple_third (qtriple_pack first second third)) third.
Proof.
  intros d first second third index.
  pose proof (qtriple_pack_yz d first second third (Fin.R d index)) as Hyz.
  unfold qtriple_third. rewrite <- qtriple_yz_selection_right.
  transitivity (qpair_pack second third (Fin.R d index)).
  - exact Hyz.
  - unfold qpair_pack, qvec_join, qvec_of_vector.
    rewrite VectorSpec.nth_append_R, qvec_to_vector_nth. reflexivity.
Qed.

Lemma qdefinable_minkowski_sum : forall d (left right : QSet d),
    QDefinable left -> QDefinable right ->
    QDefinable (fun value => exists left_value right_value,
      left left_value /\ right right_value /\
      qvec_eq value (qvec_add left_value right_value)).
Proof.
  intros d left right Hleft Hright.
  pose proof (qdefinable_coordinate_preimage d ((d + d) + d)
    (qfirst_selection d) left Hleft) as Hfirst.
  pose proof (qdefinable_coordinate_preimage d ((d + d) + d)
    (qsecond_selection d) right Hright) as Hsecond.
  pose proof (qdefinable_intersection ((d + d) + d) _ _ Hfirst Hsecond)
    as Hboth.
  pose proof (qdefinable_intersection ((d + d) + d) _ _ Hboth
    (qdefinable_add_graph d)) as Htriple.
  pose proof (qdefinable_projection ((d + d) + d) d
    (qthird_selection d) _ Htriple) as Hprojected.
  eapply (@qdefinable_congr d
    (fun value => exists triple,
      ((left (fun index => triple (qfirst_selection d index)) /\
        right (fun index => triple (qsecond_selection d index))) /\
       QAddGraph triple) /\
      forall index, value index == triple (qthird_selection d index))
    (fun value => exists left_value right_value,
      left left_value /\ right right_value /\
      qvec_eq value (qvec_add left_value right_value))).
  - intro value. split.
    + intros [triple [[[Hl Hr] Hgraph] Hvisible]].
      exists (qtriple_first triple), (qtriple_second triple). repeat split.
      * exact Hl.
      * exact Hr.
      * intro index. transitivity (qtriple_third triple index).
        -- exact (Hvisible index).
        -- exact (Hgraph index).
    + intro Hsum_witness.
      destruct Hsum_witness as [left_value [right_value [Hl [Hr Hsum]]]].
      exists (qtriple_pack left_value right_value
        (qvec_add left_value right_value)). split.
      * repeat split.
        -- assert (Heq : qvec_eq left_value
              (fun index => qtriple_pack left_value right_value
                (qvec_add left_value right_value)
                (qfirst_selection d index))).
           { intro index. unfold qfirst_selection, qtriple_first.
             apply Qeq_sym. exact (qtriple_pack_first_local d left_value
               right_value (qvec_add left_value right_value) index). }
           apply (proj1 (qdefinable_qvec_extensional d left Hleft _ _ Heq)).
           exact Hl.
        -- assert (Heq : qvec_eq right_value
              (fun index => qtriple_pack left_value right_value
                (qvec_add left_value right_value)
                (qsecond_selection d index))).
           { intro index. unfold qsecond_selection, qtriple_second.
             apply Qeq_sym. exact (qtriple_pack_second_local d left_value
               right_value (qvec_add left_value right_value) index). }
           apply (proj1 (qdefinable_qvec_extensional d right Hright _ _ Heq)).
           exact Hr.
        -- unfold QAddGraph. intro index.
           transitivity ((qvec_add left_value right_value) index).
           ++ apply qtriple_pack_third_local.
           ++ unfold qvec_add. apply Qplus_comp.
              ** apply Qeq_sym. exact (qtriple_pack_first_local d left_value
                   right_value (qvec_add left_value right_value) index).
              ** apply Qeq_sym. exact (qtriple_pack_second_local d left_value
                   right_value (qvec_add left_value right_value) index).
      * intro index. transitivity ((qvec_add left_value right_value) index).
        -- apply Hsum.
        -- apply Qeq_sym. exact (qtriple_pack_third_local d left_value
             right_value (qvec_add left_value right_value) index).
  - exact Hprojected.
Qed.

Definition PositiveRay {d} (base : ZVec d) : QSet d :=
  fun point => exists coefficient : Q,
    (0 < coefficient)%Q /\
    qvec_eq point (qvec_scale coefficient (zvec_to_qvec base)).

Definition qpositive_ray_formula {d} (base : ZVec d) : QFormula :=
  qexists_many 1
    (QFAnd (QFLt (QTConst 0) (QTVar 0))
      (qformula_all_fin d (fun index =>
        QFEq (QTVar (1 + proj1_sig (Fin.to_nat index)))
          (QTScale (inject_Z (StdVector.nth base index)) (QTVar 0))))).

Lemma qpositive_ray_formula_closed : forall d (base : ZVec d),
    qformula_closed d (qpositive_ray_formula base) = true.
Proof.
  intros d base. unfold qpositive_ray_formula. rewrite qexists_many_closed.
  cbn. apply qformula_all_fin_closed. intro index. cbn.
  apply andb_true_iff. split.
  - apply Nat.ltb_lt.
    replace (1 + proj1_sig (Fin.to_nat index))%nat with
      (S (proj1_sig (Fin.to_nat index))) by lia.
    exact (proj2_sig (Fin.to_nat index)).
  - reflexivity.
Qed.

Lemma qpositive_ray_formula_correct : forall d (base : ZVec d) point,
    PositiveRay base point <->
    qformula_semantics (qvec_environment point) (qpositive_ray_formula base).
Proof.
  intros d base point. unfold PositiveRay, qpositive_ray_formula. split.
  - intros [coefficient [Hpositive Hpoint]].
    apply qexists_many_intro with
      (value := fun _ : Fin.t 1 => coefficient). cbn. split.
    + exact Hpositive.
    + apply (proj2 (qformula_all_fin_correct d _ _)). intro index. cbn.
      rewrite qvec_environment_inside.
      transitivity
        (coefficient * inject_Z (StdVector.nth base index))%Q.
      * exact (Hpoint index).
      * apply Qmult_comm.
  - intro Hformula. apply qexists_many_elim in Hformula as [coefficient Hbody].
    cbn in Hbody. destruct Hbody as [Hpositive Hall].
    rewrite qformula_all_fin_correct in Hall.
    exists (coefficient Fin.F1). split; [exact Hpositive|]. intro index.
    specialize (Hall index). cbn in Hall.
    rewrite qvec_environment_inside in Hall.
    transitivity (inject_Z (StdVector.nth base index) *
      coefficient Fin.F1)%Q; [exact Hall|apply Qmult_comm].
Qed.

Lemma qdefinable_positive_ray : forall d (base : ZVec d),
    QDefinable (PositiveRay base).
Proof.
  intros d base. exists (qpositive_ray_formula base). split.
  - apply qpositive_ray_formula_closed.
  - apply qpositive_ray_formula_correct.
Qed.

Lemma positive_q_as_positive_rat : forall coefficient : Q,
    (0 < coefficient)%Q ->
    exists encoded : PositiveRat, coefficient == positive_value encoded.
Proof.
  intros [numerator denominator] Hpositive. unfold Qlt in Hpositive; cbn in Hpositive.
  assert (Hnumerator : (0 < numerator)%Z) by lia.
  assert (Hnum_nat : (0 < Z.to_nat numerator)%nat).
  { apply (proj2 (Nat2Z.inj_lt 0 _)). rewrite Z2Nat.id by lia. lia. }
  exists {| positive_num := Z.to_nat numerator;
    positive_den := Pos.to_nat denominator;
    positive_num_nonzero := Hnum_nat;
    positive_den_nonzero := Pos2Nat.is_pos denominator |}.
  unfold positive_value, q_of_nat.
  cbn. rewrite Z2Nat.id by lia. rewrite positive_nat_Z.
  apply Qmake_Qdiv.
Qed.

Lemma positive_value_positive : forall coefficient : PositiveRat,
    (0 < positive_value coefficient)%Q.
Proof.
  intros [numerator denominator Hnumerator Hdenominator].
  unfold positive_value, Qdiv. apply Qmult_lt_0_compat.
  - unfold q_of_nat, Qlt. cbn. lia.
  - apply Qinv_lt_0_compat. unfold q_of_nat, Qlt. cbn. lia.
Qed.

Definition almost_component_as_z {d}
    (component : AlmostSemilinearNComponent d) : Component (d + d) :=
  (zpair_pack (nvec_to_zvec (AlmostBaseInput component))
      (nvec_to_zvec (AlmostBaseOutput component)),
    ZRelationPairs (NRelationAsZ (AlmostPeriodRelation component))).

Definition strict_component_branch {d} (component : Component d) : QSet d :=
  fun point => exists coefficient remainder,
    PositiveRay (fst component) coefficient /\
    Cone (snd component) remainder /\
    qvec_eq point (qvec_add coefficient remainder).

Lemma strict_component_branch_qdefinable : forall d component,
    AsymptoticallyDefinable (snd component) ->
    QDefinable (@strict_component_branch d component).
Proof.
  intros d [base period] Hperiod. unfold strict_component_branch; cbn in *.
  apply qdefinable_minkowski_sum; [apply qdefinable_positive_ray|exact Hperiod].
Qed.

Fixpoint strict_component_list {d} (components : list (Component d)) : QSet d :=
  match components with
  | [] => fun _ => False
  | component :: tail => fun point =>
      strict_component_branch component point \/ strict_component_list tail point
  end.

Lemma qdefinable_empty_local : forall d,
    QDefinable (fun _ : QVec d => False).
Proof.
  intro d. exists QFBot. split; [reflexivity|]. intro value. reflexivity.
Qed.

Lemma qdefinable_union_local : forall d (left right : QSet d),
    QDefinable left -> QDefinable right ->
    QDefinable (fun value => left value \/ right value).
Proof.
  intros d left right [lf [Hlc Hl]] [rf [Hrc Hr]].
  exists (QFOr lf rf). split.
  - cbn. now rewrite Hlc, Hrc.
  - intro value. cbn. now rewrite <- Hl, <- Hr.
Qed.

Lemma strict_component_list_qdefinable : forall d components,
    List.Forall (fun component => AsymptoticallyDefinable (snd component))
      components ->
    QDefinable (@strict_component_list d components).
Proof.
  intros d components H; induction H; cbn.
  - apply qdefinable_empty_local.
  - apply qdefinable_union_local;
      [now apply strict_component_branch_qdefinable|exact IHForall].
Qed.

Lemma positive_ray_zero_iff : forall d point,
    PositiveRay (zvec_zero d) point <-> qvec_eq point (qvec_zero d).
Proof.
  intros d point; split.
  - intros [coefficient [_ Hpoint]] index. transitivity
      (qvec_scale coefficient (zvec_to_qvec (zvec_zero d)) index).
    + apply Hpoint.
    + unfold qvec_scale, zvec_to_qvec, zvec_zero, qvec_zero.
      rewrite Vector.const_nth. apply Qmult_0_r.
  - intro Hpoint. exists 1%Q. split; [reflexivity|]. intro index.
    transitivity (qvec_zero d index); [apply Hpoint|].
    unfold qvec_scale, zvec_to_qvec, zvec_zero, qvec_zero.
    rewrite Vector.const_nth. symmetry. apply Qmult_0_r.
Qed.

Lemma strict_component_branch_spec : forall d (base : ZVec d)
    (period : ZVec d -> Prop) point,
    Periodic period ->
    strict_component_branch (base, period) point <->
    exists coefficient : PositiveRat, exists remainder,
      ClearedCone period remainder /\
      qvec_eq point (qvec_add
        (qvec_scale (positive_value coefficient) (zvec_to_qvec base)) remainder).
Proof.
  intros d base period point Hperiod; split.
  - intros [ray [remainder [[coefficient [Hpositive Hray]]
      [Hcone Hpoint]]]].
    destruct (positive_q_as_positive_rat coefficient Hpositive)
      as [encoded Hencoded].
    exists encoded, remainder. split.
    + apply (proj1 (periodic_standard_cone_denominator_clearing d period
        remainder Hperiod)).
      exact Hcone.
    + intro index. transitivity (qvec_add ray remainder index); [apply Hpoint|].
      unfold qvec_add. apply Qplus_comp; [|reflexivity].
      transitivity (coefficient * zvec_to_qvec base index)%Q; [apply Hray|].
      unfold qvec_scale. apply Qmult_comp; [exact Hencoded|reflexivity].
  - intros [encoded [remainder [Hcleared Hpoint]]].
    exists (qvec_scale (positive_value encoded) (zvec_to_qvec base)), remainder.
    repeat split.
    + exists (positive_value encoded). split.
      * apply positive_value_positive.
      * apply qvec_eq_refl.
    + apply (proj2 (periodic_standard_cone_denominator_clearing d period
        remainder Hperiod)).
      exact Hcleared.
    + exact Hpoint.
Qed.

Lemma strict_component_list_spec : forall d
    (components : list (Component d)) (point : QVec d),
    List.Forall (fun component => Periodic (snd component)) components ->
    strict_component_list components point <->
    exists base period, List.In (base, period) components /\
      exists coefficient : PositiveRat, exists remainder,
        ClearedCone period remainder /\
        qvec_eq point (qvec_add
          (qvec_scale (positive_value coefficient) (zvec_to_qvec base)) remainder).
Proof.
  intros d components point H; induction H as [|[base period] tail Hperiod Htail IH]; cbn.
  - split; [contradiction|intros [? [? [Hin _]]]; contradiction].
  - rewrite strict_component_branch_spec by exact Hperiod. rewrite IH. split.
    + intros [Hhead|Hrest].
      * exists base, period. split; [now left|exact Hhead].
      * destruct Hrest as [b [p [Hin Hw]]]. exists b, p. split; [now right|exact Hw].
    + intros [b [p [[Heq|Hin] Hw]]].
      * inversion Heq; subst. now left.
      * right. now exists b, p.
Qed.

Lemma almost_components_periodic : forall d components,
    List.Forall (fun component =>
      AsymptoticallyDefinableNRelation (AlmostPeriodRelation component))
      components ->
    List.Forall (fun component => Periodic (snd component))
      (List.map (@almost_component_as_z d) components).
Proof.
  intros d components H; induction H; cbn; constructor; auto.
  change (Periodic (ZRelationPairs
    (NRelationAsZ (AlmostPeriodRelation x)))).
  apply (proj1 (periodic_zrelation_pairs_iff d _)).
  apply periodic_nrelation_as_z. exact (proj1 H).
Qed.

Lemma almost_components_qdefinable : forall d components,
    List.Forall (fun component =>
      AsymptoticallyDefinableNRelation (AlmostPeriodRelation component))
      components ->
    List.Forall (fun component => AsymptoticallyDefinable (snd component))
      (List.map (@almost_component_as_z d) components).
Proof.
  intros d components H; induction H; cbn; constructor; auto.
  change (QDefinable (RelationConePairs
    (NRelationAsZ (AlmostPeriodRelation x)))). exact (proj2 H).
Qed.

Lemma almost_relation_decomposes : forall d (R : NRelation d) components,
    (forall source target,
      R source target <->
      exists component,
        List.In component components /\
        exists offset_input offset_output,
          AlmostPeriodRelation component offset_input offset_output /\
          source = nvec_add (AlmostBaseInput component) offset_input /\
          target = nvec_add (AlmostBaseOutput component) offset_output) ->
    Decomposes (ZRelationPairs (NRelationAsZ R))
      (List.map (@almost_component_as_z d) components).
Proof.
  intros d R components Hdecomp pair. unfold ZRelationPairs, NRelationAsZ.
  split.
  - intros [source [target [Hleft [Hright HR]]]].
    apply Hdecomp in HR as [component [Hin
      [offset_input [offset_output [Hperiod [Hsource Htarget]]]]]].
    exists (zpair_pack (nvec_to_zvec (AlmostBaseInput component))
      (nvec_to_zvec (AlmostBaseOutput component))),
      (ZRelationPairs (NRelationAsZ (AlmostPeriodRelation component))).
    split.
    + apply in_map_iff. exists component. split; [reflexivity|exact Hin].
    + exists (zpair_pack (nvec_to_zvec offset_input)
        (nvec_to_zvec offset_output)). split.
      * apply (proj2 (zrelation_pairs_pack d _ _ _)).
        exists offset_input, offset_output. repeat split; auto.
      * rewrite <- (zpair_pack_split d pair), Hleft, Hright, Hsource, Htarget.
        rewrite zpair_pack_add, <- !nvec_to_zvec_add. reflexivity.
  - intros [base [period [Hin [offset [Hperiod Heq]]]]].
    apply in_map_iff in Hin as [component [Hcomponent Hin]].
    injection Hcomponent as Hbase Hperiod_set. subst base period.
    unfold ZRelationPairs, NRelationAsZ in Hperiod.
    destruct Hperiod as [offset_input [offset_output
      [Hoffset_left [Hoffset_right Hperiod]]]].
    assert (Hoffset : offset = zpair_pack (nvec_to_zvec offset_input)
        (nvec_to_zvec offset_output)).
    { rewrite <- (zpair_pack_split d offset), Hoffset_left, Hoffset_right.
      reflexivity. }
    subst offset. rewrite zpair_pack_add, <- !nvec_to_zvec_add in Heq.
    exists (nvec_add (AlmostBaseInput component) offset_input),
      (nvec_add (AlmostBaseOutput component) offset_output).
    repeat split.
    + apply (f_equal (@zpair_left d)) in Heq.
      now rewrite zpair_left_pack in Heq.
    + apply (f_equal (@zpair_right d)) in Heq.
      now rewrite zpair_right_pack in Heq.
    + apply Hdecomp. exists component. split; [exact Hin|].
      exists offset_input, offset_output. auto.
Qed.

Lemma qdefinable_qvec_zero : forall d,
    QDefinable (fun point : QVec d => qvec_eq point (qvec_zero d)).
Proof.
  intro d. eapply (@qdefinable_congr d (PositiveRay (zvec_zero d))
    (fun point => qvec_eq point (qvec_zero d))).
  - intro point. apply positive_ray_zero_iff.
  - apply qdefinable_positive_ray.
Qed.

Theorem lemma_4_5_periodic_almost_semilinear_relation : forall d
    (R : NRelation d),
    PeriodicNRelation R -> AlmostSemilinearNRelation R ->
    AsymptoticallyDefinableNRelation R.
Proof.
  intros d R Hperiodic [components [Hasym Hdecomp]]. split.
  - exact Hperiodic.
  - set (geometry := List.map (@almost_component_as_z d) components).
    assert (Hglobal : Periodic (ZRelationPairs (NRelationAsZ R))).
    { apply (proj1 (periodic_zrelation_pairs_iff d _)).
      now apply periodic_nrelation_as_z. }
    assert (Hgeometry_periodic :
        List.Forall (fun component => Periodic (snd component)) geometry).
    { unfold geometry. now apply almost_components_periodic. }
    assert (Hgeometry_def :
        List.Forall (fun component => AsymptoticallyDefinable (snd component))
          geometry).
    { unfold geometry. now apply almost_components_qdefinable. }
    assert (Hdecomposes : Decomposes (ZRelationPairs (NRelationAsZ R)) geometry).
    { unfold geometry. now apply almost_relation_decomposes. }
    eapply (@qdefinable_congr (d + d) (StrictConeUnion geometry)
      (RelationConePairs (NRelationAsZ R))).
    + intro point. symmetry. apply periodic_cone_union_strict; assumption.
    + apply qdefinable_union_local.
      * apply qdefinable_qvec_zero.
      * eapply qdefinable_congr.
        -- intro point. apply strict_component_list_spec. exact Hgeometry_periodic.
        -- now apply strict_component_list_qdefinable.
Qed.

Theorem lemma_4_10_special_transformer_asymptotically_definable : forall d
    (system : IBVAS d) base,
    AsymptoticallyDefinableNRelation (SpecialTransformer system base).
Proof.
  intros d system base. apply lemma_4_5_periodic_almost_semilinear_relation.
  - apply special_transformer_periodic.
  - apply special_transformer_almost_semilinear.
Qed.

(** Period offsets associated with an initialized run (paper Lemma 4.11). *)
Definition IRunPeriod {d} (system : IBVAS d) (root : IRun d)
    (offset : NVec d) : Prop :=
  exists extension,
    ValidIRun system extension /\
    IRunLe root extension /\
    irun_target extension = nvec_add (irun_target root) offset.

Lemma nvec_add_comm_period : forall d (left right : NVec d),
    nvec_add left right = nvec_add right left.
Proof.
  intros d left right. apply StdVector.eq_nth_iff.
  intros index index' <-. unfold nvec_add.
  repeat rewrite (StdVector.nth_map2 _ _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma nvec_add_cancel_left_period : forall d
    (anchor left right : NVec d),
    nvec_add anchor left = nvec_add anchor right -> left = right.
Proof. apply nvec_add_cancel_left_local. Qed.

Theorem irun_period_periodic : forall d (system : IBVAS d) root,
    ValidIRun system root -> PeriodicNSet (IRunPeriod system root).
Proof.
  intros d system root Hroot. split.
  - exists root. split; [exact Hroot|]. split.
    + apply irun_le_refl.
    + symmetry. apply nvec_add_zero_right.
  - intros left right
      [left_run [Hleft_valid [Hleft_order Hleft_target]]]
      [right_run [Hright_valid [Hright_order Hright_target]]].
    destruct (run_amalgamation d system root left_run right_run Hroot
      Hleft_valid Hright_valid Hleft_order Hright_order)
      as [merged [Hmerged_valid [Hleft_merged
        [Hright_merged Hexact]]]].
    exists merged. split; [exact Hmerged_valid|]. split.
    + eapply irun_le_trans; [exact Hleft_order|exact Hleft_merged].
    + apply nvec_add_cancel_left_period with (anchor := irun_target root).
      rewrite Hexact, Hleft_target, Hright_target.
      rewrite !nvec_add_assoc.
      f_equal. rewrite <- nvec_add_assoc.
      rewrite (nvec_add_comm_period d left (irun_target root)).
      rewrite nvec_add_assoc. reflexivity.
Qed.

(** The finite Minkowski sum of the periods attached to a forest.  The empty
    forest contributes the singleton zero, as in Lemma 4.11. *)
Fixpoint ChildPeriodSum {d} (system : IBVAS d) (roots : IRuns d)
    (offset : NVec d) : Prop :=
  match roots with
  | iruns_nil => offset = nvec_zero d
  | iruns_cons root tail =>
      exists head_offset tail_offset,
        IRunPeriod system root head_offset /\
        ChildPeriodSum system tail tail_offset /\
        offset = nvec_add head_offset tail_offset
  end.

Lemma valid_irun_reach_mut : forall d (system : IBVAS d),
  (forall run, ValidIRun system run -> Reach system (irun_target run)) /\
  (forall runs, ValidIRuns system runs ->
    ReachChildren system (iruns_targets runs)).
Proof.
  intros d system. apply ValidIRun_ValidIRuns_mutind_local.
  - intros value Hin. apply In_nth_error in Hin as [index Hindex].
    exact (reach_initial system index value Hindex).
  - intros action children target Haction _ Hchildren Happly.
    apply In_nth_error in Haction as [index Hindex].
    exact (reach_action system index action (iruns_targets children) target
      Hindex Hchildren Happly).
  - constructor.
  - intros run runs _ Hrun _ Hruns. constructor; assumption.
Qed.

Lemma valid_irun_reach : forall d (system : IBVAS d) run,
    ValidIRun system run -> Reach system (irun_target run).
Proof. intros; now apply (proj1 (valid_irun_reach_mut d system) run). Qed.

Lemma reach_valid_irun_mut : forall d (system : IBVAS d),
  (forall value, Reach system value ->
    exists run, ValidIRun system run /\ irun_target run = value) /\
  (forall values, ReachChildren system values ->
    exists runs, ValidIRuns system runs /\ iruns_targets runs = values).
Proof.
  intros d system. apply Reach_mutind.
  - intros index value Hinitial. exists (irun_leaf value). split; [|reflexivity].
    constructor. now apply nth_error_In in Hinitial.
  - intros index action children value Haction _
      [child_runs [Hchild_valid Hchild_targets]] Happly.
    exists (irun_node action child_runs value). split; [|reflexivity].
    constructor.
    + now apply nth_error_In in Haction.
    + exact Hchild_valid.
    + now rewrite Hchild_targets.
  - exists iruns_nil. split; [constructor|reflexivity].
  - intros value values _ [run [Hrun run_target]] _
      [runs [Hruns Eruns]].
    exists (iruns_cons run runs). split; [constructor; assumption|].
    cbn. now rewrite run_target, Eruns.
Qed.

Lemma reach_forall_to_valid_iruns : forall d (system : IBVAS d) values,
    List.Forall (Reach system) values ->
    exists runs,
      ValidIRuns system runs /\ iruns_targets runs = values.
Proof.
  intros d system values Hreach.
  assert (Hchildren : ReachChildren system values).
  { induction Hreach; constructor; assumption. }
  now apply (proj2 (reach_valid_irun_mut d system) values).
Qed.

Lemma valid_iruns_forall_reach : forall d (system : IBVAS d) runs,
    ValidIRuns system runs ->
    List.Forall (Reach system) (iruns_targets runs).
Proof.
  intros d system runs Hvalid. induction Hvalid; cbn; constructor; auto.
  now apply valid_irun_reach.
Qed.

Lemma iruns_in_frame_here : forall d (before after : IRuns d) run,
    IRunsIn run (iruns_append before (iruns_cons run after)).
Proof.
  intros d before. induction before; intros; cbn; constructor; auto.
Qed.

Lemma valid_iruns_append_inv : forall d (system : IBVAS d) left right,
    ValidIRuns system (iruns_append left right) ->
    ValidIRuns system left /\ ValidIRuns system right.
Proof.
  intros d system left. induction left; intros right Hvalid; cbn in Hvalid.
  - split; [constructor|exact Hvalid].
  - inversion Hvalid as [|run runs Hrun Hruns]; subst.
    destruct (IHleft right Hruns).
    split; [constructor; assumption|assumption].
Qed.

Lemma valid_iruns_append_intro : forall d (system : IBVAS d) left right,
    ValidIRuns system left -> ValidIRuns system right ->
    ValidIRuns system (iruns_append left right).
Proof.
  intros d system left. induction left; intros right Hleft Hright; cbn.
  - exact Hright.
  - inversion Hleft as [|run runs Hrun Hruns]; subst.
    constructor; [exact Hrun|]. now apply IHleft.
Qed.

Lemma valid_context_special_leaf : forall d (system : IBVAS d)
    context matched,
    ValidIRun system (context_plug context matched) ->
    SpecialLeafReach system (irun_target matched)
      (irun_target (context_plug context matched)).
Proof.
  intros d system context. induction context as
    [|action before inner IH after target]; intros matched Hvalid; cbn in *.
  - constructor.
  - inversion Hvalid as [|? ? ? Haction Hchildren Happly]; subst.
    assert (Hinner : ValidIRun system (context_plug inner matched)).
    { eapply valid_iruns_frame_member; eauto. }
    eapply special_action with
      (action := action)
      (prefix := iruns_targets before)
      (middle := irun_target (context_plug inner matched))
      (suffix := iruns_targets after).
    + exact Haction.
    + apply valid_iruns_forall_reach.
      exact (proj1 (valid_iruns_append_inv d system before
        (iruns_cons (context_plug inner matched) after) Hchildren)).
    + now apply IH.
    + apply valid_iruns_forall_reach.
      pose proof (proj2 (valid_iruns_append_inv d system before
        (iruns_cons (context_plug inner matched) after) Hchildren)) as Hrest.
      inversion Hrest; assumption.
    + now rewrite !iruns_targets_append in Happly.
Qed.

Lemma special_leaf_wrap_embed : forall d (system : IBVAS d)
    input output (base matched : IRun d),
    ValidIRun system matched ->
    irun_target matched = input ->
    IRunEmbed base matched ->
    SpecialLeafReach system input output ->
    exists whole,
      ValidIRun system whole /\
      irun_target whole = output /\
      IRunEmbed base whole.
Proof.
  intros d system input output base matched Hmatched Htarget Hembed Hreach.
  revert base matched Hmatched Htarget Hembed.
  induction Hreach as
    [input|input action prefix middle suffix output Haction Hprefix
      Hmiddle IH Hsuffix Happly]; intros base matched Hmatched Htarget Hembed.
  - exists matched. auto.
  - destruct (IH base matched Hmatched Htarget Hembed)
      as [middle_run [Hmiddle_valid [Hmiddle_target Hmiddle_embed]]].
    destruct (reach_forall_to_valid_iruns d system prefix Hprefix)
      as [before [Hbefore Ebefore]].
    destruct (reach_forall_to_valid_iruns d system suffix Hsuffix)
      as [after [Hafter Eafter]].
    exists (irun_node action
      (iruns_append before (iruns_cons middle_run after)) output).
    split.
    + constructor; [exact Haction| |].
      * apply valid_iruns_append_intro; [exact Hbefore|].
        constructor; assumption.
      * rewrite iruns_targets_append, Ebefore. cbn.
        now rewrite Hmiddle_target, Eafter.
    + split; [reflexivity|].
      eapply embed_below.
      * apply iruns_in_frame_here.
      * exact Hmiddle_embed.
Qed.

Lemma child_period_sum_of_embed : forall d (system : IBVAS d)
    (roots extensions : IRuns d),
    ValidIRuns system roots ->
    ValidIRuns system extensions ->
    IRunsEmbed roots extensions ->
    exists offset,
      ChildPeriodSum system roots offset /\
      nvec_sum (iruns_targets extensions) =
        nvec_add (nvec_sum (iruns_targets roots)) offset.
Proof.
  intros d system roots extensions Hroots Hextensions Hembed.
  induction Hembed as
    [|left right lefts rights Hle Hrun_embed Htail_embed IH].
  - exists (nvec_zero d). split; [reflexivity|].
    symmetry. apply nvec_add_zero_right.
  - inversion Hroots as [|? ? Hleft Hlefts]; subst.
    inversion Hextensions as [|? ? Hright Hrights]; subst.
    destruct (nvec_difference_checked_correct d
      (irun_target left) (irun_target right) Hle)
      as [head_offset [_ Hhead]].
    destruct (IH Hlefts Hrights)
      as [tail_offset [Htail Htail_sum]].
    exists (nvec_add head_offset tail_offset). split.
    + cbn. exists head_offset, tail_offset. split.
      * exists right. split; [exact Hright|]. split.
        -- split; [exact Hle|exact Hrun_embed].
        -- exact Hhead.
      * split; reflexivity || assumption.
    + repeat rewrite nvec_sum_rsum in Htail_sum |- *.
      cbn. rewrite Hhead, Htail_sum.
      apply StdVector.eq_nth_iff. intros index index' <-.
      unfold nvec_add.
      repeat rewrite (StdVector.nth_map2 _ _ _ index index index
        eq_refl eq_refl).
      lia.
Qed.

Lemma root_embed_child_period_sum : forall d (system : IBVAS d)
    root matched,
    ValidIRun system root -> ValidIRun system matched ->
    RootEmbed root matched ->
    exists offset,
      (match root with
       | irun_leaf _ => offset = nvec_zero d
       | irun_node _ children _ => ChildPeriodSum system children offset
       end) /\
      irun_target matched = nvec_add (irun_target root) offset.
Proof.
  intros d system root matched Hroot Hmatched Hembed.
  inversion Hembed as [value|action roots extensions root_target matched_target
    Htarget_le Hchildren]; subst.
  - exists (nvec_zero d). split; [reflexivity|].
    symmetry. apply nvec_add_zero_right.
  - inversion Hroot as [|? ? ? Haction_root Hroots Happly_root]; subst.
    inversion Hmatched as [|? ? ? Haction_matched Hextensions Happly_matched]; subst.
    destruct (child_period_sum_of_embed d system roots extensions
      Hroots Hextensions Hchildren) as [offset [Hperiods Hsum]].
    exists offset. split; [exact Hperiods|].
    eapply apply_action_sum_shift in Happly_root.
    + rewrite Happly_matched in Happly_root. now inversion Happly_root.
    + now apply iruns_embed_lengths in Hchildren.
    + exact Hsum.
Qed.

Definition RootChildPeriodSum {d} (system : IBVAS d) (root : IRun d)
    (offset : NVec d) : Prop :=
  match root with
  | irun_leaf _ => offset = nvec_zero d
  | irun_node _ children _ => ChildPeriodSum system children offset
  end.

Lemma child_period_sum_realize : forall d (system : IBVAS d) roots offset,
    ValidIRuns system roots ->
    ChildPeriodSum system roots offset ->
    exists extensions,
      ValidIRuns system extensions /\
      IRunsLe roots extensions /\
      nvec_sum (iruns_targets extensions) =
        nvec_add (nvec_sum (iruns_targets roots)) offset.
Proof.
  intros d system roots. induction roots as [|root tail IH];
    intros offset Hvalid Hperiod.
  - cbn in Hperiod. subst offset. exists iruns_nil. split.
    + constructor.
    + split.
      * exact I.
      * symmetry. apply nvec_add_zero_right.
  - inversion Hvalid as [|? ? Hroot Htail]; subst.
    cbn in Hperiod. destruct Hperiod as
      [head_offset [tail_offset [Hhead [Htail_period Hoff]]]].
    destruct Hhead as [head_extension
      [Hhead_valid [Hhead_le Hhead_target]]].
    destruct (IH tail_offset Htail Htail_period) as
      [tail_extensions [Htail_valid [Htail_le Htail_sum]]].
    exists (iruns_cons head_extension tail_extensions). split.
    + constructor; assumption.
    + split.
      * split; [exact Hhead_le|exact Htail_le].
      * subst offset. repeat rewrite nvec_sum_rsum in Htail_sum |- *.
        cbn. rewrite Hhead_target, Htail_sum.
        apply StdVector.eq_nth_iff. intros index index' <-.
        unfold nvec_add.
        repeat rewrite (StdVector.nth_map2 _ _ _ index index index
          eq_refl eq_refl). lia.
Qed.

Lemma root_child_period_sum_realize : forall d (system : IBVAS d)
    root offset,
    ValidIRun system root ->
    RootChildPeriodSum system root offset ->
    exists matched,
      ValidIRun system matched /\
      IRunLe root matched /\
      irun_target matched = nvec_add (irun_target root) offset.
Proof.
  intros d system root offset Hvalid Hperiod.
  destruct root as [value|action children target].
  - cbn in Hperiod. subst offset. exists (irun_leaf value). split.
    + exact Hvalid.
    + split; [apply irun_le_refl|]. symmetry. apply nvec_add_zero_right.
  - inversion Hvalid as [|? ? ? Haction Hchildren Happly]; subst.
    destruct (child_period_sum_realize d system children offset
      Hchildren Hperiod) as
      [extensions [Hextensions [Hchildren_le Hsum]]].
    exists (irun_node action extensions (nvec_add target offset)). split.
    + constructor; try assumption.
      eapply apply_action_sum_shift; [|exact Hsum|exact Happly].
      apply iruns_embed_lengths. now apply iruns_le_embed.
    + split.
      * eapply root_same_action_mono; eauto.
        eapply apply_action_sum_shift; [|exact Hsum|exact Happly].
        apply iruns_embed_lengths. now apply iruns_le_embed.
      * reflexivity.
Qed.

Theorem irun_period_structural_decomposition : forall d
    (system : IBVAS d) root,
    ValidIRun system root -> forall output_offset,
    IRunPeriod system root output_offset <->
    exists input_offset,
      RootChildPeriodSum system root input_offset /\
      SpecialTransformer system (irun_target root)
        input_offset output_offset.
Proof.
  intros d system root Hroot output_offset. split.
  - intros [whole [Hwhole [Horder Hwhole_target]]].
    destruct (embed_decompose d root whole Horder)
      as [context [matched [Hplug [Hroot_embed _]]]].
    subst whole.
    assert (Hmatched : ValidIRun system matched).
    { eapply context_valid_inner; eauto. }
    destruct (root_embed_child_period_sum d system root matched
      Hroot Hmatched Hroot_embed) as [input_offset [Hchildren Hmatched_target]].
    exists input_offset. split.
    + unfold RootChildPeriodSum. exact Hchildren.
    + unfold SpecialTransformer.
      rewrite <- Hmatched_target, <- Hwhole_target.
      now apply valid_context_special_leaf.
  - intros [input_offset [Hchildren Htransformer]].
    destruct (root_child_period_sum_realize d system root input_offset
      Hroot Hchildren) as [matched [Hmatched [Hroot_matched Hmatched_target]]].
    unfold SpecialTransformer in Htransformer.
    destruct (special_leaf_wrap_embed d system
      (nvec_add (irun_target root) input_offset)
      (nvec_add (irun_target root) output_offset)
      root matched Hmatched Hmatched_target (proj2 Hroot_matched) Htransformer)
      as [whole [Hwhole [Hwhole_target Hembed]]].
    exists whole. split; [exact Hwhole|]. split.
    + split.
      * rewrite Hwhole_target. apply nvec_le_add_right.
      * exact Hembed.
    + exact Hwhole_target.
Qed.

Definition ZSetMinkowski {d} (left right : ZSet d) : ZSet d :=
  fun value => exists left_value right_value,
    left left_value /\ right right_value /\
    value = zvec_add left_value right_value.

Lemma periodic_zset_minkowski : forall d (left right : ZSet d),
    Periodic left -> Periodic right ->
    Periodic (ZSetMinkowski left right).
Proof.
  intros d left right [Hl0 Hladd] [Hr0 Hradd]. split.
  - exists (zvec_zero d), (zvec_zero d). repeat split; auto.
    symmetry. apply zvec_add_zero_left.
  - intros x y [xl [xr [Hxl [Hxr ->]]]] [yl [yr [Hyl [Hyr ->]]]].
    exists (zvec_add xl yl), (zvec_add xr yr). repeat split; auto.
    apply StdVector.eq_nth_iff. intros index index' <-. unfold zvec_add.
    repeat rewrite (StdVector.nth_map2 _ _ _ index index index
      eq_refl eq_refl). lia.
Qed.

Theorem periodic_cone_minkowski : forall d (left right : ZSet d),
    Periodic left -> Periodic right -> forall point,
    Cone (ZSetMinkowski left right) point <->
    exists left_point right_point,
      Cone left left_point /\ Cone right right_point /\
      qvec_eq point (qvec_add left_point right_point).
Proof.
  intros d left right Hleft Hright point. split.
  - intro Hsum.
    apply (proj1 (periodic_cone_positive_multiple_iff d
      (ZSetMinkowski left right) point
      (periodic_zset_minkowski d left right Hleft Hright))) in Hsum.
    destruct Hsum as [multiplier [integer_sum
      [Hpositive [[integer_left [integer_right
        [Hinteger_left [Hinteger_right Hsum]]]] Hpoint]]]].
    subst integer_sum.
    exists (qvec_scale (/ q_of_nat multiplier) (zvec_to_qvec integer_left)),
      (qvec_scale (/ q_of_nat multiplier) (zvec_to_qvec integer_right)).
    repeat split.
    + apply (proj2 (periodic_cone_positive_multiple_iff d left _ Hleft)).
      exists multiplier, integer_left. repeat split; try assumption.
      intro index. unfold qvec_scale, q_of_nat. field.
      now apply q_of_nat_nonzero.
    + apply (proj2 (periodic_cone_positive_multiple_iff d right _ Hright)).
      exists multiplier, integer_right. repeat split; try assumption.
      intro index. unfold qvec_scale, q_of_nat. field.
      now apply q_of_nat_nonzero.
    + intro index. pose proof (Hpoint index) as Hpoint_index.
      unfold qvec_scale, qvec_add, zvec_to_qvec, zvec_add in *.
      rewrite (StdVector.nth_map2 _ _ _ index index index
        eq_refl eq_refl), inject_Z_plus in Hpoint_index.
      transitivity (/ q_of_nat multiplier *
        (q_of_nat multiplier * point index)).
      * field. now apply q_of_nat_nonzero.
      * rewrite Hpoint_index. ring.
  - intros [left_point [right_point [Hleft_cone
      [Hright_cone Hpoint]]]].
    apply (proj1 (periodic_cone_positive_multiple_iff d left left_point Hleft))
      in Hleft_cone.
    apply (proj1 (periodic_cone_positive_multiple_iff d right right_point Hright))
      in Hright_cone.
    destruct Hleft_cone as [left_multiplier [integer_left
      [Hleft_positive [Hinteger_left Hleft_point]]]].
    destruct Hright_cone as [right_multiplier [integer_right
      [Hright_positive [Hinteger_right Hright_point]]]].
    apply (proj2 (periodic_cone_positive_multiple_iff d
      (ZSetMinkowski left right) point
      (periodic_zset_minkowski d left right Hleft Hright))).
    exists (left_multiplier * right_multiplier)%nat,
      (zvec_add (zvec_nsmul right_multiplier integer_left)
        (zvec_nsmul left_multiplier integer_right)).
    split; [nia|]. split.
    + exists (zvec_nsmul right_multiplier integer_left),
        (zvec_nsmul left_multiplier integer_right). split.
      * now apply (periodic_nsmul d left Hleft).
      * split.
        -- now apply (periodic_nsmul d right Hright).
        -- reflexivity.
    + eapply qvec_eq_trans with
        (y := qvec_scale (q_of_nat (left_multiplier * right_multiplier))
          (qvec_add left_point right_point)).
      * intro index. unfold qvec_scale.
        apply Qmult_comp; [reflexivity|exact (Hpoint index)].
      * intro index. unfold qvec_scale, qvec_add, zvec_to_qvec, zvec_add.
        rewrite (StdVector.nth_map2 _ _ _ index index index
          eq_refl eq_refl), inject_Z_plus, !nth_zvec_nsmul,
          !inject_Z_mult.
        pose proof (Hleft_point index) as Hl.
        pose proof (Hright_point index) as Hr.
        unfold qvec_scale in Hl, Hr. unfold q_of_nat in *.
        rewrite Nat2Z.inj_mul, inject_Z_mult.
        transitivity
          (inject_Z (Z.of_nat right_multiplier) *
             (inject_Z (Z.of_nat left_multiplier) * left_point index) +
           inject_Z (Z.of_nat left_multiplier) *
             (inject_Z (Z.of_nat right_multiplier) * right_point index)).
        -- ring.
        -- setoid_rewrite Hl. setoid_rewrite Hr. reflexivity.
Qed.

Definition NSetMinkowski {d} (left right : NVec d -> Prop) : NVec d -> Prop :=
  fun value => exists left_value right_value,
    left left_value /\ right right_value /\
    value = nvec_add left_value right_value.

Lemma periodic_nset_minkowski : forall d (left right : NVec d -> Prop),
    PeriodicNSet left -> PeriodicNSet right ->
    PeriodicNSet (NSetMinkowski left right).
Proof.
  intros d left right [Hl0 Hladd] [Hr0 Hradd]. split.
  - exists (nvec_zero d), (nvec_zero d). repeat split; auto.
    symmetry. apply nvec_add_zero_left.
  - intros x y [xl [xr [Hxl [Hxr ->]]]] [yl [yr [Hyl [Hyr ->]]]].
    exists (nvec_add xl yl), (nvec_add xr yr). repeat split; auto.
    apply StdVector.eq_nth_iff. intros index index' <-. unfold nvec_add.
    repeat rewrite (StdVector.nth_map2 _ _ _ index index index
      eq_refl eq_refl). lia.
Qed.

Lemma nset_as_z_minkowski : forall d (left right : NVec d -> Prop) value,
    NSetAsZ (NSetMinkowski left right) value <->
    ZSetMinkowski (NSetAsZ left) (NSetAsZ right) value.
Proof.
  intros d left right value. split.
  - intros [natural [-> [l [r [Hl [Hr ->]]]]]].
    exists (nvec_to_zvec l), (nvec_to_zvec r). repeat split.
    + now exists l.
    + now exists r.
    + apply nvec_to_zvec_add.
  - intros [zl [zr [[l [-> Hl]] [[r [-> Hr]] Hvalue]]]].
    exists (nvec_add l r). split; [|exists l, r; auto].
    now rewrite nvec_to_zvec_add.
Qed.

Lemma asymptotic_nset_congr : forall d (left right : NVec d -> Prop),
    (forall value, left value <-> right value) ->
    AsymptoticallyDefinableNSet left ->
    AsymptoticallyDefinableNSet right.
Proof.
  intros d left right Hsame [Hperiodic Hdef]. split.
  - split.
    + apply Hsame, Hperiodic.
    + intros x y Hx Hy. apply Hsame. apply Hperiodic;
        [now apply Hsame|now apply Hsame].
  - eapply qdefinable_congr; [|exact Hdef]. intro point.
    apply cone_same_generators. intro integer. split;
      intros [natural [Heq Hmember]]; exists natural; split; auto;
      [now apply Hsame|now apply Hsame].
Qed.

Theorem asymptotically_definable_nset_minkowski : forall d
    (left right : NVec d -> Prop),
    AsymptoticallyDefinableNSet left ->
    AsymptoticallyDefinableNSet right ->
    AsymptoticallyDefinableNSet (NSetMinkowski left right).
Proof.
  intros d left right [Hlperiodic Hldef] [Hrperiodic Hrdef]. split.
  - now apply periodic_nset_minkowski.
  - assert (Hsumdef : QDefinable (fun point => exists lp rp,
        Cone (NSetAsZ left) lp /\ Cone (NSetAsZ right) rp /\
        qvec_eq point (qvec_add lp rp))).
    { now apply qdefinable_minkowski_sum. }
    eapply qdefinable_congr; [|exact Hsumdef]. intro point.
    rewrite <- (periodic_cone_minkowski d (NSetAsZ left) (NSetAsZ right)
      (periodic_nset_as_z d left Hlperiodic)
      (periodic_nset_as_z d right Hrperiodic) point).
    apply cone_same_generators. intro integer.
    symmetry. apply nset_as_z_minkowski.
Qed.

Lemma singleton_zero_asymptotically_definable : forall d,
    AsymptoticallyDefinableNSet
      (fun value : NVec d => value = nvec_zero d).
Proof.
  intro d. split.
  - split; [reflexivity|]. intros left right -> ->.
    exact (nvec_add_zero_left d (nvec_zero d)).
  - eapply (@qdefinable_congr d
      (fun point => qvec_eq point (qvec_zero d))
      (Cone (NSetAsZ (fun value : NVec d => value = nvec_zero d))));
      [|apply qdefinable_qvec_zero]. intro point.
    split.
    + intro Hzero. exists (qvec_zero d). split; [constructor|exact Hzero].
    + intros [generated [Hgenerated Hpoint]].
      eapply qvec_eq_trans; [exact Hpoint|]. clear Hpoint point.
      induction Hgenerated.
      * apply qvec_eq_refl.
      * destruct H0 as [natural [-> Hzero]]. subst natural.
        eapply qvec_eq_trans; [|exact IHHgenerated].
        intro index. unfold qvec_add, qvec_scale, zvec_to_qvec,
          nvec_to_zvec, nvec_zero.
        rewrite (StdVector.nth_map _ _ index index eq_refl),
          (StdVector.const_nth nat 0%nat d index). ring.
Qed.

Lemma child_period_sum_asymptotic : forall d (system : IBVAS d) roots,
    (forall root, IRunsIn root roots ->
      AsymptoticallyDefinableNSet (IRunPeriod system root)) ->
    AsymptoticallyDefinableNSet (ChildPeriodSum system roots).
Proof.
  intros d system roots. induction roots as [|root tail IH]; intro Hall.
  - apply singleton_zero_asymptotically_definable.
  - apply (asymptotic_nset_congr d
      (NSetMinkowski (IRunPeriod system root)
        (ChildPeriodSum system tail))).
    + intro value. cbn. reflexivity.
    + apply asymptotically_definable_nset_minkowski.
      * apply Hall. constructor.
      * apply IH. intros child Hin. apply Hall. now constructor 2.
Qed.

Definition ZeroSourceRelation {d} (set : NVec d -> Prop) : NRelation d :=
  fun source target => source = nvec_zero d /\ set target.

Lemma zero_source_relation_periodic : forall d (set : NVec d -> Prop),
    PeriodicNSet set -> PeriodicNRelation (ZeroSourceRelation set).
Proof.
  intros d set [Hzero Hadd]. split.
  - split; reflexivity || exact Hzero.
  - intros s1 t1 s2 t2 [-> H1] [-> H2]. split.
    + apply nvec_add_zero_left.
    + now apply Hadd.
Qed.

Lemma zero_source_relation_cone : forall d (set : NVec d -> Prop),
    PeriodicNSet set -> forall source target,
    RationalRelationCone (NRelationAsZ (ZeroSourceRelation set)) source target
    <-> qvec_eq source (qvec_zero d) /\ Cone (NSetAsZ set) target.
Proof.
  intros d set Hperiodic source target. split.
  - intro Hcone.
    apply (proj1 (periodic_relation_cone_positive_multiple_iff d _ _ _
      (periodic_nrelation_as_z d _
        (zero_source_relation_periodic d set Hperiodic)))) in Hcone.
    destruct Hcone as [multiplier [integer_source [integer_target
      [Hpositive [Hrelation [Hsource Htarget]]]]]].
    destruct Hrelation as [natural_source [natural_target
      [Esource [Etarget [Hnatural_source Hset]]]]].
    subst natural_source integer_source integer_target. split.
    + intro index. pose proof (Hsource index) as Hcoordinate.
      unfold qvec_scale, zvec_to_qvec, nvec_to_zvec, nvec_zero in Hcoordinate.
      rewrite (StdVector.nth_map _ _ index index eq_refl),
        (StdVector.const_nth nat 0%nat d index) in Hcoordinate.
      unfold q_of_nat in Hcoordinate. cbn in Hcoordinate.
      apply (Qmult_integral _ _) in Hcoordinate as [Hzero|Hzero].
      * exfalso. apply (q_of_nat_nonzero multiplier Hpositive). exact Hzero.
      * exact Hzero.
    + apply (proj2 (periodic_cone_positive_multiple_iff d
        (NSetAsZ set) target (periodic_nset_as_z d set Hperiodic))).
      exists multiplier, (nvec_to_zvec natural_target). split; [exact Hpositive|].
      split.
      * exists natural_target. auto.
      * exact Htarget.
  - intros [Hzero_source Htarget_cone].
    apply (proj1 (periodic_cone_positive_multiple_iff d
      (NSetAsZ set) target (periodic_nset_as_z d set Hperiodic)))
      in Htarget_cone.
    destruct Htarget_cone as [multiplier [integer_target
      [Hpositive [Hinteger_target Htarget_scaled]]]].
    apply (proj2 (periodic_relation_cone_positive_multiple_iff d _ source target
      (periodic_nrelation_as_z d _
        (zero_source_relation_periodic d set Hperiodic)))).
    exists multiplier, (zvec_zero d), integer_target. split; [exact Hpositive|].
    split.
    + destruct Hinteger_target as [natural_target [Etarget Hset]].
      exists (nvec_zero d), natural_target. repeat split; auto.
      apply StdVector.eq_nth_iff. intros index index' <-.
      unfold nvec_to_zvec, nvec_zero, zvec_zero.
      rewrite (StdVector.nth_map _ _ index index eq_refl),
        (StdVector.const_nth nat 0%nat d index),
        (StdVector.const_nth Z 0%Z d index). reflexivity.
    + split.
      * intro index. unfold qvec_scale, zvec_to_qvec, zvec_zero.
        rewrite (StdVector.const_nth Z 0%Z d index).
        rewrite (Hzero_source index). unfold qvec_zero. ring.
      * exact Htarget_scaled.
Qed.

Theorem zero_source_relation_asymptotic : forall d
    (set : NVec d -> Prop),
    AsymptoticallyDefinableNSet set ->
    AsymptoticallyDefinableNRelation (ZeroSourceRelation set).
Proof.
  intros d set [Hperiodic Hdef]. split.
  - now apply zero_source_relation_periodic.
  - assert (Hsource_zero : QDefinable (fun pair : QVec (d + d) =>
        qvec_eq (qpair_left pair) (qvec_zero d))).
    { pose proof (qdefinable_coordinate_preimage d (d + d)
        (fun index => Fin.L d index)
        (fun point => qvec_eq point (qvec_zero d))
        (qdefinable_qvec_zero d)) as Hpre.
      eapply qdefinable_congr; [|exact Hpre]. intro pair. split;
        intros H index.
      - transitivity (pair (Fin.L d index));
          [apply qpair_left_coordinate|exact (H index)].
      - transitivity (qpair_left pair index);
          [symmetry; apply qpair_left_coordinate|exact (H index)]. }
    assert (Htarget_set : QDefinable (fun pair : QVec (d + d) =>
        Cone (NSetAsZ set) (qpair_right pair))).
    { pose proof (qdefinable_coordinate_preimage d (d + d)
        (fun index => Fin.R d index) (Cone (NSetAsZ set)) Hdef) as Hpre.
      eapply qdefinable_congr; [|exact Hpre]. intro pair.
      apply cone_qvec_extensional. intro index.
      symmetry. apply qpair_right_coordinate. }
    pose proof (qdefinable_intersection (d + d) _ _
      Hsource_zero Htarget_set) as Hintersection.
    eapply qdefinable_congr; [|exact Hintersection]. intro pair.
    rewrite relation_cone_pairs_unpack.
    symmetry. apply zero_source_relation_cone. exact Hperiodic.
Qed.

Lemma irun_period_asymptotic_from_children : forall d
    (system : IBVAS d) root,
    ValidIRun system root ->
    AsymptoticallyDefinableNSet (RootChildPeriodSum system root) ->
    AsymptoticallyDefinableNSet (IRunPeriod system root).
Proof.
  intros d system root Hvalid Hchildren.
  pose proof (zero_source_relation_asymptotic d
    (RootChildPeriodSum system root) Hchildren) as Hzero.
  pose proof (lemma_5_1_nrelation_compose d
    (ZeroSourceRelation (RootChildPeriodSum system root))
    (SpecialTransformer system (irun_target root)) Hzero
    (lemma_4_10_special_transformer_asymptotically_definable
      d system (irun_target root))) as Hcompose.
  pose proof (asymptotically_definable_nrelation_target_projection d _
    Hcompose) as Hprojection.
  apply (asymptotic_nset_congr d
    (NRelationTargetProjection
      (NRelCompose (ZeroSourceRelation (RootChildPeriodSum system root))
        (SpecialTransformer system (irun_target root))))
    (IRunPeriod system root)); [|exact Hprojection].
  intro output. unfold NRelationTargetProjection, NRelCompose,
    ZeroSourceRelation. rewrite irun_period_structural_decomposition by exact Hvalid.
  split.
  - intros [source [middle [[_ Hchild] Htransformer]]].
    exists middle. auto.
  - intros [middle [Hchild Htransformer]].
    exists (nvec_zero d), middle. auto.
Qed.

Theorem irun_period_asymptotic_mut : forall d (system : IBVAS d),
  (forall root, ValidIRun system root ->
    AsymptoticallyDefinableNSet (IRunPeriod system root)) /\
  (forall roots, ValidIRuns system roots ->
    AsymptoticallyDefinableNSet (ChildPeriodSum system roots)).
Proof.
  intros d system. apply IRun_IRuns_ind.
  - intros value Hvalid. apply irun_period_asymptotic_from_children;
      [exact Hvalid|].
    change (AsymptoticallyDefinableNSet
      (fun offset : NVec d => offset = nvec_zero d)).
    apply singleton_zero_asymptotically_definable.
  - intros action children Hchildren_asym target Hvalid.
    apply irun_period_asymptotic_from_children; [exact Hvalid|].
    change (AsymptoticallyDefinableNSet (ChildPeriodSum system children)).
    inversion Hvalid; subst. now apply Hchildren_asym.
  - intros _. apply singleton_zero_asymptotically_definable.
  - intros root Hroot_asym tail Htail_asym Hvalid.
    inversion Hvalid as [|? ? Hroot_valid Htail_valid]; subst.
    apply (asymptotic_nset_congr d
      (NSetMinkowski (IRunPeriod system root)
        (ChildPeriodSum system tail))).
    + intro value. cbn. reflexivity.
    + apply asymptotically_definable_nset_minkowski;
        [now apply Hroot_asym|now apply Htail_asym].
Qed.

Theorem lemma_4_11_irun_period_asymptotically_definable : forall d
    (system : IBVAS d) root,
    ValidIRun system root ->
    AsymptoticallyDefinableNSet (IRunPeriod system root).
Proof.
  intros d system root Hvalid.
  now apply (proj1 (irun_period_asymptotic_mut d system) root).
Qed.
