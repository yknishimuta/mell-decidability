From Coq Require Import List Lia QArith Vector VectorSpec ZArith.
From KruskalAfProp Require Import af.af af.af_tools.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge Periodic Cone QConeCore
  RationalDefinability LatticeGordanH LatticeGordanInterface.
From Mell.Order Require Import PeriodicOrder.

Open Scope Z_scope.

Definition zvec_opp {d} (value : ZVec d) : ZVec d :=
  Vector.map Z.opp value.

Definition Difference {d} (set : ZSet d) : ZSet d :=
  fun value => exists left right,
    set left /\ set right /\ value = zvec_sub left right.

Record IntegerAdditiveGroup {d} (set : ZSet d) : Prop := {
  integer_group_zero : set (zvec_zero d);
  integer_group_add : forall left right,
    set left -> set right -> set (zvec_add left right);
  integer_group_opp : forall value, set value -> set (zvec_opp value)
}.

Definition QSetExtensional {d} (set : QSet d) : Prop :=
  forall left right, QVecEq left right -> (set left <-> set right).

Record RationalCone {d} (set : QSet d) : Prop := {
  rational_cone_is_cone : IsCone set;
  rational_cone_extensional : QSetExtensional set
}.

Definition Linearization {d} (set : ZSet d) : ZSet d :=
  fun value =>
    Difference set value /\ Cone set (zvec_to_qvec value).

Definition ClosedLinearization {d} (set : ZSet d) : ZSet d :=
  fun value =>
    Difference set value /\
    QClosure (Cone set) (zvec_to_qvec value).

Lemma closed_linearization_spec : forall d (set : ZSet d) value,
    ClosedLinearization set value <->
    Difference set value /\ QClosure (Cone set) (zvec_to_qvec value).
Proof. reflexivity. Qed.

Definition FullPeriodic {d} (set : ZSet d) : Prop :=
  Periodic set /\
  exists (group : ZSet d) (cone : QSet d),
    IntegerAdditiveGroup group /\ RationalCone cone /\
    SameSet set
      (fun value : ZVec d => group value /\ cone (zvec_to_qvec value)).

Definition PolyhedralFullPeriodic {d} (set : ZSet d) : Prop :=
  Periodic set /\
  exists (group : ZSet d) (cone : QSet d),
    FinitelyGeneratedGroup group /\ RationalPolyhedralCone cone /\
    SameSet set
      (fun value : ZVec d => group value /\ cone (zvec_to_qvec value)).

Definition AsymptoticallyDefinable {d} (set : ZSet d) : Prop :=
  QDefinable (Cone set).

Lemma zvec_sub_self : forall d (value : ZVec d),
    zvec_sub value value = zvec_zero d.
Proof.
  intros d value. apply zvec_ext. intro index.
  unfold zvec_sub, zvec_zero.
  rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl), const_nth.
  lia.
Qed.

Lemma zvec_opp_sub : forall d (left right : ZVec d),
    zvec_opp (zvec_sub left right) = zvec_sub right left.
Proof.
  intros d left right. apply zvec_ext. intro index.
  unfold zvec_opp, zvec_sub.
  rewrite (nth_map _ _ index index eq_refl).
  repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma zvec_add_sub_distribute : forall d
    (left1 right1 left2 right2 : ZVec d),
    zvec_add (zvec_sub left1 right1) (zvec_sub left2 right2) =
      zvec_sub (zvec_add left1 left2) (zvec_add right1 right2).
Proof.
  intros d left1 right1 left2 right2. apply zvec_ext. intro index.
  unfold zvec_add, zvec_sub.
  repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma difference_zero : forall d (set : ZSet d),
    Periodic set -> Difference set (zvec_zero d).
Proof.
  intros d set [Hzero Hadd]. exists (zvec_zero d), (zvec_zero d).
  repeat split; try exact Hzero. symmetry. apply zvec_sub_self.
Qed.

Lemma difference_add : forall d (set : ZSet d),
    Periodic set -> forall left right,
    Difference set left -> Difference set right ->
    Difference set (zvec_add left right).
Proof.
  intros d set [Hzero Hadd] left right
    [left1 [right1 [Hleft1 [Hright1 Heq1]]]]
    [left2 [right2 [Hleft2 [Hright2 Heq2]]]].
  subst left; subst right.
  exists (zvec_add left1 left2), (zvec_add right1 right2).
  repeat split; try now apply Hadd.
  apply zvec_add_sub_distribute.
Qed.

Lemma difference_opp : forall d (set : ZSet d) value,
    Difference set value -> Difference set (zvec_opp value).
Proof.
  intros d set value [left [right [Hleft [Hright Heq]]]]. subst value.
  exists right, left. repeat split; try assumption. apply zvec_opp_sub.
Qed.

Theorem difference_is_integer_additive_group : forall d (set : ZSet d),
    Periodic set -> IntegerAdditiveGroup (Difference set).
Proof.
  intros d set Hperiodic. constructor.
  - now apply difference_zero.
  - now apply difference_add.
  - now apply difference_opp.
Qed.

Lemma integer_additive_group_periodic : forall d (set : ZSet d),
    IntegerAdditiveGroup set -> Periodic set.
Proof.
  intros d set Hgroup. split.
  - exact (integer_group_zero set Hgroup).
  - exact (integer_group_add set Hgroup).
Qed.

Lemma zvec_sub_as_add_opp : forall d (left right : ZVec d),
    zvec_sub left right = zvec_add left (zvec_opp right).
Proof.
  intros d left right. apply zvec_ext. intro index.
  unfold zvec_sub, zvec_add, zvec_opp.
  rewrite (nth_map2 Z.sub left right index index index eq_refl eq_refl).
  rewrite (nth_map2 Z.add left (Vector.map Z.opp right)
    index index index eq_refl eq_refl).
  rewrite (nth_map Z.opp right index index eq_refl). lia.
Qed.

Lemma integer_additive_group_periodic_le_total : forall d
    (set : ZSet d), IntegerAdditiveGroup set -> forall left right,
    set left -> set right -> PeriodicLe set left right.
Proof.
  intros d set Hgroup left right Hleft Hright. unfold PeriodicLe.
  rewrite zvec_sub_as_add_opp.
  apply (integer_group_add set Hgroup); [exact Hright|].
  now apply (integer_group_opp set Hgroup).
Qed.

Lemma integer_additive_group_order_wqo : forall d (set : ZSet d),
    IntegerAdditiveGroup set ->
    @afs (ZVec d) set (PeriodicLe set).
Proof.
  intros d set Hgroup. apply afs_full.
  intros left right Hleft Hright.
  now apply integer_additive_group_periodic_le_total.
Qed.

Lemma cone_gen_scale : forall d (set : ZSet d) (value : QVec d)
    (coefficient : Q),
    ConeGen set value -> (0 <= coefficient)%Q ->
    exists scaled, ConeGen set scaled /\
      QVecEq scaled (qvec_scale coefficient value).
Proof.
  intros d set value coefficient Hvalue Hcoefficient.
  induction Hvalue.
  - exists (qvec_zero d). split; [constructor|].
    intro index. unfold qvec_scale, qvec_zero. ring.
  - destruct IHHvalue as [scaled [Hscaled Hscaled_eq]].
    exists (qvec_add
      (qvec_scale (coefficient0 * coefficient) (zvec_to_qvec value))
      scaled). split.
    + constructor.
      * apply Qmult_le_0_compat; assumption.
      * exact H0.
      * exact Hscaled.
    + intro index. unfold qvec_scale, qvec_add in *.
      specialize (Hscaled_eq index). setoid_rewrite Hscaled_eq. ring.
Qed.

Lemma cone_gen_plus : forall d (set : ZSet d) (left right : QVec d),
    ConeGen set left -> ConeGen set right ->
    exists sum, ConeGen set sum /\ QVecEq sum (qvec_add left right).
Proof.
  intros d set left right Hleft Hright. induction Hleft.
  - exists right. split; [exact Hright|]. intro index.
    unfold qvec_add, qvec_zero. symmetry. apply Qplus_0_l.
  - destruct IHHleft as [sum [Hsum Heq]].
    exists (qvec_add (qvec_scale coefficient (zvec_to_qvec value)) sum).
    split.
    + constructor; assumption.
    + intro index. unfold qvec_add in *. specialize (Heq index).
      setoid_rewrite Heq. apply Qplus_assoc.
Qed.

Lemma cone_qvec_extensional : forall d (set : ZSet d) left right,
    QVecEq left right -> (Cone set left <-> Cone set right).
Proof.
  intros d set left right Heq. split.
  - intros [generated [Hgenerated Hleft]]. exists generated. split.
    + exact Hgenerated.
    + eapply qvec_eq_trans; [apply qvec_eq_sym; exact Heq|exact Hleft].
  - intros [generated [Hgenerated Hright]]. exists generated. split.
    + exact Hgenerated.
    + eapply qvec_eq_trans; [exact Heq|exact Hright].
Qed.

Lemma cone_is_cone : forall d (set : ZSet d), IsCone (Cone set).
Proof.
  intros d set. constructor.
  - exists (qvec_zero d). split; [constructor|apply qvec_eq_refl].
  - intros left right
      [left' [Hleft Hleft_eq]] [right' [Hright Hright_eq]].
    destruct (cone_gen_plus d set left' right' Hleft Hright)
      as [sum [Hsum Hsum_eq]].
    exists sum. split; [exact Hsum|].
    eapply (@qvec_eq_trans d _ (qvec_add left' right') _).
    + apply qvec_eq_add; assumption.
    + apply qvec_eq_sym. exact Hsum_eq.
  - intros coefficient value Hcoefficient
      [generated [Hgenerated Hvalue_eq]].
    destruct (cone_gen_scale d set generated coefficient
      Hgenerated Hcoefficient) as [scaled [Hscaled Hscaled_eq]].
    exists scaled. split; [exact Hscaled|].
    eapply (@qvec_eq_trans d _ (qvec_scale coefficient generated) _).
    + apply qvec_eq_scale; [reflexivity|exact Hvalue_eq].
    + apply qvec_eq_sym. exact Hscaled_eq.
Qed.

Lemma cone_is_rational_cone : forall d (set : ZSet d),
    RationalCone (Cone set).
Proof.
  intros d set. constructor.
  - apply cone_is_cone.
  - intros left right Heq.
    now apply (cone_qvec_extensional d set left right).
Qed.

Lemma cone_contains_source : forall d (set : ZSet d) value,
    set value -> Cone set (zvec_to_qvec value).
Proof.
  intros d set value Hvalue.
  exists (qvec_add (qvec_scale 1 (zvec_to_qvec value)) (qvec_zero d)).
  split.
  - constructor.
    + unfold Qle; cbn; lia.
    + exact Hvalue.
    + constructor.
  - intro index. unfold qvec_add, qvec_scale, qvec_zero. ring.
Qed.

Lemma cone_gen_in_rational_cone : forall d (set : ZSet d)
    (cone : QSet d),
    RationalCone cone ->
    (forall value, set value -> cone (zvec_to_qvec value)) ->
    forall generated, ConeGen set generated -> cone generated.
Proof.
  intros d set cone [Hcone Hextensional] Hsubset generated Hgenerated.
  induction Hgenerated.
  - exact (cone_contains_zero cone Hcone).
  - apply (cone_closed_add cone Hcone).
    + apply (cone_closed_scale cone Hcone); [exact H|now apply Hsubset].
    + exact IHHgenerated.
Qed.

Lemma cone_in_rational_cone : forall d (set : ZSet d) (cone : QSet d),
    RationalCone cone ->
    (forall value, set value -> cone (zvec_to_qvec value)) ->
    forall point, Cone set point -> cone point.
Proof.
  intros d set cone Hcone Hsubset point
    [generated [Hgenerated Hpoint]].
  apply (proj2 (rational_cone_extensional cone Hcone point generated Hpoint)).
  now apply cone_gen_in_rational_cone with (set := set).
Qed.

Lemma difference_in_integer_group : forall d (set group : ZSet d),
    IntegerAdditiveGroup group ->
    (forall value, set value -> group value) ->
    forall value, Difference set value -> group value.
Proof.
  intros d set group Hgroup Hsubset value
    [left [right [Hleft [Hright Heq]]]].
  subst value. rewrite zvec_sub_as_add_opp.
  apply (integer_group_add group Hgroup).
  - now apply Hsubset.
  - apply (integer_group_opp group Hgroup). now apply Hsubset.
Qed.

Lemma periodic_subset_linearization : forall d (set : ZSet d),
    Periodic set -> forall value, set value -> Linearization set value.
Proof.
  intros d set Hperiodic value Hvalue. split.
  - exists value, (zvec_zero d). repeat split.
    + exact Hvalue.
    + exact (proj1 Hperiodic).
    + apply zvec_ext. intro index. unfold zvec_sub, zvec_zero.
      rewrite (nth_map2 Z.sub value (Vector.const 0 d)
        index index index eq_refl eq_refl), const_nth. lia.
  - now apply cone_contains_source.
Qed.

Theorem full_periodic_iff_linearization_fixed : forall d (set : ZSet d),
    Periodic set ->
    (FullPeriodic set <-> SameSet set (Linearization set)).
Proof.
  intros d set Hperiodic. split.
  - intros [_ [group [cone [Hgroup [Hcone Hrepresentation]]]]].
    intro value. split.
    + now apply periodic_subset_linearization.
    + intros [Hdifference Hgenerated]. apply (proj2 (Hrepresentation value)).
      split.
      * apply difference_in_integer_group with (set := set); try assumption.
        intros source Hsource.
        exact (proj1 (proj1 (Hrepresentation source) Hsource)).
      * apply cone_in_rational_cone with (set := set); try assumption.
        intros source Hsource.
        exact (proj2 (proj1 (Hrepresentation source) Hsource)).
  - intros Hequality. split; [exact Hperiodic|].
    exists (Difference set), (Cone set). split.
    + now apply difference_is_integer_additive_group.
    + split.
      * apply cone_is_rational_cone.
      * exact Hequality.
Qed.

Lemma zgroup_combination_nat_coefficients : forall d
    (generators : list (ZVec d)) coefficients,
    zgroup_combination generators (Vector.map Z.of_nat coefficients) =
      zvec_linear_combination generators (Vector.to_list coefficients).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intro coefficients.
  - refine (Vector.case0 (fun coefficients => _) _ coefficients). reflexivity.
  - refine (Vector.caseS' coefficients (fun coefficients => _) _).
    intros coefficient tail. cbn.
    rewrite zvec_zsmul_nat, IH. reflexivity.
Qed.

Lemma zvec_generated_in_zgroup_generated : forall d
    (generators : list (ZVec d)) value,
    zvec_generated generators value -> ZGroupGenerated generators value.
Proof.
  intros d generators value [coefficients Hcoefficients].
  exists (Vector.map Z.of_nat coefficients).
  rewrite zgroup_combination_nat_coefficients. exact Hcoefficients.
Qed.

Lemma zvec_opp_nth : forall d (value : ZVec d) index,
    Vector.nth (zvec_opp value) index = - Vector.nth value index.
Proof.
  intros d value index. unfold zvec_opp.
  now rewrite (nth_map _ _ index index eq_refl).
Qed.

Lemma integer_additive_group_zsmul : forall d (set : ZSet d),
    IntegerAdditiveGroup set -> forall coefficient value,
    set value -> set (zvec_zsmul coefficient value).
Proof.
  intros d set Hgroup coefficient value Hvalue.
  destruct coefficient as [|positive|positive].
  - rewrite zvec_zsmul_zero. exact (integer_group_zero set Hgroup).
  - assert (Heq : zvec_zsmul (Z.pos positive) value =
        zvec_nsmul (Pos.to_nat positive) value).
    { apply zvec_ext. intro index.
      rewrite zvec_zsmul_nth, nth_zvec_nsmul, positive_nat_Z. reflexivity. }
    rewrite Heq. apply periodic_nsmul with (set := set).
    + now apply integer_additive_group_periodic.
    + exact Hvalue.
  - assert (Heq : zvec_zsmul (Z.neg positive) value =
        zvec_opp (zvec_nsmul (Pos.to_nat positive) value)).
    { apply zvec_ext. intro index.
      rewrite zvec_zsmul_nth, zvec_opp_nth, nth_zvec_nsmul,
        positive_nat_Z.
      change ((- Z.pos positive) * Vector.nth value index =
        - (Z.pos positive * Vector.nth value index)). ring. }
    rewrite Heq. apply (integer_group_opp set Hgroup).
    apply periodic_nsmul with (set := set).
    + now apply integer_additive_group_periodic.
    + exact Hvalue.
Qed.

Lemma zgroup_combination_in_integer_additive_group : forall d
    (set : ZSet d), IntegerAdditiveGroup set ->
    forall (generators : list (ZVec d)) coefficients,
    (forall generator, List.In generator generators -> set generator) ->
    set (zgroup_combination generators coefficients).
Proof.
  intros d set Hgroup generators. induction generators as
    [|generator generators IH]; intro coefficients; intro Hall.
  - refine (Vector.case0 (fun coefficients => _) _ coefficients).
    exact (integer_group_zero set Hgroup).
  - refine (Vector.caseS' coefficients (fun coefficients => _) _).
    intros coefficient tail. cbn.
    apply (integer_group_add set Hgroup).
    + apply integer_additive_group_zsmul; [exact Hgroup|].
      apply Hall. now left.
    + apply IH. intros value Hin. apply Hall. now right.
Qed.

Lemma zgroup_generated_in_integer_additive_group : forall d
    (set : ZSet d), IntegerAdditiveGroup set ->
    forall (generators : list (ZVec d)),
    (forall generator, List.In generator generators -> set generator) ->
    forall value, ZGroupGenerated generators value -> set value.
Proof.
  intros d set Hgroup generators Hgenerators value
    [coefficients Hcoefficients].
  rewrite <- Hcoefficients.
  now apply zgroup_combination_in_integer_additive_group.
Qed.

Theorem difference_group_finitely_generated : forall d (set : ZSet d),
    Periodic set -> FinitelyGeneratedGroup (Difference set).
Proof.
  intros d set Hperiodic.
  pose proof (difference_is_integer_additive_group d set Hperiodic) as Hgroup.
  pose proof (integer_additive_group_periodic d (Difference set) Hgroup)
    as Hdifference_periodic.
  pose proof (integer_additive_group_order_wqo d (Difference set) Hgroup)
    as Hdifference_wqo.
  pose proof (proj1 (periodic_order_wqo_iff_finitely_generated d
    (Difference set) Hdifference_periodic) Hdifference_wqo) as Hgenerated.
  destruct Hgenerated as [generators [Hgenerators Hcharacterization]].
  exists generators. intro value. split.
  - intro Hvalue. apply zvec_generated_in_zgroup_generated.
    apply (proj1 (Hcharacterization value)). exact Hvalue.
  - intro Hvalue.
    apply zgroup_generated_in_integer_additive_group with
      (generators := generators); assumption.
Qed.
