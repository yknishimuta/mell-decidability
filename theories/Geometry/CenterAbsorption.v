From Coq Require Import Fin Lia List Lra QArith QArith.Qabs Qring Vector
  VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Center CenterCharacterization
  ClosedLinearization Cone LatticeGordanH LatticeGordanPullback
  LatticeGordanV MathCompBridge Periodic QConeCore RationalClosure RationalSpan
  SpanPerturbation.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Definition qvec_difference {d} (left right : QVec d) : QVec d :=
  fun index => left index - right index.

Lemma qvec_difference_as_add_opp : forall d (left right : QVec d),
    QVecEq (qvec_difference left right)
      (qvec_add left (qvec_opp right)).
Proof.
  intros d left right index.
  unfold qvec_difference, qvec_add, qvec_opp, qvec_scale. ring.
Qed.

Lemma periodic_cone_positive_ray : forall d (set : ZSet d) point,
    Periodic set -> Cone set point ->
    exists value coefficient,
      set value /\ 0 < coefficient /\
      QVecEq point
        (qvec_scale coefficient (zvec_to_qvec value)).
Proof.
  intros d set point Hperiodic Hcone.
  apply (proj1 (periodic_standard_cone_denominator_clearing
    d set point Hperiodic)) in Hcone.
  destruct Hcone as [denominator [value
    [Hdenominator [Hvalue Hpoint]]]].
  exists value, (/ q_of_nat denominator). repeat split; try assumption.
  - apply Qinv_lt_0_compat, q_of_nat_positive_v. lia.
Qed.

Lemma member_in_vecof : forall d (set : ZSet d) value,
    set value -> VecOf set (zvec_to_qvec value).
Proof.
  intros d set value Hvalue. exists [value]. split.
  - repeat constructor; assumption.
  - apply qspan_member. now left.
Qed.

Lemma difference_in_vecof : forall d (set : ZSet d) value,
    Difference set value -> VecOf set (zvec_to_qvec value).
Proof.
  intros d set value
    [left [right [Hleft [Hright Heq]]]]. subst value.
  exists [left; right]. split.
  - repeat constructor; assumption.
  - exists (@Vector.cons Q 1 1
      (@Vector.cons Q (-1) 0 (@Vector.nil Q))).
    intro index. unfold zvec_to_qvec, zvec_sub.
    rewrite (nth_map2 Z.sub left right index index index eq_refl eq_refl).
    unfold Z.sub. rewrite inject_Z_plus, inject_Z_opp.
    cbn [qgroup_combination].
    unfold qvec_add, qvec_scale, qvec_zero, zvec_to_qvec.
    cbn. ring.
Qed.

Lemma periodic_cone_in_vecof : forall d (set : ZSet d) point,
    Periodic set -> Cone set point -> VecOf set point.
Proof.
  intros d set point Hperiodic Hcone.
  destruct (periodic_cone_positive_ray d set point Hperiodic Hcone)
    as [value [coefficient [Hvalue [Hcoefficient Hpoint]]]].
  exists [value]. split.
  - repeat constructor; assumption.
  - exists (@Vector.cons Q coefficient 0 (@Vector.nil Q)).
    eapply qvec_eq_trans; [exact Hpoint|]. intro index.
    cbn [qgroup_combination]. unfold qvec_add, qvec_scale, qvec_zero.
    cbn. ring.
Qed.

Lemma qspan_difference : forall d (generators : list (ZVec d)) left right,
    QSpan generators left -> QSpan generators right ->
    QSpan generators (qvec_difference left right).
Proof.
  intros d generators left right Hleft Hright.
  apply (proj2 (qspan_qvec_ext d generators _ _
    (qvec_difference_as_add_opp d left right))).
  apply qspan_add; [exact Hleft|now apply qspan_opp].
Qed.

Lemma vector_map2_plus_positive : forall n
    (positive perturbation : Vector.t Q n),
    Vector.Forall (fun coefficient => 0 < coefficient) positive ->
    (forall index : Fin.t n,
      - Vector.nth positive index < Vector.nth perturbation index) ->
    Vector.Forall (fun coefficient => 0 < coefficient)
      (Vector.map2 Qplus positive perturbation).
Proof.
  intros n positive perturbation Hpositive Hlower.
  apply (proj2 (Vector.Forall_nth _ _ _ _)). intro index.
  rewrite (nth_map2 Qplus positive perturbation
    index index index eq_refl eq_refl).
  specialize (Hlower index).
  apply (proj1 (Qlt_minus_iff _ _)) in Hlower.
  setoid_replace
    (Vector.nth positive index + Vector.nth perturbation index)
    with (Vector.nth perturbation index + - (- Vector.nth positive index))
    by ring.
  exact Hlower.
Qed.

Lemma positive_spanning_cons : forall d (set : ZSet d)
    (head : ZVec d) generators,
    set head -> List.Forall set generators ->
    (forall point : QVec d, VecOf set point <-> QSpan generators point) ->
    forall point : QVec d,
      VecOf set point <-> QSpan (head :: generators) point.
Proof.
  intros d set head generators Hhead Hgenerators Hspan point.
  rewrite Hspan. symmetry. apply qspan_cons_equiv.
  apply (proj1 (Hspan (zvec_to_qvec head))).
  now apply member_in_vecof.
Qed.

Lemma perturbed_positive_combination : forall d
    (value offset generator : ZVec d)
    (perturbation_point point : QVec d) generators coefficient
    (positive perturbation : Vector.t Q (length generators)),
    QVecEq (zvec_to_qvec value)
      (qgroup_combination generators positive) ->
    QVecEq perturbation_point
      (qgroup_combination generators perturbation) ->
    QVecEq point
      (qvec_scale coefficient (zvec_to_qvec generator)) ->
    QVecEq (zvec_to_qvec offset)
      (qvec_add perturbation_point point) ->
    QVecEq (zvec_to_qvec (zvec_add value offset))
      (qgroup_combination (generator :: generators)
        (@Vector.cons Q coefficient _
          (Vector.map2 Qplus positive perturbation))).
Proof.
  intros d value offset generator perturbation_point point generators
    coefficient positive perturbation Hvalue Hperturbation Hpoint Hsplit index.
  pose proof (Hvalue index) as Hvalue_index.
  pose proof (Hperturbation index) as Hperturbation_index.
  pose proof (Hpoint index) as Hpoint_index.
  pose proof (Hsplit index) as Hsplit_index.
  pose proof (qgroup_combination_add_q d generators positive perturbation
    index) as Hcombined.
  pose proof (zvec_to_qvec_add d value offset index) as Hadd.
  cbn [qgroup_combination]. unfold qvec_add, qvec_scale, qvec_zero. cbn.
  eapply Qeq_trans; [exact Hadd|].
  eapply Qeq_trans with
    (y := qgroup_combination generators positive index +
      (perturbation_point index + point index)).
  - apply Qplus_comp; [exact Hvalue_index|].
    exact Hsplit_index.
  - eapply Qeq_trans with
      (y := coefficient * zvec_to_qvec generator index +
        (qgroup_combination generators positive index +
         qgroup_combination generators perturbation index)).
    + setoid_rewrite Hperturbation_index.
      setoid_rewrite Hpoint_index.
      unfold qvec_scale. ring.
    + apply Qplus_comp; [reflexivity|]. symmetry. exact Hcombined.
Qed.

Theorem center_add_closed_linearization :
  forall d (set : ZSet d) (value offset : ZVec d),
    Periodic set ->
    Center set value ->
    ClosedLinearization set offset ->
    Center set (zvec_add value offset).
Proof.
  intros d set value offset Hperiodic Hcenter Hclosed.
  destruct (proj1 (center_characterization d set value Hperiodic) Hcenter)
    as [Hvalue_difference
      [generators [Hgenerators [Hspan
        [positive [Hpositive Hvalue]]]]]].
  destruct (proj1 (closed_linearization_spec d set offset) Hclosed)
    as [Hoffset_difference Hclosure].
  destruct (qspan_uniform_small_coefficients d generators positive Hpositive)
    as [epsilon [Hepsilon Hsmall_coefficients]].
  destruct (Hclosure epsilon Hepsilon) as
    [approximant [Happroximant Hnear]].
  destruct (periodic_cone_positive_ray d set approximant
    Hperiodic Happroximant) as
    [ray [coefficient [Hray [Hcoefficient Hray_point]]]].
  set (perturbation := qvec_difference (zvec_to_qvec offset) approximant).
  assert (Hoffset_span : QSpan generators (zvec_to_qvec offset)).
  { apply (proj1 (Hspan _)). now apply difference_in_vecof. }
  assert (Happroximant_span : QSpan generators approximant).
  { apply (proj1 (Hspan _)).
    now apply periodic_cone_in_vecof with (set := set). }
  assert (Hperturbation_span : QSpan generators perturbation).
  { unfold perturbation. now apply qspan_difference. }
  assert (Hperturbation_small : forall index : Fin.t d,
      - epsilon < perturbation index /\ perturbation index < epsilon).
  { intro index. unfold perturbation, qvec_difference.
    pose proof (Hnear index) as Habsolute.
    apply (proj1 (Qabs_Qlt_condition _ _)). exact Habsolute. }
  destruct (Hsmall_coefficients perturbation Hperturbation_span
    Hperturbation_small) as [delta [Hdelta Hdelta_bounds]].
  set (combined := Vector.map2 Qplus positive delta).
  assert (Hcombined_positive :
      Vector.Forall (fun q : Q => 0 < q) combined).
  { unfold combined. apply vector_map2_plus_positive; [exact Hpositive|].
    intro index. exact (proj1 (Hdelta_bounds index)). }
  apply (proj2 (center_characterization d set
    (zvec_add value offset) Hperiodic)). split.
  - apply difference_add with (set := set); try assumption.
  - exists (ray :: generators). split.
    + constructor; assumption.
    + split.
      * now apply positive_spanning_cons.
      * exists (@Vector.cons Q coefficient _ combined). split.
        -- constructor; assumption.
        -- unfold combined, perturbation in *.
           eapply perturbed_positive_combination;
             [exact Hvalue|exact Hdelta|exact Hray_point|].
           intro index. unfold perturbation, qvec_difference, qvec_add.
           ring.
Qed.

Lemma closed_linearization_zero : forall d (set : ZSet d),
    Periodic set -> ClosedLinearization set (zvec_zero d).
Proof.
  intros d set Hperiodic.
  apply (proj2 (closed_linearization_spec d set (zvec_zero d))). split.
  - now apply difference_zero.
  - apply (proj1 (qclosure_qvec_extensional d (Cone set)
      (qvec_zero d) (zvec_to_qvec (zvec_zero d))
      (qvec_eq_sym _ _ _ (zvec_to_qvec_zero d)))).
    apply qclosure_extensive. exists (qvec_zero d). split.
    + constructor.
    + apply qvec_eq_refl.
Qed.

Theorem center_absorbs_closed_linearization :
  forall d (set : ZSet d),
    Periodic set ->
    SameSet
      (fun result =>
        exists value offset,
          Center set value /\
          ClosedLinearization set offset /\
          result = zvec_add value offset)
      (Center set).
Proof.
  intros d set Hperiodic result. split.
  - intros [value [offset [Hvalue [Hoffset Heq]]]]. subst result.
    now apply center_add_closed_linearization with (set := set).
  - intro Hresult.
    exists result, (zvec_zero d). split; [exact Hresult|]. split.
    + now apply closed_linearization_zero.
    + symmetry. apply zvec_add_zero_right.
Qed.
