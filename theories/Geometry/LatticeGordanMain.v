From Coq Require Import List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge Periodic QConeCore
  RationalDefinability LatticeGordanH LatticeGordanInterface
  LatticeGordanV LatticeGordanPullback.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Lemma F_Z_zero : forall d (groups : list (ZVec d)),
    F_Z groups (zvec_zero (length groups)) = zvec_zero d.
Proof. intros d groups. unfold F_Z. apply zgroup_combination_zero. Qed.

Lemma F_Z_nsmul : forall d (groups : list (ZVec d)) coefficient value,
    F_Z groups (zvec_nsmul coefficient value) =
      zvec_nsmul coefficient (F_Z groups value).
Proof.
  intros d groups coefficient value.
  rewrite <- (zvec_zsmul_nat (length groups) coefficient value).
  rewrite <- (zvec_zsmul_nat d coefficient (F_Z groups value)).
  apply F_Z_scale.
Qed.

Lemma F_Z_linear_combination_nat : forall d (groups : list (ZVec d))
    (values : list (ZVec (length groups))) coefficients,
    F_Z groups (zvec_linear_combination values coefficients) =
      zvec_linear_combination (List.map (F_Z groups) values) coefficients.
Proof.
  intros d groups values. induction values as [|value values IH];
    intros coefficients; destruct coefficients as [|coefficient coefficients].
  - apply F_Z_zero.
  - apply F_Z_zero.
  - apply F_Z_zero.
  - cbn [zvec_linear_combination List.map].
    rewrite F_Z_add, F_Z_nsmul, IH. reflexivity.
Qed.

Lemma zvec_generated_map_F_Z : forall d (groups : list (ZVec d))
    (generators : list (ZVec (length groups))) value,
    zvec_generated generators value ->
    zvec_generated (List.map (F_Z groups) generators) (F_Z groups value).
Proof.
  intros d groups generators value [coefficients Hcoefficients].
  set (coefficient_list := Vector.to_list coefficients).
  assert (Hlength : length coefficient_list = length generators).
  { unfold coefficient_list. apply VectorSpec.length_to_list. }
  replace (F_Z groups value) with
    (zvec_linear_combination (List.map (F_Z groups) generators)
      coefficient_list).
  - apply zvec_generated_list_coefficients.
    rewrite length_map. exact Hlength.
  - rewrite <- F_Z_linear_combination_nat.
    unfold coefficient_list. now rewrite Hcoefficients.
Qed.

Lemma finitely_generated_group_periodic : forall d (group : ZSet d),
    FinitelyGeneratedGroup group -> Periodic group.
Proof.
  intros d group [generators Hgroup].
  destruct (zgroup_generated_periodic d generators) as [Hzero Hadd].
  split.
  - apply (proj2 (Hgroup _)). exact Hzero.
  - intros left right Hleft Hright. apply (proj2 (Hgroup _)).
    apply Hadd; apply (proj1 (Hgroup _)); assumption.
Qed.

Lemma rational_polyhedral_integer_points_periodic : forall d
    (cone : QSet d), RationalPolyhedralCone cone ->
    Periodic (fun value : ZVec d => cone (zvec_to_qvec value)).
Proof.
  intros d cone [generators Hcone]. split.
  - apply (proj2 (Hcone _)).
    apply (proj2 (qcone_generated_qvec_ext d generators
      (zvec_to_qvec (zvec_zero d)) (qvec_zero d)
      (zvec_to_qvec_zero_v d))).
    apply qcone_generated_zero.
  - intros left right Hleft Hright. apply (proj2 (Hcone _)).
    apply (proj2 (qcone_generated_qvec_ext d generators
      (zvec_to_qvec (zvec_add left right))
      (qvec_add (zvec_to_qvec left) (zvec_to_qvec right))
      (zvec_to_qvec_add d left right))).
    apply qcone_generated_add;
      apply (proj1 (Hcone _)); assumption.
Qed.

Lemma finitely_generated_group_cone_intersection_periodic : forall d
    (group : ZSet d) (cone : QSet d),
    FinitelyGeneratedGroup group -> RationalPolyhedralCone cone ->
    Periodic (fun value : ZVec d =>
      group value /\ cone (zvec_to_qvec value)).
Proof.
  intros d group cone Hgroup Hcone.
  destruct (finitely_generated_group_periodic d group Hgroup)
    as [Hgroup_zero Hgroup_add].
  destruct (rational_polyhedral_integer_points_periodic d cone Hcone)
    as [Hcone_zero Hcone_add].
  split.
  - split; assumption.
  - intros left right [Hleft_group Hleft_cone]
      [Hright_group Hright_cone]. split.
    + now apply Hgroup_add.
    + now apply Hcone_add.
Qed.

Theorem lattice_gordan : forall d (group : ZSet d) (cone : QSet d),
    FinitelyGeneratedGroup group ->
    RationalPolyhedralCone cone ->
    FinitelyGeneratedPeriodic
      (fun value => group value /\ cone (zvec_to_qvec value)).
Proof.
  intros d group cone Hgroup Hcone.
  destruct Hgroup as [groups Hgroups].
  destruct Hcone as [cones Hcones].
  destruct (vcone_pullback_finitely_generated d groups cones)
    as [pullback_generators Hpullback].
  destruct (integer_points_vcone_finitely_generated
    (length groups) pullback_generators)
    as [coefficient_generators [Hcoefficient_generators Hcoefficients]].
  set (generators := List.map (F_Z groups) coefficient_generators).
  assert (Hgenerators : forall generator, List.In generator generators ->
      group generator /\ cone (zvec_to_qvec generator)).
  { intros generator Hin. unfold generators in Hin.
    apply in_map_iff in Hin as [coefficient [Heq Hin]]. subst generator.
    split.
    - apply (proj2 (Hgroups _)). exists coefficient. reflexivity.
    - apply (proj2 (Hcones _)).
      apply (proj1 (qcone_generated_qvec_ext d cones
        (F_Q groups (zvec_to_qvec coefficient))
        (zvec_to_qvec (F_Z groups coefficient))
        (F_Q_of_Z d groups coefficient))).
      apply (proj1 (Hpullback (zvec_to_qvec coefficient))).
      now apply Hcoefficient_generators.
  }
  exists generators. split; [exact Hgenerators|]. intro value. split.
  - intros [Hvalue_group Hvalue_cone].
    apply (proj1 (Hgroups value)) in Hvalue_group.
    destruct Hvalue_group as [coefficients Hvalue]. subst value.
    assert (Hcone_coefficients :
        qcone_generated cones (F_Q groups (zvec_to_qvec coefficients))).
    { apply (proj2 (qcone_generated_qvec_ext d cones
        (F_Q groups (zvec_to_qvec coefficients))
        (zvec_to_qvec (F_Z groups coefficients))
        (F_Q_of_Z d groups coefficients))).
      now apply (proj1 (Hcones _)). }
    assert (Hpullback_coefficients : qcone_generated pullback_generators
        (zvec_to_qvec coefficients)).
    { apply (proj2 (Hpullback _)). exact Hcone_coefficients. }
    apply zvec_generated_map_F_Z.
    apply (proj1 (Hcoefficients coefficients)).
    exact Hpullback_coefficients.
  - intro Hgenerated.
    apply (generated_in_periodic d
      (fun point : ZVec d => group point /\ cone (zvec_to_qvec point))
      generators value).
    + apply finitely_generated_group_cone_intersection_periodic.
      * exists groups. exact Hgroups.
      * exists cones. exact Hcones.
    + exact Hgenerators.
    + exact Hgenerated.
Qed.
