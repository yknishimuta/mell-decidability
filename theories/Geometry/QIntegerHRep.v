From Coq Require Import Fin Lia List QArith Vector.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Faces LatticeGordanInterface MathCompBridge
  QConeCore QratHomogeneousAdapter RationalDefinability RationalHToV.

Import ListNotations.
Open Scope Q_scope.

Lemma qnormal_clear_denominators : forall (d : nat) (normal : QVec d),
    exists (multiplier : positive) (integer_normal : ZVec d),
      forall index : Fin.t d,
        zvec_to_qvec integer_normal index ==
          inject_Z (Z.pos multiplier) * normal index.
Proof.
  intros d normal.
  destruct (qvector_clear_denominators d (qvec_to_vector d normal)) as
    [denominator [integer_normal [Hpositive Hclear]]].
  destruct denominator as [|denominator]; [lia|].
  exists (Pos.of_succ_nat denominator), integer_normal.
  intro index. unfold zvec_to_qvec.
  specialize (Hclear index). rewrite qvec_to_vector_nth in Hclear.
  transitivity (q_of_nat (S denominator) * normal index); [exact Hclear|].
  unfold q_of_nat. rewrite Nat2Z.inj_succ, <- Zpos_P_of_succ_nat.
  reflexivity.
Qed.

Lemma qnormal_integer_inner : forall d (normal : QVec d)
    (integer_normal : ZVec d) (multiplier : positive),
    (forall index : Fin.t d,
      zvec_to_qvec integer_normal index ==
        inject_Z (Z.pos multiplier) * normal index) ->
    forall value : QVec d,
      qinner (zvec_to_qvec integer_normal) value ==
        inject_Z (Z.pos multiplier) * qinner normal value.
Proof.
  intros d normal integer_normal multiplier Hcoordinates value.
  unfold qinner.
  transitivity
    (qdot
      (Vector.map (Qmult (inject_Z (Z.pos multiplier)))
        (qvec_to_vector d normal))
      (qvec_to_vector d value)).
  - apply qdot_ext; [|intro index; reflexivity].
    intro index. rewrite qvec_to_vector_nth,
      (nth_map _ _ index index eq_refl), qvec_to_vector_nth.
    apply Hcoordinates.
  - apply qdot_scale_left.
Qed.

Lemma qnormal_integer_nonnegative_iff : forall d
    (normal : QVec d) (integer_normal : ZVec d)
    (multiplier : positive),
    (forall index : Fin.t d,
      zvec_to_qvec integer_normal index ==
        inject_Z (Z.pos multiplier) * normal index) ->
    forall value : QVec d,
      (0 <= qinner normal value <->
       0 <= qinner (zvec_to_qvec integer_normal) value).
Proof.
  intros d normal integer_normal multiplier Hcoordinates value.
  pose proof (qnormal_integer_inner d normal integer_normal multiplier
    Hcoordinates value) as Hinner.
  assert (Hpositive : 0 < inject_Z (Z.pos multiplier)).
  { unfold Qlt, inject_Z. cbn. lia. }
  split; intro Hnonnegative.
  - setoid_rewrite Hinner.
    apply Qmult_le_0_compat; [apply Qlt_le_weak; exact Hpositive|assumption].
  - apply (proj1 (Qmult_le_l 0 (qinner normal value)
      (inject_Z (Z.pos multiplier)) Hpositive)).
    setoid_rewrite Qmult_0_r.
    setoid_rewrite <- Hinner. exact Hnonnegative.
Qed.

Lemma qnormal_list_integer_hrep : forall d (normals : list (QVec d)),
    exists integer_normals : list (ZVec d),
      forall value : QVec d,
        (forall normal, List.In normal normals ->
          0 <= qinner normal value) <->
        (forall normal, List.In normal integer_normals ->
          0 <= qinner (zvec_to_qvec normal) value).
Proof.
  intros d normals. induction normals as [|normal normals IH].
  - exists []. intro value. split; intros H candidate Hin; inversion Hin.
  - destruct (qnormal_clear_denominators d normal) as
      [multiplier [integer_normal Hcoordinates]].
    destruct IH as [integer_normals Htail].
    exists (integer_normal :: integer_normals). intro value. split.
    + intros H candidate [Heq | Hin].
      * subst candidate. apply (proj1
          (qnormal_integer_nonnegative_iff d normal integer_normal multiplier
            Hcoordinates value)).
        apply H. now left.
      * apply (proj1 (Htail value)).
        -- intros tail_normal Htail_in. apply H. now right.
        -- exact Hin.
    + intros H candidate [Heq | Hin].
      * subst candidate. apply (proj2
          (qnormal_integer_nonnegative_iff d normal integer_normal multiplier
            Hcoordinates value)).
        apply H. now left.
      * apply (proj2 (Htail value)).
        -- intros tail_integer Htail_in. apply H. now right.
        -- exact Hin.
Qed.

Theorem polyhedral_cone_integer_hrep : forall (d : nat) (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists normals : list (ZVec d),
      forall value : QVec d,
        cone value <->
        forall normal : ZVec d,
          List.In normal normals ->
          0 <= qinner (zvec_to_qvec normal) value.
Proof.
  intros d cone [generators Hsame].
  destruct (polyhedra_cone_homogeneous_base generators) as
    [normals Hhomogeneous].
  destruct (qnormal_list_integer_hrep d normals) as
    [integer_normals Hinteger].
  exists integer_normals. intro value.
  rewrite (Hsame value), (Hhomogeneous value), (Hinteger value).
  reflexivity.
Qed.
