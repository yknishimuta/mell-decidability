From Coq Require Import Fin Lia QArith QArith.Qabs Qring Vector.
From Mell.Geometry Require Import MathCompBridge RationalDefinability
  QConeCore RationalClosure ClosedLinearization.

Open Scope Q_scope.
Set Printing Implicit.

Check @qclosure_qdefinable.
Check @qclosure_is_cone.
Check @qclosure_topologically_closed.

Definition closure_q1 (value : Q) : QVec 1 := fun _ => value.

Definition closure_q2 (left right : Q) : QVec 2 :=
  fun index => Fin.caseS' index (fun _ => Q) left (fun _ => right).

Definition closure_empty {d} : QSet d := fun _ => False.
Definition closure_full {d} : QSet d := fun _ => True.
Definition closure_singleton {d} (center : QVec d) : QSet d :=
  fun value => QVecEq value center.
Definition closure_open_ray : QSet 1 :=
  fun value => 0 < value Fin.F1.
Definition closure_open_quadrant : QSet 2 :=
  fun value => 0 < value Fin.F1 /\ 0 < value (Fin.FS Fin.F1).
Definition closure_nonclosed_cone : QSet 2 :=
  fun value => QVecEq value (qvec_zero 2) \/ closure_open_quadrant value.

Example closure_dimension_zero : forall (set : QSet 0) (point : QVec 0),
    (exists value, set value) -> QClosure set point.
Proof.
  intros set point [value Hvalue] delta Hdelta. exists value. split.
  - exact Hvalue.
  - intro index. exact (Fin.case0 (fun index =>
      Qabs (point index - value index) < delta) index).
Qed.

Example closure_empty_stays_empty : forall d (point : QVec d),
    ~ QClosure closure_empty point.
Proof.
  intros d point Hclosure.
  destruct (Hclosure 1) as [approximant [Hfalse _]].
  - unfold Qlt; cbn; lia.
  - exact Hfalse.
Qed.

Example closure_full_stays_full : forall d (point : QVec d),
    QClosure closure_full point.
Proof.
  intros d point. apply qclosure_extensive. exact I.
Qed.

Lemma qabs_positive_of_not_zero : forall value : Q,
    ~ value == 0 -> 0 < Qabs value.
Proof.
  intros value Hnonzero.
  destruct (Qlt_le_dec 0 (Qabs value)) as [Hpositive|Hnonpositive].
  - exact Hpositive.
  - exfalso. apply Hnonzero.
    apply (proj1 (Qabs_Qle_condition value 0)) in Hnonpositive.
    destruct Hnonpositive as [Hlower Hupper].
    setoid_replace (- 0) with 0 in Hlower by ring.
    now apply Qle_antisym.
Qed.

Lemma qclosure_singleton_correct : forall d (center point : QVec d),
    QClosure (closure_singleton center) point <-> QVecEq point center.
Proof.
  intros d center point. split.
  - intros Hclosure index.
    destruct (Qeq_dec (point index) (center index)) as [Heq|Hneq];
      [exact Heq|].
    assert (Hdifference : ~ point index - center index == 0).
    { intro Hzero. apply Hneq.
      apply (proj1 (Qplus_inj_r (point index) (center index)
        (- center index))).
      setoid_replace (point index + - center index)
        with (point index - center index) by ring.
      setoid_replace (center index + - center index) with 0 by ring.
      exact Hzero. }
    pose proof (qabs_positive_of_not_zero
      (point index - center index) Hdifference) as Hpositive.
    destruct (Hclosure (Qabs (point index - center index)) Hpositive)
      as [approximant [Hsingle Hnear]].
    specialize (Hnear index). specialize (Hsingle index).
    setoid_rewrite Hsingle in Hnear.
    exfalso. exact (Qlt_irrefl _ Hnear).
  - intro Heq. apply (proj2 (qclosure_qvec_extensional d
      (closure_singleton center) point center Heq)).
    apply qclosure_extensive. apply qvec_eq_refl.
Qed.

Lemma closure_open_ray_qdefinable : QDefinable closure_open_ray.
Proof.
  exists (QFLt (QTConst 0) (QTVar 0)). split; [reflexivity|].
  intro value. unfold closure_open_ray. cbn. reflexivity.
Qed.

Example closure_open_ray_is_definable : QDefinable (QClosure closure_open_ray).
Proof. now apply qclosure_qdefinable, closure_open_ray_qdefinable. Qed.

Lemma qhalf_below : forall delta : Q, 0 < delta -> delta / 2 < delta.
Proof.
  intros delta Hdelta.
  assert (Htwo : 0 < (2 : Q)) by reflexivity.
  apply (proj1 (Qmult_lt_r (delta / 2) delta 2 Htwo)).
  setoid_replace (delta / 2 * 2) with delta by field.
  setoid_replace (delta * 2) with (delta + delta) by ring.
  pose proof (proj2 (Qplus_lt_l 0 delta delta) Hdelta) as Hsum.
  setoid_replace (0 + delta) with delta in Hsum by ring. exact Hsum.
Qed.

Lemma qnegative_below_half : forall delta : Q,
    0 < delta -> 0 - delta < delta / 2.
Proof.
  intros delta Hdelta. setoid_replace (0 - delta) with (- delta) by ring.
  eapply Qlt_trans with 0.
  - setoid_replace 0 with (- 0) by ring. now apply Qopp_lt_compat.
  - now apply qhalf_positive.
Qed.

Lemma closure_open_ray_contains_zero :
    QClosure closure_open_ray (closure_q1 0).
Proof.
  intros delta Hdelta. exists (closure_q1 (delta / 2)). split.
  - unfold closure_open_ray, closure_q1. apply qhalf_positive. exact Hdelta.
  - intro index. refine (Fin.caseS' index (fun index =>
      Qabs (closure_q1 0 index - closure_q1 (delta / 2) index) < delta)
      _ _).
    + unfold closure_q1. apply (proj2 (Qabs_diff_Qlt_condition _ _ _)).
      split.
      * apply qnegative_below_half. exact Hdelta.
      * setoid_replace (0 + delta) with delta by ring.
        apply qhalf_below. exact Hdelta.
    + intro impossible. inversion impossible.
Qed.

Example closure_open_ray_is_not_identity :
    QClosure closure_open_ray (closure_q1 0) /\
    ~ closure_open_ray (closure_q1 0).
Proof.
  split; [exact closure_open_ray_contains_zero|].
  unfold closure_open_ray, closure_q1, Qlt. cbn. lia.
Qed.

Lemma closure_nonclosed_cone_is_cone : IsCone closure_nonclosed_cone.
Proof.
  constructor.
  - now left.
  - intros left right Hleft Hright.
    destruct Hleft as [Hleft|[Hleft0 Hleft1]];
      destruct Hright as [Hright|[Hright0 Hright1]].
    + left. intro index. unfold qvec_add, qvec_zero.
      setoid_rewrite (Hleft index). setoid_rewrite (Hright index).
      reflexivity.
    + right. split; unfold qvec_add.
      * setoid_rewrite (Hleft Fin.F1). setoid_rewrite Qplus_0_l.
        exact Hright0.
      * setoid_rewrite (Hleft (Fin.FS Fin.F1)). setoid_rewrite Qplus_0_l.
        exact Hright1.
    + right. split; unfold qvec_add.
      * setoid_rewrite (Hright Fin.F1). setoid_rewrite Qplus_0_r.
        exact Hleft0.
      * setoid_rewrite (Hright (Fin.FS Fin.F1)). setoid_rewrite Qplus_0_r.
        exact Hleft1.
    + right. split; unfold qvec_add;
        setoid_replace 0 with (0 + 0)%Q by ring;
        now apply Qplus_lt_compat.
  - intros coefficient value Hcoefficient Hvalue.
    destruct Hvalue as [Hzero|[Hpositive0 Hpositive1]].
    + left. intro index. unfold qvec_scale, qvec_zero.
      setoid_rewrite (Hzero index). apply Qmult_0_r.
    + destruct (Qle_lt_or_eq _ _ Hcoefficient) as [Hpositive|Hzero].
      * right. split; unfold qvec_scale;
          now apply Qmult_lt_0_compat.
      * left. intro index. unfold qvec_scale, qvec_zero.
        setoid_rewrite <- Hzero. apply Qmult_0_l.
Qed.

Lemma closure_open_quadrant_boundary :
    QClosure closure_open_quadrant (closure_q2 1 0).
Proof.
  intros delta Hdelta. exists (closure_q2 1 (delta / 2)). split.
  - split.
    + unfold closure_q2. unfold Qlt; cbn; lia.
    + unfold closure_q2. apply qhalf_positive. exact Hdelta.
  - intro index. refine (Fin.caseS' index (fun index =>
      Qabs (closure_q2 1 0 index - closure_q2 1 (delta / 2) index) < delta)
      _ _).
    + unfold closure_q2. setoid_replace (1 - 1) with 0 by ring.
      exact Hdelta.
    + intro tail. refine (Fin.caseS' tail (fun tail =>
        Qabs (closure_q2 1 0 (Fin.FS tail) -
          closure_q2 1 (delta / 2) (Fin.FS tail)) < delta) _ _).
      * unfold closure_q2. apply (proj2 (Qabs_diff_Qlt_condition _ _ _)).
        split.
        -- apply qnegative_below_half. exact Hdelta.
        -- setoid_replace (0 + delta) with delta by ring.
           apply qhalf_below. exact Hdelta.
      * intro impossible. inversion impossible.
Qed.

Example closure_open_quadrant_gains_boundary :
    QClosure closure_open_quadrant (closure_q2 1 0) /\
    ~ closure_open_quadrant (closure_q2 1 0).
Proof.
  split; [exact closure_open_quadrant_boundary|].
  intros [_ Hfalse]. unfold closure_q2, Qlt in Hfalse. cbn in Hfalse. lia.
Qed.

Example closure_nonclosed_cone_gains_boundary :
    IsCone closure_nonclosed_cone /\
    QClosure closure_nonclosed_cone (closure_q2 1 0) /\
    ~ closure_nonclosed_cone (closure_q2 1 0).
Proof.
  split; [exact closure_nonclosed_cone_is_cone|]. split.
  - eapply qclosure_monotone; [|exact closure_open_quadrant_boundary].
    intros value Hvalue. now right.
  - intros [Hzero|[_ Hfalse]].
    + specialize (Hzero Fin.F1). unfold closure_q2, qvec_zero in Hzero.
      unfold Qeq in Hzero; cbn in Hzero; lia.
    + unfold closure_q2, Qlt in Hfalse. cbn in Hfalse. lia.
Qed.

Example closure_nonnormalized_qeq :
    QClosure (closure_singleton (closure_q1 1)) (closure_q1 (2#2)) <->
    QClosure (closure_singleton (closure_q1 1)) (closure_q1 1).
Proof.
  apply qclosure_qvec_extensional. intro index.
  refine (Fin.caseS' index (fun index =>
    closure_q1 (2#2) index == closure_q1 1 index) _ _).
  - reflexivity.
  - intro impossible. inversion impossible.
Qed.

Print QClosure.
Print QDefinable.
Print QFormula.
Print IsCone.
Print RationalCone.
Print TopologicallyClosed.
Print QVecEq.
Print Assumptions qclosure_qdefinable.
Print Assumptions qclosure_is_cone.
Print Assumptions qclosure_topologically_closed.
