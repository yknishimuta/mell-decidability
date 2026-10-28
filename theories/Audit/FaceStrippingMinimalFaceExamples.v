From Coq Require Import Fin Lia List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone FaceStrippingExtract
  FaceStrippingMinimalFace LatticeGordanInterface MathCompBridge Periodic
  QConeCore RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Q_scope.

Check @ConeLineality.
Check @MinimalConeFace.
Check @polyhedral_lineality_minimal_face.
Check @lineality_face_period_inverse.
Check @lineality_face_period_inverse_closed.
Check @lemma_6_9_minimal_extract.
Check @lemma_6_9_any_minimal_face.

Example lineality_minimal_face_public_type :
  forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    MinimalConeFace cone (ConeLineality cone).
Proof. apply polyhedral_lineality_minimal_face. Qed.

Definition d0_q1 (value : Q) : QVec 1 :=
  fun index => Fin.caseS' index (fun _ => Q) value
    (fun impossible => Fin.case0 (fun _ => Q) impossible).

Definition d0_q2 (left right : Q) : QVec 2 :=
  fun index => Fin.caseS' index (fun _ => Q) left
    (fun tail => Fin.caseS' tail (fun _ => Q) right
      (fun impossible => Fin.case0 (fun _ => Q) impossible)).

Definition d0_z1 (value : Z) : ZVec 1 := Vector.of_list [value].

Definition d0_z2 (left right : Z) : ZVec 2 :=
  Vector.of_list [left; right].

Definition d0_zero_cone {d} : QSet d :=
  fun value => QVecEq value (qvec_zero d).

Definition d0_full_cone {d} : QSet d := fun _ => True.

Definition d0_nonnegative_ray : QSet 1 :=
  fun value => 0 <= value Fin.F1.

Definition d0_nonnegative_quadrant : QSet 2 :=
  fun value =>
    0 <= value Fin.F1 /\
    0 <= value (Fin.FS Fin.F1).

Definition d0_nonnegative_times_line : QSet 2 :=
  fun value => 0 <= value Fin.F1.

Lemma d0_nonnegative_and_negative_zero : forall value : Q,
    0 <= value -> 0 <= - value -> value == 0.
Proof.
  intros value Hpositive Hnegative. apply Qle_antisym; [|exact Hpositive].
  pose proof (Qopp_le_compat _ _ Hnegative) as Hupper.
  now rewrite !Qopp_involutive in Hupper.
Qed.

Example dimension_zero_lineality_is_full :
    SameSet (ConeLineality (@d0_full_cone 0)) (@d0_full_cone 0).
Proof. intros value. firstorder. Qed.

Example zero_cone_lineality_is_zero : forall d,
    SameSet (ConeLineality (@d0_zero_cone d)) (@d0_zero_cone d).
Proof.
  intros d value. split; [firstorder|]. intro Hzero. split; [exact Hzero|].
  intro index. unfold qvec_scale, qvec_zero.
  setoid_rewrite (Hzero index). reflexivity.
Qed.

Example full_space_lineality_is_full : forall d,
    SameSet (ConeLineality (@d0_full_cone d)) (@d0_full_cone d).
Proof. intros d value. firstorder. Qed.

Example nat_and_two_nat_cone_lineality_is_zero :
    SameSet (ConeLineality d0_nonnegative_ray)
      (fun value => value Fin.F1 == 0).
Proof.
  intro value. unfold ConeLineality, d0_nonnegative_ray, qvec_scale.
  split.
  - intros [Hpositive Hnegative]. apply d0_nonnegative_and_negative_zero;
      [exact Hpositive|].
    setoid_replace (- value Fin.F1) with (-1 * value Fin.F1) by ring.
    exact Hnegative.
  - intro Hzero. split; setoid_rewrite Hzero; unfold Qle; cbn; lia.
Qed.

Example integer_cone_lineality_is_full :
    SameSet (ConeLineality (@d0_full_cone 1)) (@d0_full_cone 1).
Proof. apply full_space_lineality_is_full. Qed.

Example nat_square_cone_lineality_is_zero :
    SameSet (ConeLineality d0_nonnegative_quadrant)
      (fun value =>
        value Fin.F1 == 0 /\ value (Fin.FS Fin.F1) == 0).
Proof.
  intro value. unfold ConeLineality, d0_nonnegative_quadrant, qvec_scale.
  split.
  - intros [[Hx Hy] [Hnx Hny]]. split;
      apply d0_nonnegative_and_negative_zero; try assumption;
      setoid_replace (- value Fin.F1) with (-1 * value Fin.F1) by ring;
      try exact Hnx;
      setoid_replace (- value (Fin.FS Fin.F1))
        with (-1 * value (Fin.FS Fin.F1)) by ring;
      exact Hny.
  - intros [Hx Hy]. split; split; setoid_rewrite Hx || setoid_rewrite Hy;
      unfold Qle; cbn; lia.
Qed.

Example nat_times_integer_lineality_is_second_axis :
    SameSet (ConeLineality d0_nonnegative_times_line)
      (fun value => value Fin.F1 == 0).
Proof.
  intro value. unfold ConeLineality, d0_nonnegative_times_line, qvec_scale.
  split.
  - intros [Hpositive Hnegative]. apply d0_nonnegative_and_negative_zero;
      [exact Hpositive|].
    setoid_replace (- value Fin.F1) with (-1 * value Fin.F1) by ring.
    exact Hnegative.
  - intro Hzero. split; setoid_rewrite Hzero; unfold Qle; cbn; lia.
Qed.

Definition d0_nat_period : ZSet 1 :=
  fun value => (0 <= Vector.nth value Fin.F1)%Z.

Definition d0_two_nat_period : ZSet 1 :=
  fun value =>
    (0 <= Vector.nth value Fin.F1)%Z /\
    Z.Even (Vector.nth value Fin.F1).

Definition d0_integer_period : ZSet 1 := fun _ => True.

Definition d0_nat_square_period : ZSet 2 :=
  fun value =>
    (0 <= Vector.nth value Fin.F1)%Z /\
    (0 <= Vector.nth value (Fin.FS Fin.F1))%Z.

Definition d0_nat_times_integer_period : ZSet 2 :=
  fun value => (0 <= Vector.nth value Fin.F1)%Z.

Lemma d0_cone_coordinate_nonnegative : forall d (set : ZSet d)
    (index : Fin.t d) point,
    (forall value, set value ->
      0 <= inject_Z (Vector.nth value index)) ->
    Cone set point -> 0 <= point index.
Proof.
  intros d set index point Hsource
    [generated [Hgenerated Hpoint]].
  setoid_rewrite (Hpoint index). clear point Hpoint.
  induction Hgenerated.
  - unfold qvec_zero, Qle. cbn. lia.
  - unfold qvec_add, qvec_scale.
    setoid_replace 0 with (0 + 0) by ring.
    apply Qplus_le_compat; [now apply Qmult_le_0_compat, Hsource|assumption].
Qed.

Definition d0_nat_excluded : ZSet 1 :=
  fun value => (2 <= Vector.nth value Fin.F1)%Z.

Lemma d0_nat_periodic : Periodic d0_nat_period.
Proof.
  split.
  - unfold d0_nat_period, zvec_zero. rewrite Vector.const_nth. lia.
  - intros left right Hleft Hright. unfold d0_nat_period, zvec_add in *.
    rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1 eq_refl eq_refl).
    lia.
Qed.

Lemma d0_two_nat_periodic : Periodic d0_two_nat_period.
Proof.
  split.
  - unfold d0_two_nat_period, zvec_zero. rewrite Vector.const_nth.
    split; [lia|exists 0%Z; lia].
  - intros left right [Hleft [left_half Hleft_even]]
      [Hright [right_half Hright_even]].
    unfold d0_two_nat_period, zvec_add in *.
    rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1 eq_refl eq_refl).
    split; [lia|exists (left_half + right_half)%Z; lia].
Qed.

Lemma d0_integer_periodic : Periodic d0_integer_period.
Proof. split; firstorder. Qed.

Lemma d0_nat_square_periodic : Periodic d0_nat_square_period.
Proof.
  split.
  - unfold d0_nat_square_period, zvec_zero. rewrite !Vector.const_nth.
    lia.
  - intros left right [Hlx Hly] [Hrx Hry].
    unfold d0_nat_square_period, zvec_add in *.
    rewrite !(Vector.nth_map2 _ _ _ _ _ _ eq_refl eq_refl). lia.
Qed.

Lemma d0_nat_times_integer_periodic : Periodic d0_nat_times_integer_period.
Proof.
  split.
  - unfold d0_nat_times_integer_period, zvec_zero.
    rewrite Vector.const_nth. lia.
  - intros left right Hleft Hright.
    unfold d0_nat_times_integer_period, zvec_add in *.
    rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1 eq_refl eq_refl).
    lia.
Qed.

Lemma d0_nat_finitely_generated :
    FinitelyGeneratedPeriodic d0_nat_period.
Proof.
  exists [d0_z1 1]. split.
  - intros generator [<- | Hin]; [unfold d0_nat_period, d0_z1; cbn; lia|].
    contradiction.
  - intro value. split.
    + intro Hvalue. unfold zvec_generated.
      exists (Vector.of_list [Z.to_nat (Vector.nth value Fin.F1)]).
      cbn [zvec_linear_combination]. apply zvec_ext. intro index.
      refine (Fin.caseS' index (fun index => _) _ _).
      * unfold d0_nat_period in Hvalue. unfold d0_z1. cbn.
        unfold zvec_add.
        rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1
          eq_refl eq_refl), nth_zvec_nsmul. cbn.
        rewrite Z2Nat.id by exact Hvalue. lia.
      * intro impossible. inversion impossible.
    + intros [coefficients Hvalue].
      remember (Vector.to_list coefficients) as coefficient_list eqn:Hlist.
      assert (Hlength : length coefficient_list = 1%nat).
      { rewrite Hlist, length_to_list. reflexivity. }
      destruct coefficient_list as [|coefficient coefficient_list];
        [discriminate|].
      destruct coefficient_list as [|extra coefficient_list];
        [|discriminate].
      unfold d0_nat_period. rewrite <- Hvalue.
      cbn [zvec_linear_combination]. unfold d0_z1. cbn. unfold zvec_add.
      rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1
        eq_refl eq_refl), nth_zvec_nsmul. cbn. lia.
Qed.

Definition d0_q_nonnegative : QSet 1 :=
  fun value => 0 <= value Fin.F1.

Lemma d0_q_nonnegative_rational_cone : RationalCone d0_q_nonnegative.
Proof.
  constructor.
  - constructor.
    + unfold d0_q_nonnegative, qvec_zero, Qle. cbn. lia.
    + intros left right Hleft Hright. unfold d0_q_nonnegative, qvec_add in *.
      setoid_replace 0 with (0 + 0) by ring. now apply Qplus_le_compat.
    + intros coefficient value Hcoefficient Hvalue.
      unfold d0_q_nonnegative, qvec_scale in *. now apply Qmult_le_0_compat.
  - intros left right Heq. unfold d0_q_nonnegative.
    setoid_rewrite (Heq Fin.F1). reflexivity.
Qed.

Lemma d0_nonnegative_times_line_rational_cone :
    RationalCone d0_nonnegative_times_line.
Proof.
  constructor.
  - constructor.
    + unfold d0_nonnegative_times_line, qvec_zero, Qle. cbn. lia.
    + intros left right Hleft Hright.
      unfold d0_nonnegative_times_line, qvec_add in *.
      setoid_replace 0 with (0 + 0) by ring. now apply Qplus_le_compat.
    + intros coefficient value Hcoefficient Hvalue.
      unfold d0_nonnegative_times_line, qvec_scale in *.
      now apply Qmult_le_0_compat.
  - intros left right Heq. unfold d0_nonnegative_times_line.
    setoid_rewrite (Heq Fin.F1). reflexivity.
Qed.

Lemma d0_nat_full : FullPeriodic d0_nat_period.
Proof.
  split; [exact d0_nat_periodic|].
  exists (fun _ : ZVec 1 => True), d0_q_nonnegative. split.
  - constructor; trivial.
  - split; [exact d0_q_nonnegative_rational_cone|].
    intro value. unfold d0_nat_period, d0_q_nonnegative, zvec_to_qvec.
    split.
    + intro Hvalue. split; [exact I|].
      unfold Qle, inject_Z. cbn. lia.
    + intros [_ Hvalue]. unfold Qle, inject_Z in Hvalue.
      cbn in Hvalue. lia.
Qed.

Lemma d0_nat_times_integer_full : FullPeriodic d0_nat_times_integer_period.
Proof.
  split; [exact d0_nat_times_integer_periodic|].
  exists (fun _ : ZVec 2 => True), d0_nonnegative_times_line. split.
  - constructor; trivial.
  - split; [exact d0_nonnegative_times_line_rational_cone|].
    intro value. unfold d0_nat_times_integer_period,
      d0_nonnegative_times_line, zvec_to_qvec.
    split.
    + intro Hvalue. split; [exact I|].
      unfold Qle, inject_Z. cbn. lia.
    + intros [_ Hvalue]. unfold Qle, inject_Z in Hvalue.
      cbn in Hvalue. lia.
Qed.

Lemma d0_nat_excluded_cylindric :
    QCylindric d0_nat_period d0_nat_excluded.
Proof.
  intros base increment Hbase Hincrement.
  unfold d0_nat_excluded, d0_nat_period, zvec_add in *.
  rewrite (Vector.nth_map2 _ _ _ Fin.F1 Fin.F1 Fin.F1 eq_refl eq_refl).
  lia.
Qed.

Lemma d0_nat_remaining_cylindric :
    QCylindric d0_nat_period d0_nat_period.
Proof. exact (proj2 d0_nat_periodic). Qed.

Lemma d0_face_period_value_and_opp : forall d (period : ZSet d) value,
    period value -> period (zvec_opp value) ->
    FacePeriod period (ConeLineality (Cone period)) value.
Proof.
  intros d period value Hvalue Hopp. split; [exact Hvalue|]. split.
  - now apply cone_contains_source.
  - apply (proj1 (cone_qvec_extensional d period
      (zvec_to_qvec (zvec_opp value))
      (qvec_scale (-1) (zvec_to_qvec value))
      (zvec_to_qvec_opp d value))).
    now apply cone_contains_source.
Qed.

Lemma d0_face_period_nonnegative_coordinate_zero : forall d
    (period : ZSet d) (index : Fin.t d) value,
    (forall source, period source ->
      0 <= inject_Z (Vector.nth source index)) ->
    FacePeriod period (ConeLineality (Cone period)) value ->
    Vector.nth value index = 0%Z.
Proof.
  intros d period index value Hsource
    [Hvalue [_ Hnegative_cone]].
  pose proof (Hsource value Hvalue) as Hpositive.
  pose proof (d0_cone_coordinate_nonnegative d period index
    (qvec_scale (-1) (zvec_to_qvec value)) Hsource
    Hnegative_cone) as Hnegative.
  unfold qvec_scale, zvec_to_qvec, Qle, inject_Z in Hnegative.
  unfold Qle, inject_Z in Hpositive.
  destruct (Vector.nth value index); cbn in Hnegative, Hpositive; lia.
Qed.

Example nat_face_period_is_zero :
    SameSet
      (FacePeriod d0_nat_period
        (ConeLineality (Cone d0_nat_period)))
      (fun value => Vector.nth value Fin.F1 = 0%Z).
Proof.
  intro value. split.
  - apply d0_face_period_nonnegative_coordinate_zero.
    intros source Hsource. unfold d0_nat_period in Hsource.
    unfold Qle, inject_Z. destruct (Vector.nth source Fin.F1); cbn; lia.
  - intro Hzero. apply d0_face_period_value_and_opp.
    + unfold d0_nat_period. exact (eq_ind_r (fun coordinate => (0 <= coordinate)%Z)
        (Z.le_refl 0) Hzero).
    + unfold d0_nat_period. rewrite zvec_opp_nth, Hzero. lia.
Qed.

Example two_nat_face_period_is_zero :
    SameSet
      (FacePeriod d0_two_nat_period
        (ConeLineality (Cone d0_two_nat_period)))
      (fun value => Vector.nth value Fin.F1 = 0%Z).
Proof.
  intro value. split.
  - apply d0_face_period_nonnegative_coordinate_zero.
    intros source [Hsource _]. unfold Qle, inject_Z.
    destruct (Vector.nth source Fin.F1); cbn; lia.
  - intro Hzero. apply d0_face_period_value_and_opp.
    + unfold d0_two_nat_period. rewrite Hzero.
      split; [lia|exists 0%Z; lia].
    + unfold d0_two_nat_period. rewrite zvec_opp_nth, Hzero.
      split; [lia|exists 0%Z; lia].
Qed.

Example integer_face_period_is_full :
    SameSet
      (FacePeriod d0_integer_period
        (ConeLineality (Cone d0_integer_period)))
      d0_integer_period.
Proof.
  intro value. split; [firstorder|]. intro Hvalue.
  apply d0_face_period_value_and_opp; exact I.
Qed.

Example nat_square_face_period_is_zero :
    SameSet
      (FacePeriod d0_nat_square_period
        (ConeLineality (Cone d0_nat_square_period)))
      (fun value =>
        Vector.nth value Fin.F1 = 0%Z /\
        Vector.nth value (Fin.FS Fin.F1) = 0%Z).
Proof.
  intro value. split.
  - intro Hface. split.
    + eapply d0_face_period_nonnegative_coordinate_zero; [|exact Hface].
      intros source [Hsource _]. unfold Qle, inject_Z.
      destruct (Vector.nth source Fin.F1); cbn; lia.
    + eapply d0_face_period_nonnegative_coordinate_zero; [|exact Hface].
      intros source [_ Hsource]. unfold Qle, inject_Z.
      destruct (Vector.nth source (Fin.FS Fin.F1)); cbn; lia.
  - intros [Hx Hy]. apply d0_face_period_value_and_opp.
    + unfold d0_nat_square_period. now rewrite Hx, Hy.
    + unfold d0_nat_square_period. rewrite !zvec_opp_nth, Hx, Hy. lia.
Qed.

Example nat_times_integer_face_period_is_second_axis :
    SameSet
      (FacePeriod d0_nat_times_integer_period
        (ConeLineality (Cone d0_nat_times_integer_period)))
      (fun value => Vector.nth value Fin.F1 = 0%Z).
Proof.
  intro value. split.
  - apply d0_face_period_nonnegative_coordinate_zero.
    intros source Hsource. unfold d0_nat_times_integer_period in Hsource.
    unfold Qle, inject_Z. destruct (Vector.nth source Fin.F1); cbn; lia.
  - intro Hzero. apply d0_face_period_value_and_opp.
    + unfold d0_nat_times_integer_period. now rewrite Hzero.
    + unfold d0_nat_times_integer_period. rewrite zvec_opp_nth, Hzero. lia.
Qed.

Example nat_times_integer_nonzero_inverse_closure :
    FacePeriod d0_nat_times_integer_period
      (ConeLineality (Cone d0_nat_times_integer_period)) (d0_z2 0 1) /\
    FacePeriod d0_nat_times_integer_period
      (ConeLineality (Cone d0_nat_times_integer_period)) (d0_z2 0 (-1)).
Proof.
  split.
  - apply (proj2 (nat_times_integer_face_period_is_second_axis
      (d0_z2 0 1))). reflexivity.
  - pose proof (lineality_face_period_inverse_closed 2
      d0_nat_times_integer_period (d0_z2 0 1)
      d0_nat_times_integer_periodic d0_nat_times_integer_full
      (proj2 (nat_times_integer_face_period_is_second_axis
        (d0_z2 0 1)) eq_refl)) as Hinverse.
    change (FacePeriod d0_nat_times_integer_period
      (ConeLineality (Cone d0_nat_times_integer_period))
      (zvec_opp (d0_z2 0 1))).
    exact Hinverse.
Qed.

Example nat_times_integer_off_axis_rejected :
    ~ FacePeriod d0_nat_times_integer_period
      (ConeLineality (Cone d0_nat_times_integer_period)) (d0_z2 1 0).
Proof.
  intro Hface.
  apply (proj1 (nat_times_integer_face_period_is_second_axis
    (d0_z2 1 0))) in Hface. discriminate.
Qed.

Example nat_tail_extract_is_zero_or_one : forall value : ZVec 1,
    ExtractFace d0_nat_period
      (ConeLineality (Cone d0_nat_period))
      d0_nat_excluded d0_nat_period value <->
    Vector.nth value Fin.F1 = 0%Z \/
    Vector.nth value Fin.F1 = 1%Z.
Proof.
  intro value.
  pose proof (lemma_6_9_minimal_extract 1 d0_nat_period d0_nat_excluded
    d0_nat_period d0_nat_periodic d0_nat_finitely_generated d0_nat_full
    d0_nat_excluded_cylindric d0_nat_remaining_cylindric
    ltac:(intros item Hitem; unfold d0_nat_excluded, d0_nat_period in *;
      lia)) as Hextract.
  unfold SameSet in Hextract. rewrite Hextract.
  unfold d0_nat_period, d0_nat_excluded. lia.
Qed.

Example empty_excluded_minimal_extract_is_remaining : forall d
    (period remaining : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    QCylindric period remaining ->
    SameSet
      (ExtractFace period (ConeLineality (Cone period))
        (fun _ => False) remaining)
      remaining.
Proof.
  intros d period remaining Hperiodic Hfinite Hfull Hremaining value.
  pose proof (lemma_6_9_minimal_extract d period (fun _ => False)
    remaining Hperiodic Hfinite Hfull
    ltac:(intros base increment Hfalse; contradiction)
    Hremaining ltac:(intros item Hfalse; contradiction)) as Hextract.
  unfold SameSet in Hextract. specialize (Hextract value). tauto.
Qed.

Example equal_excluded_remaining_minimal_extract_is_empty : forall d
    (period remaining : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    QCylindric period remaining ->
    SameSet
      (ExtractFace period (ConeLineality (Cone period)) remaining remaining)
      (fun _ => False).
Proof.
  intros d period remaining Hperiodic Hfinite Hfull Hremaining value.
  pose proof (lemma_6_9_minimal_extract d period remaining remaining
    Hperiodic Hfinite Hfull Hremaining Hremaining
    ltac:(intros item Hitem; exact Hitem)) as Hextract.
  unfold SameSet in Hextract. specialize (Hextract value). tauto.
Qed.

Print Assumptions polyhedral_lineality_minimal_face.
Print Assumptions lineality_face_period_inverse.
Print Assumptions lemma_6_9_minimal_extract.
Print Assumptions lemma_6_9_any_minimal_face.
