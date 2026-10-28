From Coq Require Import Lra QArith QArith.Qabs Qring Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore ClosedLinearization
  FaceStrippingLemma610 Faces QratHomogeneousAdapter RationalClosure
  RationalHToV Periodic Cone.
From Mell.Order Require Import PeriodicOrder.

Open Scope Q_scope.

Fixpoint qinner_continuity_weight (d : nat) : QVec d -> Q :=
  match d return QVec d -> Q with
  | O => fun _ => 1
  | S tail => fun normal =>
      Qabs (normal Fin.F1) + 1 +
      qinner_continuity_weight tail (fun index => normal (Fin.FS index))
  end.

Lemma qinner_continuity_weight_positive : forall d (normal : QVec d),
  0 < qinner_continuity_weight d normal.
Proof.
  intros d. induction d as [|d IH]; intro normal; cbn.
  - reflexivity.
  - setoid_replace 0 with (0 + 0) by ring.
    apply Qplus_lt_compat.
    + apply Qlt_le_trans with 1; [reflexivity|].
      setoid_replace 1 with (0 + 1) by ring.
      apply Qplus_le_compat; [apply Qabs_nonneg|apply Qle_refl].
    + apply IH.
Qed.

Lemma qinner_uniform_continuity_bound : forall d
    (normal point approximant : QVec d) delta,
  0 < delta ->
  (forall index, Qabs (point index - approximant index) < delta) ->
  Qabs (qinner normal point - qinner normal approximant) <
    delta * qinner_continuity_weight d normal.
Proof.
  intros d. induction d as [|d IH]; intros normal point approximant delta
      Hdelta Hclose.
  - cbn [qinner qrow_apply qvec_to_vector qdot
      qinner_continuity_weight]. unfold Qminus.
    setoid_replace (delta * 1) with delta by ring.
    rewrite Qplus_opp_r, Qabs_pos; [exact Hdelta|apply Qle_refl].
  - cbn [qinner qrow_apply qvec_to_vector qdot
      qinner_continuity_weight].
    set (head_difference := point Fin.F1 - approximant Fin.F1).
    set (tail_normal := fun index : Fin.t d => normal (Fin.FS index)).
    set (tail_point := fun index : Fin.t d => point (Fin.FS index)).
    set (tail_approximant :=
      fun index : Fin.t d => approximant (Fin.FS index)).
    change (Qabs
      ((normal Fin.F1 * point Fin.F1 + qinner tail_normal tail_point) -
       (normal Fin.F1 * approximant Fin.F1 +
        qinner tail_normal tail_approximant)) <
      delta *
        (Qabs (normal Fin.F1) + 1 +
          qinner_continuity_weight d tail_normal)).
    assert (Htail := IH tail_normal tail_point tail_approximant delta
      Hdelta (fun index => Hclose (Fin.FS index))).
    assert (Hhead_close : Qabs head_difference < delta).
    { exact (Hclose Fin.F1). }
    assert (Hhead_nonnegative : 0 <= Qabs (normal Fin.F1))
      by apply Qabs_nonneg.
    assert (Hhead_bound :
      Qabs (normal Fin.F1 * head_difference) <
        delta * (Qabs (normal Fin.F1) + 1)).
    { setoid_rewrite Qabs_Qmult.
      eapply Qle_lt_trans.
      - setoid_replace
          (Qabs (normal Fin.F1) * Qabs head_difference) with
          (Qabs head_difference * Qabs (normal Fin.F1)) by ring.
        apply Qmult_le_compat_r; [apply Qlt_le_weak; exact Hhead_close|].
        exact Hhead_nonnegative.
      - setoid_replace (delta * Qabs (normal Fin.F1)) with
          (Qabs (normal Fin.F1) * delta) by ring.
        setoid_replace (delta * (Qabs (normal Fin.F1) + 1)) with
          ((Qabs (normal Fin.F1) + 1) * delta) by ring.
        apply Qmult_lt_compat_r; [exact Hdelta|].
        apply (proj1 (Qplus_lt_r (Qabs (normal Fin.F1))
          (Qabs (normal Fin.F1) + 1) (- Qabs (normal Fin.F1)))).
        setoid_replace (- Qabs (normal Fin.F1) + Qabs (normal Fin.F1))
          with 0 by ring.
        setoid_replace
          (- Qabs (normal Fin.F1) + (Qabs (normal Fin.F1) + 1))
          with 1 by ring. reflexivity. }
    setoid_replace
      ((normal Fin.F1 * point Fin.F1 + qinner tail_normal tail_point) -
       (normal Fin.F1 * approximant Fin.F1 +
        qinner tail_normal tail_approximant)) with
      (normal Fin.F1 * head_difference +
       (qinner tail_normal tail_point -
        qinner tail_normal tail_approximant)) by
      (unfold head_difference; ring).
    eapply Qle_lt_trans.
    + apply Qabs_triangle.
    + eapply Qlt_le_trans.
      * apply Qplus_lt_compat; [exact Hhead_bound|exact Htail].
      * setoid_replace
          (delta * (Qabs (normal Fin.F1) + 1) +
            delta * qinner_continuity_weight d tail_normal) with
          (delta * (Qabs (normal Fin.F1) + 1 +
            qinner_continuity_weight d tail_normal)) by ring.
        apply Qle_refl.
Qed.

Theorem finitely_generated_rational_cone_closed : forall d
    (generators : list (QVec d)),
  TopologicallyClosed (qcone_generated generators).
Proof.
  intros d generators point Hclosure.
  destruct (@polyhedra_cone_homogeneous_base d generators) as
    [normals Hnormals].
  apply (proj2 (Hnormals point)). intros normal Hnormal.
  destruct (Qlt_le_dec (qinner normal point) 0) as [Hnegative|Hnonnegative];
    [|exact Hnonnegative].
  set (weight := qinner_continuity_weight d normal).
  assert (Hweight : 0 < weight).
  { apply qinner_continuity_weight_positive. }
  set (delta := (- qinner normal point) / weight).
  assert (Hdelta : 0 < delta).
  { unfold delta, Qdiv. apply Qmult_lt_0_compat.
    - pose proof (Qopp_lt_compat _ _ Hnegative) as Hopp.
      setoid_replace (- 0) with 0 in Hopp by ring. exact Hopp.
    - now apply Qinv_lt_0_compat. }
  destruct (Hclosure delta Hdelta) as
    [approximant [Happroximant Hclose]].
  pose proof (qinner_uniform_continuity_bound d normal point approximant
    delta Hdelta Hclose) as Hbound.
  assert (Hscaled : delta * weight == - qinner normal point).
  { unfold delta. setoid_replace
      ((- qinner normal point / weight) * weight) with
      ((- qinner normal point * weight) / weight) by
      (unfold Qdiv; ring).
    apply Qdiv_mult_l. intro Hzero.
    apply (Qlt_not_eq 0 weight Hweight). symmetry. exact Hzero. }
  change (Qabs (qinner normal point - qinner normal approximant) <
    delta * weight) in Hbound.
  setoid_rewrite Hscaled in Hbound.
  apply (proj1 (Qabs_Qlt_condition
    (qinner normal point - qinner normal approximant)
    (- qinner normal point))) in Hbound.
  pose proof (proj1 (Hnormals approximant) Happroximant normal Hnormal)
    as Happroximant_nonnegative.
  destruct Hbound as [Hlower _].
  setoid_replace (- (- qinner normal point)) with
    (qinner normal point) in Hlower by ring.
  exfalso. apply (Qlt_not_le _ _ Hlower).
  assert (Hle : qinner normal point + - qinner normal approximant <=
      qinner normal point + 0).
  { apply Qplus_le_compat; [apply Qle_refl|].
    setoid_replace 0 with (- 0) by ring.
    now apply Qopp_le_compat. }
  unfold Qminus. setoid_replace (qinner normal point + 0) with
    (qinner normal point) in Hle by ring. exact Hle.
Qed.

Lemma finitely_generated_period_cone_closed : forall d (period : ZSet d),
  Periodic period -> FinitelyGeneratedPeriodic period ->
  TopologicallyClosed (Cone period).
Proof.
  intros d period Hperiodic Hfinite point Hclosure.
  destruct (finitely_generated_period_cone_polyhedral d period
    Hperiodic Hfinite) as [generators Hgenerators].
  apply (proj2 (Hgenerators point)).
  apply finitely_generated_rational_cone_closed.
  intros delta Hdelta. destruct (Hclosure delta Hdelta) as
    [approximant [Happroximant Hclose]].
  exists approximant. split; [now apply (proj1 (Hgenerators approximant))|].
  exact Hclose.
Qed.

Theorem remark_2_2_full_iff_closed_linearization_fixed : forall d
    (period : ZSet d),
  Periodic period -> FinitelyGeneratedPeriodic period ->
  (FullPeriodic period <-> SameSet (ClosedLinearization period) period).
Proof.
  intros d period Hperiodic Hfinite. split.
  - intros Hfull value. split.
    + intros [Hdifference Hclosure].
      apply (proj1 (full_periodic_iff_linearization_fixed d period Hperiodic)
        Hfull value), conj; [exact Hdifference|].
      now apply (finitely_generated_period_cone_closed d period
        Hperiodic Hfinite).
    + intros Hvalue. split.
      * exact (proj1 (periodic_subset_linearization d period Hperiodic
          value Hvalue)).
      * apply qclosure_extensive.
        exact (proj2 (periodic_subset_linearization d period Hperiodic
          value Hvalue)).
  - intros Hfixed.
    apply (proj2 (full_periodic_iff_linearization_fixed d period Hperiodic)).
    intro value. split.
    + intros Hvalue.
      exact (periodic_subset_linearization d period Hperiodic value Hvalue).
    + intros Hvalue.
      apply (proj1 (Hfixed value)). split.
      * exact (proj1 Hvalue).
      * apply qclosure_extensive. exact (proj2 Hvalue).
Qed.
