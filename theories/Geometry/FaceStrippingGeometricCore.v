From Coq Require Import Classical_Prop Fin Lia List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import Code RunOrder.
From Mell.Geometry Require Import ClosedLinearization CommonIntegerFaceNormals
  Cone Corollary67Finitary FaceOrder Faces FaceStrippingBases
  FaceStrippingExtract FaceStrippingMonotoneSubsequence
  FaceStrippingOrderFoundation FaceZeroPatternWitness MathCompBridge Periodic
  QConeCore RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Fixpoint normal_list_difference {d}
    (normals excluded : list (ZVec d)) : list (ZVec d) :=
  match normals with
  | [] => []
  | normal :: tail =>
      if in_dec zvec_eq_dec normal excluded
      then normal_list_difference tail excluded
      else normal :: normal_list_difference tail excluded
  end.

Lemma normal_list_difference_spec : forall d
    (normals excluded : list (ZVec d)) normal,
    List.In normal (normal_list_difference normals excluded) <->
    List.In normal normals /\ ~ List.In normal excluded.
Proof.
  intros d normals. induction normals as [|head tail IH];
    intros excluded normal.
  - cbn [normal_list_difference]. tauto.
  - unfold normal_list_difference; fold @normal_list_difference.
    destruct (in_dec zvec_eq_dec head excluded) as [Hhead|Hhead] eqn:Hdecision;
      cbn.
    + rewrite IH. split.
      * intros [Hin Hnot]. split; [now right|exact Hnot].
      * intros [[Heq|Hin] Hnot].
        -- subst normal. contradiction.
        -- now split.
    + rewrite IH. split.
      * intros [Heq|[Hin Hnot]].
        -- subst normal. split; [now left|exact Hhead].
        -- split; [now right|exact Hnot].
      * intros [[Heq|Hin] Hnot].
        -- now left.
        -- right. now split.
Qed.

Theorem simultaneous_unbounded_normals_threshold : forall d
    (normals : list (ZVec d)) (sequence : nat -> ZVec d),
    (forall normal,
      List.In normal normals ->
      NormalTailUnbounded sequence normal) ->
    (forall normal,
      List.In normal normals -> forall n,
      (zinner normal (sequence n) <=
       zinner normal (sequence (S n)))%Z) ->
    forall (bound : ZVec d) lower,
      exists n,
        (lower <= n)%nat /\
        forall normal,
          List.In normal normals ->
          (zinner normal bound <= zinner normal (sequence n))%Z.
Proof.
  intros d normals. induction normals as [|head tail IH];
    intros sequence Hunbounded Hmonotone bound lower.
  - exists lower. split; [apply Nat.le_refl|]. intros normal Hin. contradiction.
  - destruct (Hunbounded head ltac:(now left)
      (zinner head bound) lower) as [head_index [Hhead_lower Hhead_bound]].
    destruct (IH sequence
      (fun normal Hin => Hunbounded normal ltac:(now right))
      (fun normal Hin => Hmonotone normal ltac:(now right))
      bound lower) as [tail_index [Htail_lower Htail_bound]].
    exists (Nat.max head_index tail_index). split; [lia|].
    intros normal [Heq|Hin].
    + subst normal. eapply Z.le_trans; [exact Hhead_bound|].
      apply monotone_integer_le with
        (sequence := fun n => zinner head (sequence n)).
      * apply Hmonotone. now left.
      * apply Nat.le_max_l.
    + eapply Z.le_trans; [apply Htail_bound; exact Hin|].
      apply monotone_integer_le with
        (sequence := fun n => zinner normal (sequence n)).
      * apply Hmonotone. now right.
      * apply Nat.le_max_r.
Qed.

Lemma zinner_nsmul : forall d coefficient (normal value : ZVec d),
    zinner normal (zvec_nsmul coefficient value) =
      (Z.of_nat coefficient * zinner normal value)%Z.
Proof.
  intros d coefficient. induction coefficient as [|coefficient IH];
    intros normal value.
  - cbn. rewrite zinner_zero. reflexivity.
  - cbn [zvec_nsmul]. rewrite zinner_add, IH, Nat2Z.inj_succ. ring.
Qed.

Theorem inactive_normals_uniform_nsmul : forall d
    (normals : list (ZVec d)) (base witness : ZVec d),
    (forall normal,
      List.In normal normals -> (0 < zinner normal witness)%Z) ->
    exists multiplier : nat,
      forall normal,
        List.In normal normals ->
        (0 <= zinner normal
          (zvec_add base (zvec_nsmul multiplier witness)))%Z.
Proof.
  intros d normals. induction normals as [|head tail IH];
    intros base witness Hpositive.
  - exists 0%nat. intros normal Hin. contradiction.
  - set (head_multiplier :=
      Z.to_nat (Z.max 0 (- zinner head base))).
    destruct (IH base witness
      (fun normal Hin => Hpositive normal ltac:(now right))) as
      [tail_multiplier Htail].
    exists (Nat.max head_multiplier tail_multiplier).
    intros normal [Heq|Hin].
    + subst normal. rewrite zinner_add, zinner_nsmul.
      assert (Hq : (1 <= zinner head witness)%Z).
      { pose proof (Hpositive head ltac:(now left)). lia. }
      assert (Hm :
          (Z.max 0 (- zinner head base) <=
           Z.of_nat (Nat.max head_multiplier tail_multiplier))%Z).
      { unfold head_multiplier. rewrite Nat2Z.inj_max.
        rewrite Z2Nat.id by apply Z.le_max_l.
        pose proof (Nat.le_max_l head_multiplier tail_multiplier).
        apply Nat2Z.inj_le in H. lia. }
      nia.
    + specialize (Htail normal Hin).
      rewrite !zinner_add, !zinner_nsmul in *.
      assert (Hq : (0 <= zinner normal witness)%Z).
      { pose proof (Hpositive normal ltac:(now right)). lia. }
      assert (Hm :
          (Z.of_nat tail_multiplier <=
           Z.of_nat (Nat.max head_multiplier tail_multiplier))%Z).
      { apply Nat2Z.inj_le, Nat.le_max_r. }
      nia.
Qed.

Definition prepared_threshold {d} (sequence : nat -> ZVec d)
    (normal : ZVec d) : Q :=
  inject_Z (zinner normal (sequence 0%nat)).

Definition corrected_remainder {d} (sequence : nat -> ZVec d)
    (index : nat) (increment : ZVec d) (multiplier : nat)
    (witness : ZVec d) : ZVec d :=
  zvec_add
    (zvec_sub (zvec_sub (sequence index) (sequence 0%nat)) increment)
    (zvec_nsmul multiplier witness).

Lemma qinner_integer_zero_iff : forall d (normal value : ZVec d),
    (qinner (zvec_to_qvec normal) (zvec_to_qvec value) == 0 <->
     zinner normal value = 0%Z).
Proof.
  intros d normal value. split; intro Hzero.
  - assert (Hinject : inject_Z (zinner normal value) == inject_Z 0%Z).
    { transitivity (qinner (zvec_to_qvec normal) (zvec_to_qvec value)).
      - symmetry. apply qinner_zvec_to_qvec.
      - transitivity 0; [exact Hzero|reflexivity]. }
    now apply (proj1 (inject_Z_injective _ _)) in Hinject.
  - transitivity (inject_Z (zinner normal value)).
    + apply qinner_zvec_to_qvec.
    + now rewrite Hzero.
Qed.

Lemma periodic_chain_members : forall d (period : ZSet d),
    Periodic period -> forall sequence : nat -> ZVec d,
    period (sequence 0%nat) ->
    (forall n, PeriodicLe period (sequence n) (sequence (S n))) ->
    forall n, period (sequence n).
Proof.
  intros d period Hperiodic sequence Hzero Hstep n.
  assert (Hdelta : PeriodicLe period (sequence 0%nat) (sequence n)).
  { apply periodic_le_sequence; [exact Hperiodic|exact Hstep|lia]. }
  unfold PeriodicLe in Hdelta.
  replace (sequence n) with
      (zvec_add (sequence 0%nat) (zvec_sub (sequence n) (sequence 0%nat))).
  - exact (proj2 Hperiodic _ _ Hzero Hdelta).
  - apply zvec_sub_add_cancel.
Qed.

Lemma corrected_remainder_difference_identity : forall d
    (sequence : nat -> ZVec d) index increment multiplier witness,
    corrected_remainder sequence index increment multiplier witness =
      zvec_sub
        (zvec_add (zvec_sub (sequence index) (sequence 0%nat))
          (zvec_nsmul multiplier witness))
        increment.
Proof.
  intros d sequence index increment multiplier witness.
  apply zvec_ext. intro coordinate.
  unfold corrected_remainder, zvec_add, zvec_sub.
  repeat rewrite (nth_map2 _ _ _ coordinate coordinate coordinate
    eq_refl eq_refl). lia.
Qed.

Lemma corrected_remainder_balance : forall d
    (sequence : nat -> ZVec d) index increment multiplier witness,
    zvec_add (sequence index) (zvec_nsmul multiplier witness) =
      zvec_add (zvec_add (sequence 0%nat) increment)
        (corrected_remainder sequence index increment multiplier witness).
Proof.
  intros d sequence index increment multiplier witness.
  apply zvec_ext. intro coordinate.
  unfold corrected_remainder, zvec_add, zvec_sub.
  repeat rewrite (nth_map2 _ _ _ coordinate coordinate coordinate
    eq_refl eq_refl). lia.
Qed.

Theorem finite_supporting_normals_prepared_reindex : forall d
    (period : ZSet d) (normals : list (ZVec d))
    (sequence : nat -> ZVec d),
    List.Forall
      (fun normal =>
        SupportingNormal (Cone period) (zvec_to_qvec normal)) normals ->
    (forall n, PeriodicLe period (sequence n) (sequence (S n))) ->
    exists unbounded N,
      (forall normal,
        List.In normal unbounded <->
        List.In normal normals /\ NormalTailUnbounded sequence normal) /\
      (forall normal,
        List.In normal normals ->
        ~ List.In normal unbounded ->
        forall n,
          zinner normal (tail_reindex sequence N n) =
          zinner normal (tail_reindex sequence N 0%nat)) /\
      (forall normal,
        List.In normal unbounded ->
        NormalTailUnbounded (tail_reindex sequence N) normal) /\
      (forall normal,
        List.In normal normals -> forall n,
        (zinner normal (tail_reindex sequence N n) <=
         zinner normal (tail_reindex sequence N (S n)))%Z).
Proof.
  intros d period normals sequence Hsupport Hstep.
  destruct (finite_supporting_normals_tail_reindex d period normals sequence
    Hsupport Hstep) as
    [unbounded [constant [N
      [Hunbounded [Hconstant [Hcommon [Hunbounded_tail Hmonotone]]]]]]].
  exists unbounded, N. split; [exact Hunbounded|].
  split.
  - intros normal Hnormal Hnot_unbounded n.
    apply Hcommon, Hconstant. split; [exact Hnormal|].
    destruct (supporting_normal_inner_tail_dichotomy d period normal sequence)
      as [Heventually|Htail].
    + exact (proj1 (List.Forall_forall _ _) Hsupport normal Hnormal).
    + exact Hstep.
    + exact Heventually.
    + exfalso. apply Hnot_unbounded, Hunbounded. now split.
  - now split.
Qed.

Theorem maximal_extract_prepared_chain_face_collapse : forall d
    (period excluded remaining : ZSet d) (face : QSet d)
    (normals unbounded : list (ZVec d))
    (sequence : nat -> ZVec d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    MaximalNonemptyExtractFace period excluded remaining face ->
    (forall point : QVec d,
      Cone period point <->
      forall normal,
        List.In normal normals ->
        0 <= qinner (zvec_to_qvec normal) point) ->
    QCylindric period excluded ->
    QCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    period (sequence 0%nat) ->
    (forall n,
      ExtractFace period face excluded remaining (sequence n)) ->
    (forall n,
      PeriodicLe period (sequence n) (sequence (S n))) ->
    (forall normal,
      List.In normal unbounded ->
      List.In normal normals /\ NormalTailUnbounded sequence normal) ->
    (forall normal,
      List.In normal normals ->
      ~ List.In normal unbounded ->
      forall n,
        zinner normal (sequence n) = zinner normal (sequence 0%nat)) ->
    exists active tight,
      (forall normal,
        List.In normal active <->
        List.In normal normals /\
        IntegerNormalOrthogonalToFace face normal) /\
      (forall normal,
        List.In normal tight <->
        List.In normal active /\ ~ List.In normal unbounded) /\
      (forall normal,
        List.In normal tight -> List.In normal normals) /\
      let larger := ThresholdFace (Cone period) tight in
      let slice := RationalThresholdSlice period normals tight
        (prepared_threshold sequence) in
      FaceOf (Cone period) larger /\
      FaceSubset face larger /\
      FinitaryQCylindric (FacePeriod period larger) slice /\
      (forall n, slice (sequence n)) /\
      ExtractFace period larger excluded remaining (sequence 0%nat) /\
      SameSet face larger.
Proof.
  intros d period excluded remaining face normals unbounded sequence
    Hperiodic Hgenerated Hfull Hmaximal Hcone Hexcluded_cyl Hremaining_cyl
    Hexcluded_remaining Hsequence_zero Hextract Hstep Hunbounded Hconstant.
  destruct Hmaximal as [Hface [_ Hmaximal]].
  assert (Hsupport : List.Forall
      (fun normal => SupportingNormal (Cone period) (zvec_to_qvec normal))
      normals).
  { now apply integer_hrep_normals_supporting. }
  destruct (face_active_integer_normals d normals face) as
    [active Hactive].
  set (tight := normal_list_difference active unbounded).
  assert (Htight : forall normal,
      List.In normal tight <->
      List.In normal active /\ ~ List.In normal unbounded).
  { intro normal. unfold tight. apply normal_list_difference_spec. }
  assert (Htight_normals : forall normal,
      List.In normal tight -> List.In normal normals).
  { intros normal Hin. apply Htight in Hin as [Hin _].
    now apply Hactive in Hin as [Hin _]. }
  set (larger := ThresholdFace (Cone period) tight).
  set (slice := RationalThresholdSlice period normals tight
    (prepared_threshold sequence)).
  assert (Hlarger_face : FaceOf (Cone period) larger).
  { unfold larger. now apply threshold_face_is_face with (normals := normals). }
  assert (Hface_subset : FaceSubset face larger).
  { intros point Hpoint. split.
    - now apply (face_subset d (Cone period) face Hface).
    - intros normal Hin.
      apply Htight in Hin as [Hactive_normal _].
      apply Hactive in Hactive_normal as [_ Horthogonal].
      now apply Horthogonal. }
  assert (Hfinitary : FinitaryQCylindric
      (FacePeriod period larger) slice).
  { unfold larger, slice.
    now apply corollary_6_7_finitary. }
  assert (Hsequence_period : forall n, period (sequence n)).
  { now apply periodic_chain_members. }
  assert (Hmonotone : forall normal,
      List.In normal normals -> forall n,
      (zinner normal (sequence n) <=
       zinner normal (sequence (S n)))%Z).
  { intros normal Hin.
    apply supporting_normal_monotone_sequence with (period := period).
    - exact (proj1 (List.Forall_forall _ _) Hsupport normal Hin).
    - exact Hstep. }
  assert (Hsequence_slice : forall n, slice (sequence n)).
  { intro n. unfold slice, RationalThresholdSlice, prepared_threshold.
    split; [apply Hsequence_period|]. split.
    - intros normal Hin. apply Qle_trans with
        (y := inject_Z (zinner normal (sequence n))).
      + rewrite <- Zle_Qle. apply monotone_integer_le with
          (sequence := fun k => zinner normal (sequence k));
          [apply Hmonotone; exact Hin|lia].
      + pose proof (qinner_zvec_to_qvec d normal (sequence n)) as Hinner.
        apply (proj1 (Qle_comp
          (inject_Z (zinner normal (sequence n)))
          (inject_Z (zinner normal (sequence n))) (Qeq_refl _)
          (inject_Z (zinner normal (sequence n)))
          (qinner (zvec_to_qvec normal) (zvec_to_qvec (sequence n)))
          ltac:(now symmetry))).
        apply Qle_refl.
    - intros normal Hin.
      assert (Hnormal_constant : forall k,
          zinner normal (sequence k) = zinner normal (sequence 0%nat)).
      { apply Hconstant.
        - apply Htight_normals. exact Hin.
        - exact (proj2 (proj1 (Htight normal) Hin)). }
      transitivity (inject_Z (zinner normal (sequence n))).
      + apply qinner_zvec_to_qvec.
      + now rewrite Hnormal_constant. }
  destruct (face_zero_pattern_witness d period face normals Hperiodic
    Hface Hsupport) as [witness [Hwitness_period Hzero_pattern]].
  assert (Hextract_larger :
      ExtractFace period larger excluded remaining (sequence 0%nat)).
  { intros increment Hincrement. split.
    - assert (Hremaining_zero : remaining (sequence 0%nat)).
      { pose proof (face_periodic d period face Hperiodic Hface) as Hfp.
        pose proof (Hextract 0%nat (zvec_zero d) (proj1 Hfp)) as Hextract0.
        now rewrite zvec_add_zero_right in Hextract0. }
      apply Hremaining_cyl; [exact Hremaining_zero|exact (proj1 Hincrement)].
    - intro Hexcluded_shift.
      destruct (simultaneous_unbounded_normals_threshold d unbounded sequence
        (fun normal Hin => proj2 (Hunbounded normal Hin))
        (fun normal Hin => Hmonotone normal (proj1 (Hunbounded normal Hin)))
        (zvec_add (sequence 0%nat) increment) 0%nat) as
        [index [_ Hindex]].
      destruct (face_inactive_integer_normals d normals face) as
        [inactive Hinactive].
      set (base := zvec_sub
        (zvec_sub (sequence index) (sequence 0%nat)) increment).
      assert (Hinactive_positive : forall normal,
          List.In normal inactive -> (0 < zinner normal witness)%Z).
      { intros normal Hin.
        apply Hinactive in Hin as [Hnormal Hnot_orthogonal].
        assert (Hnonnegative : (0 <= zinner normal witness)%Z).
        { apply (proj1 (integer_qinner_nonnegative_iff d normal witness)).
          apply (proj1 (List.Forall_forall _ _) Hsupport normal Hnormal).
          now apply (face_subset d (Cone period) face Hface),
            (proj2 Hwitness_period). }
        assert (Hnonzero : zinner normal witness <> 0%Z).
        { intro Hzero. apply Hnot_orthogonal.
          apply (proj2 (Hzero_pattern normal Hnormal)).
          now apply (proj2 (qinner_integer_zero_iff d normal witness)). }
        lia. }
      destruct (inactive_normals_uniform_nsmul d inactive base witness
        Hinactive_positive) as [multiplier Hmultiplier].
      set (remainder := corrected_remainder sequence index increment
        multiplier witness).
      assert (Hremainder_inner : forall normal,
          List.In normal normals ->
          (0 <= zinner normal remainder)%Z).
      { intros normal Hnormal.
        destruct (classic (IntegerNormalOrthogonalToFace face normal)) as
          [Horthogonal|Hnot_orthogonal].
        - assert (Hnormal_active : List.In normal active).
          { apply Hactive. now split. }
          destruct (classic (List.In normal unbounded)) as [HinU|HnotU].
          + assert (Hlarge := Hindex normal HinU).
            assert (Hwitness_zero : zinner normal witness = 0%Z).
            { apply (proj1 (qinner_integer_zero_iff d normal witness)).
              apply (proj1 (Hzero_pattern normal Hnormal)). exact Horthogonal. }
            unfold remainder, corrected_remainder, base.
            rewrite zinner_add, zinner_sub_right, zinner_sub_right,
              zinner_nsmul, Hwitness_zero.
            rewrite zinner_add in Hlarge. lia.
          + assert (Htight_normal : List.In normal tight).
            { apply Htight. now split. }
            assert (Hconstant_normal := Hconstant normal Hnormal HnotU index).
            assert (Hincrement_zero : zinner normal increment = 0%Z).
            { apply (proj1 (qinner_integer_zero_iff d normal increment)).
              pose proof (proj2 Hincrement) as Hincrement_larger.
              unfold larger, ThresholdFace in Hincrement_larger.
              exact (proj2 Hincrement_larger normal Htight_normal). }
            assert (Hwitness_zero : zinner normal witness = 0%Z).
            { apply (proj1 (qinner_integer_zero_iff d normal witness)).
              apply (proj1 (Hzero_pattern normal Hnormal)). exact Horthogonal. }
            unfold remainder, corrected_remainder, base.
            rewrite zinner_add, zinner_sub_right, zinner_sub_right,
              zinner_nsmul, Hconstant_normal, Hincrement_zero,
              Hwitness_zero. lia.
        - assert (Hin : List.In normal inactive).
          { apply Hinactive. now split. }
          unfold remainder, corrected_remainder. apply Hmultiplier. exact Hin. }
      assert (Hremainder_cone : Cone period (zvec_to_qvec remainder)).
      { apply (proj2 (Hcone _)). intros normal Hin.
        apply (proj2 (integer_qinner_nonnegative_iff d normal remainder)).
        now apply Hremainder_inner. }
      assert (Hdelta : period
          (zvec_sub (sequence index) (sequence 0%nat))).
      { exact (periodic_le_sequence d period Hperiodic sequence Hstep
          0%nat index ltac:(lia)). }
      assert (Hscaled : period (zvec_nsmul multiplier witness)).
      { apply periodic_nsmul; [exact Hperiodic|exact (proj1 Hwitness_period)]. }
      assert (Hremainder_difference : Difference period remainder).
      { unfold remainder. rewrite corrected_remainder_difference_identity.
        exists (zvec_add (zvec_sub (sequence index) (sequence 0%nat))
          (zvec_nsmul multiplier witness)), increment.
        repeat split.
        - exact (proj2 Hperiodic _ _ Hdelta Hscaled).
        - exact (proj1 Hincrement). }
      assert (Hremainder_period : period remainder).
      { apply (proj2 (full_periodic_member_iff_difference_cone d period
          Hperiodic Hfull remainder)). now split. }
      assert (Hexcluded_right : excluded
          (zvec_add (zvec_add (sequence 0%nat) increment) remainder)).
      { apply Hexcluded_cyl; [exact Hexcluded_shift|exact Hremainder_period]. }
      unfold remainder in Hexcluded_right.
      rewrite <- corrected_remainder_balance in Hexcluded_right.
      pose proof (Hextract index (zvec_nsmul multiplier witness)) as
        Hextract_index.
      assert (Hscaled_face : FacePeriod period face
          (zvec_nsmul multiplier witness)).
      { apply periodic_nsmul.
        - now apply face_periodic.
        - exact Hwitness_period. }
      exact (proj2 (Hextract_index Hscaled_face) Hexcluded_right). }
  assert (Hsame : SameSet face larger).
  { apply Hmaximal; [exact Hlarger_face|exact Hface_subset|].
    now exists (sequence 0%nat). }
  exists active, tight.
  split; [exact Hactive|].
  split; [exact Htight|].
  split; [exact Htight_normals|].
  exact (conj Hlarger_face
    (conj Hface_subset
      (conj Hfinitary
        (conj Hsequence_slice
          (conj Hextract_larger Hsame))))).
Qed.
