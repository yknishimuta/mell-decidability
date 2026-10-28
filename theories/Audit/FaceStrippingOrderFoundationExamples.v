From Coq Require Import Lia List ZArith.
From KruskalAfProp Require Import af.af.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Cone FaceOrder Faces FaceStrippingBases
  FaceStrippingExtract FaceStrippingFinitary FaceStrippingOrderFoundation FiniteFaces
  LatticeGordanInterface MathCompBridge QConeCore RationalDefinability.
From Mell.Order Require Import PeriodicOrder.
From Mell.Audit Require Import FaceStrippingExtractExamples
  FaceStrippingFinitaryExamples PeriodicOrderStatements.

Import ListNotations.
Open Scope Z_scope.

Check @MaximalNonemptyExtractFace.
Check @extract_face_antitone.
Check @extract_face_same_set.
Check @maximal_nonempty_extract_face_exists.
Check @finitary_qcylindric_afs.
Check @finitary_qcylindric_good_pair.
Check @monotone_integer_tail_dichotomy.
Check @supporting_normal_monotone.
Check @supporting_normal_monotone_sequence.
Check @finite_supporting_normals_tail_classification.

Example extract_face_antitone_direction : forall d
    (period excluded remaining : ZSet d)
    (smaller larger : QSet d),
    FaceSubset smaller larger ->
    forall value,
      ExtractFace period larger excluded remaining value ->
      ExtractFace period smaller excluded remaining value.
Proof. exact extract_face_antitone. Qed.

Example extract_face_same_set_reflexive : forall d
    (period excluded remaining : ZSet d) (face : QSet d),
    SameSet
      (ExtractFace period face excluded remaining)
      (ExtractFace period face excluded remaining).
Proof.
  intros. apply extract_face_same_set, same_set_refl.
Qed.

Example maximal_nonempty_extract_face_connection : forall d
    (period excluded remaining : ZSet d),
    RationalPolyhedralCone (Cone period) ->
    (exists face value,
      FaceOf (Cone period) face /\
      ExtractFace period face excluded remaining value) ->
    exists face,
      MaximalNonemptyExtractFace period excluded remaining face.
Proof. exact maximal_nonempty_extract_face_exists. Qed.

Lemma generated_period_self_afs : forall d (generators : list (ZVec d)),
    afs (zvec_generated generators)
      (PeriodicLe (zvec_generated generators)).
Proof.
  intros d generators. apply finitary_qcylindric_afs.
  - apply generated_periodic.
  - apply generated_period_finitely_generated.
  - apply period_finitary_self, generated_periodic.
Qed.

Definition order_foundation_two_nat : ZSet 1 :=
  zvec_generated [extract_z1 2].

Example zero_period_order_afs : forall d,
    afs (@zvec_generated d [])
      (PeriodicLe (@zvec_generated d [])).
Proof. intros. apply generated_period_self_afs. Qed.

Example zero_dimension_order_afs :
    afs (@zvec_generated 0 [])
      (PeriodicLe (@zvec_generated 0 [])).
Proof. apply generated_period_self_afs. Qed.

Example nat_order_afs :
    afs extract_nat_period (PeriodicLe extract_nat_period).
Proof. apply generated_period_self_afs. Qed.

Example two_nat_order_afs :
    afs order_foundation_two_nat (PeriodicLe order_foundation_two_nat).
Proof. apply generated_period_self_afs. Qed.

Example quadrant_order_afs :
    afs extract_quadrant_period (PeriodicLe extract_quadrant_period).
Proof. apply generated_period_self_afs. Qed.

Example integer_group_order_afs :
    afs extract_lineality_period (PeriodicLe extract_lineality_period).
Proof. apply generated_period_self_afs. Qed.

Example low_rank_signed_order_afs :
    afs low_rank_signed_period (PeriodicLe low_rank_signed_period).
Proof. apply generated_period_self_afs. Qed.

Example constant_integer_sequence_is_eventually_constant :
    EventuallyConstantIntegerSequence (fun _ => (-7)%Z).
Proof. exists 0%nat. reflexivity. Qed.

Example constant_integer_sequence_not_unbounded :
    ~ TailUnboundedIntegerSequence (fun _ => (-7)%Z).
Proof.
  apply eventually_constant_not_tail_unbounded.
  exact constant_integer_sequence_is_eventually_constant.
Qed.

Example natural_integer_sequence_is_tail_unbounded :
    TailUnboundedIntegerSequence (fun n => Z.of_nat n).
Proof.
  intros bound N.
  exists (N + Z.to_nat (Z.max 0 bound))%nat. split; [lia|].
  rewrite Nat2Z.inj_add.
  destruct (Z_le_dec 0 bound) as [Hbound|Hbound].
  - rewrite Z.max_r by exact Hbound.
    rewrite Z2Nat.id by exact Hbound. lia.
  - rewrite Z.max_l by lia. cbn. lia.
Qed.

Example negative_start_sequence_is_tail_unbounded :
    TailUnboundedIntegerSequence (fun n => (Z.of_nat n - 10)%Z).
Proof.
  intros bound N.
  exists (N + Z.to_nat (Z.max 0 (bound + 10)))%nat. split; [lia|].
  rewrite Nat2Z.inj_add.
  destruct (Z_le_dec 0 (bound + 10)) as [Hbound|Hbound].
  - rewrite Z.max_r by exact Hbound.
    rewrite Z2Nat.id by exact Hbound. lia.
  - rewrite Z.max_l by lia. cbn. lia.
Qed.

Example eventually_three_sequence_is_eventually_constant :
    EventuallyConstantIntegerSequence
      (fun n => if (n <? 3)%nat then Z.of_nat n else 3%Z).
Proof.
  exists 3%nat. intros n Hn.
  change ((if (n <? 3)%nat then Z.of_nat n else 3%Z) = 3%Z).
  destruct (n <? 3)%nat eqn:Hlt; [apply Nat.ltb_lt in Hlt; lia|reflexivity].
Qed.

Example empty_supporting_family_classifies : forall d
    (period : ZSet d) (sequence : nat -> ZVec d),
    (forall n, PeriodicLe period (sequence n) (sequence (S n))) ->
    exists unbounded constant N,
      (forall normal,
        List.In normal unbounded <->
        List.In normal ([] : list (ZVec d)) /\
          NormalTailUnbounded sequence normal) /\
      (forall normal,
        List.In normal constant <->
        List.In normal ([] : list (ZVec d)) /\
          NormalEventuallyConstant sequence normal) /\
      (forall normal,
        List.In normal constant ->
        forall n, (N <= n)%nat ->
          zinner normal (sequence n) = zinner normal (sequence N)).
Proof.
  intros d period sequence Hsequence.
  apply (finite_supporting_normals_tail_classification
    d period [] sequence); [constructor|assumption].
Qed.

Example duplicate_supporting_normals_classify : forall d
    (period : ZSet d) (normal : ZVec d)
    (sequence : nat -> ZVec d),
    SupportingNormal (Cone period) (zvec_to_qvec normal) ->
    (forall n, PeriodicLe period (sequence n) (sequence (S n))) ->
    exists unbounded constant N,
      (forall candidate,
        List.In candidate unbounded <->
        List.In candidate [normal; normal] /\
          NormalTailUnbounded sequence candidate) /\
      (forall candidate,
        List.In candidate constant <->
        List.In candidate [normal; normal] /\
          NormalEventuallyConstant sequence candidate) /\
      (forall candidate,
        List.In candidate constant ->
        forall n, (N <= n)%nat ->
          zinner candidate (sequence n) =
          zinner candidate (sequence N)).
Proof.
  intros d period normal sequence Hsupport Hsequence.
  apply (finite_supporting_normals_tail_classification
    d period [normal; normal] sequence); [repeat constructor; assumption|].
  exact Hsequence.
Qed.

Example supporting_normal_sequence_connection : forall d
    (period : ZSet d) (normal : ZVec d)
    (sequence : nat -> ZVec d),
    SupportingNormal (Cone period) (zvec_to_qvec normal) ->
    (forall n, PeriodicLe period (sequence n) (sequence (S n))) ->
    forall n,
      (zinner normal (sequence n) <=
       zinner normal (sequence (S n)))%Z.
Proof. exact supporting_normal_monotone_sequence. Qed.

Print Assumptions MaximalNonemptyExtractFace.
Print Assumptions extract_face_antitone.
Print Assumptions extract_face_same_set.
Print Assumptions maximal_nonempty_extract_face_exists.
Print Assumptions finitary_qcylindric_afs.
Print Assumptions finitary_qcylindric_good_pair.
Print Assumptions monotone_integer_tail_dichotomy.
Print Assumptions supporting_normal_monotone_sequence.
Print Assumptions finite_supporting_normals_tail_classification.
