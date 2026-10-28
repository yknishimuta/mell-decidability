From Coq Require Import Lia List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Geometry Require Import FaceStrippingBases FaceStrippingGeometricCore
  FaceStrippingOrderFoundation Periodic.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.

Check @normal_list_difference.
Check @normal_list_difference_spec.
Check @simultaneous_unbounded_normals_threshold.
Check @inactive_normals_uniform_nsmul.
Check @finite_supporting_normals_prepared_reindex.
Check @corrected_remainder_difference_identity.
Check @corrected_remainder_balance.
Check @maximal_extract_prepared_chain_face_collapse.

Example prepared_threshold_is_reindexed_zero : forall d
    (sequence : nat -> ZVec d) normal,
    prepared_threshold sequence normal =
      inject_Z (zinner normal (sequence 0%nat)).
Proof. reflexivity. Qed.

Example empty_unbounded_list_makes_tight_equal_active : forall d
    (active : list (ZVec d)) normal,
    List.In normal (normal_list_difference active []) <->
    List.In normal active.
Proof.
  intros. rewrite normal_list_difference_spec. tauto.
Qed.

Example all_active_normals_unbounded_makes_tight_empty : forall d
    (active unbounded : list (ZVec d)),
    (forall normal, List.In normal active -> List.In normal unbounded) ->
    forall normal,
      ~ List.In normal (normal_list_difference active unbounded).
Proof.
  intros d active unbounded Hsubset normal Hin.
  apply normal_list_difference_spec in Hin as [Hin Hnot].
  now apply Hnot, Hsubset.
Qed.

Example empty_unbounded_family_has_common_index : forall d
    (sequence : nat -> ZVec d) (bound : ZVec d) lower,
    exists n,
      (lower <= n)%nat /\
      forall normal,
        List.In normal ([] : list (ZVec d)) ->
        (zinner normal bound <= zinner normal (sequence n))%Z.
Proof.
  intros d sequence bound lower.
  apply simultaneous_unbounded_normals_threshold.
  - intros normal Hin. inversion Hin.
  - intros normal Hin. inversion Hin.
Qed.

Example duplicate_unbounded_family_uses_one_index : forall d
    (normal : ZVec d) (sequence : nat -> ZVec d),
    NormalTailUnbounded sequence normal ->
    (forall n,
      (zinner normal (sequence n) <=
       zinner normal (sequence (S n)))%Z) ->
    forall bound lower,
      exists n,
        (lower <= n)%nat /\
        forall candidate,
          List.In candidate [normal; normal] ->
          (zinner candidate bound <= zinner candidate (sequence n))%Z.
Proof.
  intros d normal sequence Hunbounded Hmonotone bound lower.
  apply simultaneous_unbounded_normals_threshold.
  - intros candidate [->|[->|[]]]; exact Hunbounded.
  - intros candidate [->|[->|[]]]; exact Hmonotone.
Qed.

Example empty_inactive_family_needs_no_correction : forall d
    (base witness : ZVec d),
    exists multiplier : nat,
      forall normal,
        List.In normal ([] : list (ZVec d)) ->
        (0 <= zinner normal
          (zvec_add base (zvec_nsmul multiplier witness)))%Z.
Proof.
  intros. apply inactive_normals_uniform_nsmul.
  intros normal Hin. inversion Hin.
Qed.

Example one_positive_inactive_normal_has_uniform_correction : forall d
    (normal base witness : ZVec d),
    (0 < zinner normal witness)%Z ->
    exists multiplier : nat,
      (0 <= zinner normal
        (zvec_add base (zvec_nsmul multiplier witness)))%Z.
Proof.
  intros d normal base witness Hpositive.
  destruct (inactive_normals_uniform_nsmul d [normal] base witness)
    as [multiplier Hmultiplier].
  - intros candidate [->|[]]. exact Hpositive.
  - exists multiplier. apply Hmultiplier. now left.
Qed.

Example corrected_remainder_balances_exactly : forall d
    (sequence : nat -> ZVec d) index increment multiplier witness,
    zvec_add (sequence index) (zvec_nsmul multiplier witness) =
      zvec_add (zvec_add (sequence 0%nat) increment)
        (corrected_remainder sequence index increment multiplier witness).
Proof. exact corrected_remainder_balance. Qed.

Example zero_dimensional_corrected_remainder_balances
    (sequence : nat -> ZVec 0) index increment multiplier witness :
    zvec_add (sequence index) (zvec_nsmul multiplier witness) =
      zvec_add (zvec_add (sequence 0%nat) increment)
        (corrected_remainder sequence index increment multiplier witness).
Proof. apply corrected_remainder_balance. Qed.

Example every_generated_period_chain_stays_in_period : forall d
    (generators : list (ZVec d)) (sequence : nat -> ZVec d),
    zvec_generated generators (sequence 0%nat) ->
    (forall n,
      PeriodicOrder.PeriodicLe (zvec_generated generators)
        (sequence n) (sequence (S n))) ->
    forall n, zvec_generated generators (sequence n).
Proof.
  intros d generators sequence Hzero Hstep.
  apply periodic_chain_members; [apply generated_periodic|exact Hzero|exact Hstep].
Qed.

Print Assumptions simultaneous_unbounded_normals_threshold.
Print Assumptions inactive_normals_uniform_nsmul.
Print Assumptions finite_supporting_normals_prepared_reindex.
Print Assumptions maximal_extract_prepared_chain_face_collapse.
