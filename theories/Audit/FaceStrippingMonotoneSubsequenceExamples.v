From Coq Require Import Lia List Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Geometry Require Import FaceStrippingMonotoneSubsequence
  FaceStrippingFinitary FaceStrippingOrderFoundation Periodic.
From Mell.Order Require Import PeriodicOrder.

Check finitary_qcylindric_monotone_subsequence.
Check strictly_increasing_unbounded.
Check strictly_increasing_compose.
Check periodic_le_sequence.
Check eventually_constant_strict_subsequence.
Check tail_unbounded_strict_subsequence.
Check finite_supporting_normals_tail_reindex.

Example constant_sequence_has_monotone_subsequence :
  exists indices,
    StrictlyIncreasing indices /\
    forall n : nat, (7 <= 7)%nat.
Proof.
  exists (fun n => n). split; [intro n; lia|auto].
Qed.

Example increasing_sequence_has_identity_subsequence :
  StrictlyIncreasing (fun n => n) /\
  forall n, (n <= S n)%nat.
Proof. split; intro n; lia. Qed.

Definition initially_decreasing (n : nat) : nat :=
  match n with O => 5 | S n' => n' end.

Example initially_decreasing_has_monotone_tail :
  StrictlyIncreasing (fun n => S n) /\
  forall n,
    (initially_decreasing (S n) <= initially_decreasing (S (S n)))%nat.
Proof. split; intro n; cbn; lia. Qed.

Definition alternating_two_bases (n : nat) : nat := Nat.modulo n 2.

Example alternating_two_bases_constant_subsequence :
  exists value indices,
    (value < 2)%nat /\ StrictlyIncreasing indices /\
    forall n, alternating_two_bases (indices n) = value.
Proof.
  apply bounded_nat_constant_subsequence.
  intro n. unfold alternating_two_bases. apply Nat.mod_upper_bound. lia.
Qed.

Example zero_dimensional_nvec_subsequence (sequence : nat -> NVec 0) :
  exists indices,
    StrictlyIncreasing indices /\
    forall n, nvec_le (sequence (indices n)) (sequence (indices (S n))).
Proof. apply nvec_monotone_subsequence. Qed.

Example every_finitely_generated_period_has_monotone_subsequences :
  forall d (generators : list (ZVec d)) (sequence : nat -> ZVec d),
    (forall n, zvec_generated generators (sequence n)) ->
    exists indices,
      StrictlyIncreasing indices /\
      forall n,
        PeriodicLe (zvec_generated generators)
          (sequence (indices n)) (sequence (indices (S n))).
Proof.
  intros d generators sequence Hsequence.
  apply (finitary_qcylindric_monotone_subsequence d
    (zvec_generated generators) (zvec_generated generators)).
  - apply generated_periodic.
  - exists generators. split.
    + intros generator Hin. now apply generated_generator.
    + intro value. reflexivity.
  - apply period_finitary_self, generated_periodic.
  - exact Hsequence.
Qed.

Example negative_start_tail_unbounded :
  TailUnboundedIntegerSequence (fun n => (Z.of_nat n - 10)%Z).
Proof.
  intros bound N.
  exists (N + Z.to_nat (Z.max 0 (bound + 10)))%nat. split; [lia|].
  rewrite Nat2Z.inj_add, Z2Nat.id by apply Z.le_max_l.
  pose proof (Z.le_max_r 0 (bound + 10)). lia.
Qed.

Print Assumptions finitary_qcylindric_monotone_subsequence.
Print Assumptions nvec_monotone_subsequence.
Print Assumptions finite_supporting_normals_tail_reindex.
