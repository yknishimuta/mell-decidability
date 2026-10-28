From Coq Require Import Fin Lia List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Center CenterAbsorption CenterPushIn
  ClosedLinearization Cone Periodic RationalClosure RationalSpan.
From Mell.Order Require Import PeriodicOrder.
From Mell.Audit Require Import CenterExamples CenterAbsorptionExamples.

Import ListNotations.
Open Scope Z_scope.
Set Printing Implicit.

Check @center_anchor.
Check @closed_linearization_push_in_offset.
Check @closed_linearization_push_in.

Example push_in_dimension_zero :
    exists anchor : ZVec 0,
      (@center_zero_set 0) anchor /\ Center (@center_zero_set 0) anchor.
Proof. apply center_anchor, center_zero_set_periodic. Qed.

Example push_in_twoN_anchor :
    exists anchor : ZVec 1,
      center_twoN anchor /\ Center center_twoN anchor.
Proof. apply center_anchor, center_twoN_periodic. Qed.

Lemma center_zero_set_nonnegative : forall d,
    ClosedLinearizationL2.NonnegativeSet (@center_zero_set d).
Proof.
  intros d value -> index. unfold zvec_zero. rewrite const_nth. lia.
Qed.

Lemma center_twoN_nonnegative :
    ClosedLinearizationL2.NonnegativeSet center_twoN.
Proof.
  intros value [coefficient Hvalue] index.
  refine (Fin.caseS' index
    (fun index => (0 <= Vector.nth value index)%Z) _ _).
  - rewrite Hvalue. pose proof (Zle_0_nat coefficient). lia.
  - intro tail_index. exact (Fin.case0
      (fun index => (0 <= Vector.nth value (Fin.FS index))%Z)
      tail_index).
Qed.

Lemma absorption_n2_nonnegative :
    ClosedLinearizationL2.NonnegativeSet absorption_n2.
Proof.
  intros value [Hfirst Hsecond] index.
  refine (Fin.caseS' index
    (fun index => (0 <= Vector.nth value index)%Z) Hfirst _).
  intro tail_index.
  refine (Fin.caseS' tail_index
    (fun index => (0 <= Vector.nth value (Fin.FS index))%Z) Hsecond _).
  intro empty_index. exact (Fin.case0
    (fun index => (0 <= Vector.nth value (Fin.FS (Fin.FS index)))%Z)
    empty_index).
Qed.

Example push_in_zero_monoid_original_translation :
    exists anchor : ZVec 1,
      center_zero_set anchor /\
      forall offset point : ZVec 1,
        Difference center_zero_set offset ->
        ClosedLinearization center_zero_set (zvec_sub point anchor) ->
        exists radius : nat, forall n : nat,
          center_zero_set
            (zvec_add offset (zvec_nsmul (radius + n)%nat point)).
Proof.
  apply closed_linearization_push_in.
  - apply center_zero_set_periodic.
  - apply center_zero_set_nonnegative.
Qed.

Example push_in_twoN_original_translation :
    exists anchor : ZVec 1,
      center_twoN anchor /\
      forall offset point : ZVec 1,
        Difference center_twoN offset ->
        ClosedLinearization center_twoN (zvec_sub point anchor) ->
        exists radius : nat, forall n : nat,
          center_twoN
            (zvec_add offset (zvec_nsmul (radius + n)%nat point)).
Proof.
  apply closed_linearization_push_in.
  - apply center_twoN_periodic.
  - apply center_twoN_nonnegative.
Qed.

Example push_in_nonnegative_quadrant :
    exists anchor : ZVec 2,
      absorption_n2 anchor /\
      forall offset point : ZVec 2,
        Difference absorption_n2 offset ->
        ClosedLinearization absorption_n2 (zvec_sub point anchor) ->
        exists radius : nat, forall n : nat,
          absorption_n2
            (zvec_add offset (zvec_nsmul (radius + n)%nat point)).
Proof.
  apply closed_linearization_push_in.
  - apply absorption_n2_periodic.
  - apply absorption_n2_nonnegative.
Qed.

Example push_in_all_integers_signed :
    exists anchor : ZVec 1,
      absorption_all_z anchor /\
      forall offset q : ZVec 1,
        Difference absorption_all_z offset ->
        ClosedLinearization absorption_all_z q ->
        exists radius : nat, forall n : nat,
          absorption_all_z
            (zvec_add offset
              (zvec_nsmul (radius + n)%nat (zvec_add anchor q))).
Proof. apply closed_linearization_push_in_offset, absorption_all_z_periodic. Qed.

Example push_in_low_rank_signed :
    exists anchor : ZVec 1,
      zvec_generated [center_z1 2] anchor /\
      forall offset q : ZVec 1,
        Difference (zvec_generated [center_z1 2]) offset ->
        ClosedLinearization (zvec_generated [center_z1 2]) q ->
        exists radius : nat, forall n : nat,
          zvec_generated [center_z1 2]
            (zvec_add offset
              (zvec_nsmul (radius + n)%nat (zvec_add anchor q))).
Proof. apply closed_linearization_push_in_offset, generated_periodic. Qed.

Lemma center_twoN_two_closed_linearization :
    ClosedLinearization center_twoN (center_z1 2).
Proof.
  split.
  - apply periodic_member_in_difference.
    + apply center_twoN_periodic.
    + exists 1%nat. reflexivity.
  - apply qclosure_extensive, cone_contains_source.
    exists 1%nat. reflexivity.
Qed.

Example fixed_anchor_handles_negative_offset_and_distinct_q :
    exists anchor : ZVec 1,
      center_twoN anchor /\
      (exists radius : nat, forall n : nat,
        center_twoN
          (zvec_add (center_z1 (-2))
            (zvec_nsmul (radius + n)%nat
              (zvec_add anchor (zvec_zero 1))))) /\
      (exists radius : nat, forall n : nat,
        center_twoN
          (zvec_add (zvec_zero 1)
            (zvec_nsmul (radius + n)%nat
              (zvec_add anchor (center_z1 2))))).
Proof.
  destruct (closed_linearization_push_in_offset 1 center_twoN
    center_twoN_periodic) as [anchor [Hanchor Htail]].
  exists anchor. split; [exact Hanchor|]. split.
  - apply Htail.
    + apply center_twoN_minus_two_in_difference.
    + apply closed_linearization_zero, center_twoN_periodic.
  - apply Htail.
    + apply difference_zero, center_twoN_periodic.
    + apply center_twoN_two_closed_linearization.
Qed.

Example push_in_gap_q_zero :
    exists anchor : ZVec 1,
      center_gap anchor /\
      forall offset q : ZVec 1,
        Difference center_gap offset ->
        ClosedLinearization center_gap q ->
        exists radius : nat, forall n : nat,
          center_gap
            (zvec_add offset
              (zvec_nsmul (radius + n)%nat (zvec_add anchor q))).
Proof.
  apply closed_linearization_push_in_offset, center_gap_periodic.
Qed.

Example push_in_gap_original_translation :
    exists anchor : ZVec 1,
      center_gap anchor /\
      forall offset point : ZVec 1,
        Difference center_gap offset ->
        ClosedLinearization center_gap (zvec_sub point anchor) ->
        exists radius : nat, forall n : nat,
          center_gap
            (zvec_add offset (zvec_nsmul (radius + n)%nat point)).
Proof.
  apply closed_linearization_push_in.
  - apply center_gap_periodic.
  - intros value Hvalue index.
    refine (Fin.caseS' index
      (fun index => (0 <= Vector.nth value index)%Z) _ _).
    + unfold center_gap in Hvalue. destruct Hvalue; lia.
    + intro tail_index. exact (Fin.case0
        (fun index => (0 <= Vector.nth value (Fin.FS index))%Z)
        tail_index).
Qed.

Print Assumptions center_anchor.
Print Assumptions closed_linearization_push_in_offset.
Print Assumptions closed_linearization_push_in.
