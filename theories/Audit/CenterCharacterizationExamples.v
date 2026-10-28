From Coq Require Import List Lia QArith Qring Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Center CenterCharacterization ClosedLinearization
  LatticeGordanH MathCompBridge Periodic RationalSpan.
From Mell.Order Require Import PeriodicOrder.
From Mell.Audit Require Import CenterExamples.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.
Set Printing Implicit.

Check @PositiveSpanningCombination.
Check @center_implies_positive_spanning.
Check @positive_spanning_implies_center.
Check @center_characterization.

Definition characterization_all_Z (_ : ZVec 1) : Prop := True.

Lemma characterization_all_Z_periodic : Periodic characterization_all_Z.
Proof. split; [exact I|intros; exact I]. Qed.

Definition characterization_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Lemma pair_spans_all_q1 : forall point : QVec 1,
    QSpan [characterization_z1 1; characterization_z1 (-1)] point.
Proof.
  intro point.
  exists (@Vector.cons Q (point Fin.F1) 1
    (@Vector.cons Q 0 0 (@Vector.nil Q))).
  intro index. refine (Fin.caseS' index (fun index => _) _ _).
  - change (point Fin.F1 ==
      point Fin.F1 * inject_Z 1 + (0 * inject_Z (-1) + 0)). ring.
  - intro tail_index. exact (Fin.case0 (fun index =>
      point (Fin.FS index) ==
      qgroup_combination
        [characterization_z1 1; characterization_z1 (-1)]
        (@Vector.cons Q (point Fin.F1) 1
          (@Vector.cons Q 0 0 (@Vector.nil Q))) (Fin.FS index)) tail_index).
Qed.

Lemma duplicate_spans_all_q1 : forall point : QVec 1,
    QSpan [characterization_z1 1; characterization_z1 1] point.
Proof.
  intro point.
  exists (@Vector.cons Q (point Fin.F1) 1
    (@Vector.cons Q 0 0 (@Vector.nil Q))).
  intro index. refine (Fin.caseS' index (fun index => _) _ _).
  - change (point Fin.F1 ==
      point Fin.F1 * inject_Z 1 + (0 * inject_Z 1 + 0)). ring.
  - intro tail_index. exact (Fin.case0 (fun index =>
      point (Fin.FS index) ==
      qgroup_combination
        [characterization_z1 1; characterization_z1 1]
        (@Vector.cons Q (point Fin.F1) 1
          (@Vector.cons Q 0 0 (@Vector.nil Q))) (Fin.FS index)) tail_index).
Qed.

Lemma all_z_pair_span_spec : forall point : QVec 1,
    VecOf characterization_all_Z point <->
    QSpan [characterization_z1 1; characterization_z1 (-1)] point.
Proof.
  intro point. split; intro.
  - apply pair_spans_all_q1.
  - exists [characterization_z1 1; characterization_z1 (-1)].
    split; [repeat constructor; exact I|assumption].
Qed.

Lemma all_z_duplicate_span_spec : forall point : QVec 1,
    VecOf characterization_all_Z point <->
    QSpan [characterization_z1 1; characterization_z1 1] point.
Proof.
  intro point. split; intro.
  - apply duplicate_spans_all_q1.
  - exists [characterization_z1 1; characterization_z1 1].
    split; [repeat constructor; exact I|assumption].
Qed.

Example all_Z_zero_positive_dependent :
    PositiveSpanningCombination characterization_all_Z
      (characterization_z1 0).
Proof.
  exists [characterization_z1 1; characterization_z1 (-1)].
  split; [repeat constructor; exact I|]. split.
  - apply all_z_pair_span_spec.
  - exists (@Vector.cons Q 1 1
      (@Vector.cons Q 1 0 (@Vector.nil Q))). split.
    + repeat constructor; unfold Qlt; cbn; lia.
    + intro index. refine (Fin.caseS' index (fun index => _) _ _).
      * change (inject_Z 0 ==
          1 * inject_Z 1 + (1 * inject_Z (-1) + 0)). ring.
      * intro tail_index. exact (Fin.case0 (fun index =>
          zvec_to_qvec (characterization_z1 0) (Fin.FS index) ==
          qgroup_combination
            [characterization_z1 1; characterization_z1 (-1)]
            (@Vector.cons Q 1 1
              (@Vector.cons Q 1 0 (@Vector.nil Q)))
            (Fin.FS index)) tail_index).
Qed.

Example duplicate_half_coefficients_need_denominator_clearing :
    PositiveSpanningCombination characterization_all_Z
      (characterization_z1 1).
Proof.
  exists [characterization_z1 1; characterization_z1 1].
  split; [repeat constructor; exact I|]. split.
  - apply all_z_duplicate_span_spec.
  - exists (@Vector.cons Q (1#2) 1
      (@Vector.cons Q (1#2) 0 (@Vector.nil Q))). split.
    + repeat constructor; unfold Qlt; cbn; lia.
    + intro index. refine (Fin.caseS' index (fun index => _) _ _).
      * change (inject_Z 1 ==
          (1#2) * inject_Z 1 + ((1#2) * inject_Z 1 + 0)). reflexivity.
      * intro tail_index. exact (Fin.case0 (fun index =>
          zvec_to_qvec (characterization_z1 1) (Fin.FS index) ==
          qgroup_combination
            [characterization_z1 1; characterization_z1 1]
            (@Vector.cons Q (1#2) 1
              (@Vector.cons Q (1#2) 0 (@Vector.nil Q)))
            (Fin.FS index)) tail_index).
Qed.

Example zero_coefficient_is_rejected :
    ~ Vector.Forall (fun coefficient : Q => 0 < coefficient)
      (@Vector.cons Q 0 0 (@Vector.nil Q)).
Proof.
  intro H.
  pose proof (vector_forall_nth Q (fun coefficient : Q => 0 < coefficient)
    1 _ H Fin.F1) as Hzero.
  exact (Qlt_irrefl 0 Hzero).
Qed.

Definition characterization_zero0 (_ : ZVec 0) : Prop := True.

Lemma characterization_zero0_periodic : Periodic characterization_zero0.
Proof. split; [exact I|intros; exact I]. Qed.

Example empty_spanning_list_dimension_zero :
    PositiveSpanningCombination characterization_zero0 (zvec_zero 0).
Proof.
  exists []. split; [constructor|]. split.
  - intro point. split; intro.
    + apply (proj2 (qspan_nil_iff 0 point)).
      intro index. exact (Fin.case0 (fun i => point i == qvec_zero 0 i) index).
    + exists []. split; [constructor|assumption].
  - exists (@Vector.nil Q). split; [constructor|].
    intro index. exact (Fin.case0 (fun i =>
      zvec_to_qvec (zvec_zero 0) i ==
      qgroup_combination [] (@Vector.nil Q) i) index).
Qed.

Example characterization_dimension_zero :
    Center characterization_zero0 (zvec_zero 0) <->
      Difference characterization_zero0 (zvec_zero 0) /\
      PositiveSpanningCombination characterization_zero0 (zvec_zero 0).
Proof. apply center_characterization, characterization_zero0_periodic. Qed.

Example characterization_zero_monoid :
    Center (@center_zero_set 1) (zvec_zero 1) <->
      Difference (@center_zero_set 1) (zvec_zero 1) /\
      PositiveSpanningCombination (@center_zero_set 1) (zvec_zero 1).
Proof. apply center_characterization, center_zero_set_periodic. Qed.

Example characterization_twoN :
    Center center_twoN (center_z1 2) <->
      Difference center_twoN (center_z1 2) /\
      PositiveSpanningCombination center_twoN (center_z1 2).
Proof. apply center_characterization, center_twoN_periodic. Qed.

Example characterization_gap_one :
    Difference center_gap (center_z1 1) /\
    PositiveSpanningCombination center_gap (center_z1 1).
Proof.
  apply (proj1 (center_characterization 1 center_gap (center_z1 1)
    center_gap_periodic)).
  apply center_gap_one_is_central.
Qed.

Example characterization_low_rank :
    Center (zvec_generated [characterization_z1 2]) (characterization_z1 2) <->
      Difference (zvec_generated [characterization_z1 2])
        (characterization_z1 2) /\
      PositiveSpanningCombination (zvec_generated [characterization_z1 2])
        (characterization_z1 2).
Proof. apply center_characterization, generated_periodic. Qed.

Print Assumptions center_implies_positive_spanning.
Print Assumptions positive_spanning_implies_center.
Print Assumptions center_characterization.
