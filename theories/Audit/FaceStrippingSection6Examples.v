From Coq Require Import Fin Lia List Program.Equality QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Faces FaceDimension FaceStrippingDiagonal
  FaceStrippingExtract FaceStrippingGeometricCore
  FaceStrippingLemma610FiniteBasis FaceStrippingLemma611
  FaceStrippingMinimalFace FaceStrippingSection6 FaceStrippingTheorem
  MathCompBridge QConeCore
  RationalDefinability RationalHToV FaceZeroPatternWitness.
From Mell.Audit Require Import FaceStrippingDiagonalExamples
  FaceStrippingExtractExamples FaceStrippingTheoremExamples.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.

Definition t11d_lower : ZSet 1 :=
  fun value => (1 <= Vector.nth value Fin.F1)%Z.

Definition t11d_upper : ZSet 1 :=
  fun value => (0 <= Vector.nth value Fin.F1)%Z.

Example r08_correct_extract_recovers_zero :
  ExtractFace extract_nat_period extract_nat_zero_face
    t11d_lower t11d_upper (extract_z1 0).
Proof.
  intros increment [_ [_ Horthogonal]].
  specialize (Horthogonal (extract_q1 1) ltac:(now left)).
  unfold qinner, extract_q1, zvec_to_qvec, qrow_apply,
    qvec_to_vector, Qeq in Horthogonal. cbn in Horthogonal.
  assert (Hcoordinate : Vector.nth increment Fin.F1 = 0%Z).
  { destruct (Vector.nth increment Fin.F1) eqn:Hvalue;
      cbn in Horthogonal.
    - reflexivity.
    - discriminate Horthogonal.
    - discriminate Horthogonal. }
  dependent destruction increment.
  dependent destruction increment.
  cbn in Hcoordinate. subst h.
  split.
  - unfold t11d_upper, zvec_add, extract_z1. cbn. lia.
  - unfold t11d_lower, zvec_add, extract_z1. cbn. lia.
Qed.

Example r08_reversed_extract_does_not_recover_zero :
  ~ ExtractFace extract_nat_period extract_nat_zero_face
      t11d_upper t11d_lower (extract_z1 0).
Proof.
  intro Hextract.
  pose proof (face_periodic 1 extract_nat_period extract_nat_zero_face
    (generated_periodic 1 [extract_z1 1])
    extract_nat_zero_face_is_face) as Hface_periodic.
  apply (extract_face_subset_difference 1 extract_nat_period
    t11d_upper t11d_lower extract_nat_zero_face Hface_periodic
    (extract_z1 0)) in Hextract.
  destruct Hextract as [Hlower Hnot_upper]. apply Hnot_upper.
  unfold t11d_upper, extract_z1. cbn. lia.
Qed.

Definition r07_translated_chain (index : nat) : ZVec 1 :=
  extract_z1 (Z.of_nat index - 1).

Definition r07_nat_period : ZSet 1 :=
  fun value => (0 <= Vector.nth value Fin.F1)%Z.

Example r07_chain_origin_need_not_be_in_period :
  ~ r07_nat_period (r07_translated_chain 0).
Proof. unfold r07_nat_period, r07_translated_chain, extract_z1. cbn. lia. Qed.

Example r07_chain_uses_period_differences : forall index,
  PeriodicLe r07_nat_period
    (r07_translated_chain index) (r07_translated_chain (S index)).
Proof.
  intro index. unfold PeriodicLe, r07_nat_period, r07_translated_chain.
  change (0 <= (Z.of_nat (S index) - 1) -
    (Z.of_nat index - 1))%Z. lia.
Qed.

(* R09: the implemented indices are zero-based.  The theorem forbids the
   later-to-earlier direction; this existing concrete trace confirms that
   the converse earlier-to-later edge is intentionally still possible. *)
Check d3e_allowed_earlier_to_later_edge.

Check @face_periodic_finitely_generated.
Check @face_period_full.
Check @face_zero_pattern_witness.
Check @extract_remainder_cylindric.
Check @lemma_6_9_minimal_extract.
Check @corrected_remainder_difference_identity.
Check @maximal_extract_prepared_chain_face_collapse.
Check @lemma_6_10_maximal_extract_finitary.
Check @lemma_6_11_stripping_invariants.
Check @proper_face_dimension_lt.
Check @ordered_stripping_noninitial_face_proper.
Check @ordered_stripping_noninitial_face_dimension_lt.
Check @face_stripping_theorem.
Check @lemma_6_3_stripping_diagonal.
Check @face_stripping_theorem_diagonal.

Print Assumptions face_periodic_finitely_generated.
Print Assumptions face_period_full.
Print Assumptions face_zero_pattern_witness.
Print Assumptions extract_remainder_cylindric.
Print Assumptions lemma_6_9_minimal_extract.
Print Assumptions lemma_6_10_maximal_extract_finitary.
Print Assumptions lemma_6_11_stripping_invariants.
Print Assumptions proper_face_dimension_lt.
Print Assumptions ordered_stripping_noninitial_face_proper.
Print Assumptions ordered_stripping_noninitial_face_dimension_lt.
Print Assumptions face_stripping_theorem.
Print Assumptions lemma_6_3_stripping_diagonal.
Print Assumptions face_stripping_theorem_diagonal.
