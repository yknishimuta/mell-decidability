From Coq Require Import List Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Order Require Import PeriodicOrder.
From Mell.Geometry Require Import FaceStrippingExtract RationalDefinability.
From Mell.Geometry Require Import FaceStrippingLemma610.

Check ShiftedSet.
Check shifted_set_qcylindric.
Check shifted_set_finitary_qcylindric.
Check shifted_extract_face.
Check shifted_maximal_nonempty_extract_face.
Check finitely_generated_period_cone_polyhedral.
Check maximal_extract_first_normalization.
Check maximal_extract_monotone_subsequence.

Example shifted_set_zero_identity : forall d (set : ZSet d) value,
    ShiftedSet (zvec_zero d) set value <-> set value.
Proof.
  intros d set value. unfold ShiftedSet.
  now rewrite zvec_add_zero_left.
Qed.

Example shifted_extract_zero_identity : forall d
    (period excluded remaining : ZSet d) (face : QSet d) value,
    ExtractFace period face
      (ShiftedSet (zvec_zero d) excluded)
      (ShiftedSet (zvec_zero d) remaining) value <->
    ExtractFace period face excluded remaining value.
Proof.
  intros. rewrite shifted_extract_face, zvec_add_zero_left. tauto.
Qed.

(* C2-5 remains intentionally absent until the sequence-to-[afs] bridge is
   available without a forbidden countable/dependent choice principle. *)
Fail Check lemma_6_10_maximal_extract_finitary.

Print Assumptions shifted_extract_face.
Print Assumptions shifted_maximal_nonempty_extract_face.
Print Assumptions finitely_generated_period_cone_polyhedral.
Print Assumptions maximal_extract_first_normalization.
Print Assumptions maximal_extract_monotone_subsequence.
