From Coq Require Import Arith Vector.
From KruskalTrees Require Import idx vec.
From KruskalAfProp Require Import af.af af.af_tools.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.

Import idx_notations.

Lemma vec_fall2_nvec_le : forall d (left right : NVec d),
    vec_fall2 Nat.le left right -> nvec_le left right.
Proof.
  intros d left right H.
  induction H using vec_fall2_rect.
  - intro index. inversion index.
  - intro index.
    refine (Fin.caseS' index
      (fun i => Vector.nth (@Vector.cons nat x n v) i <=
        Vector.nth (@Vector.cons nat y n w) i) H _).
    intro tail_index. exact (IHvec_fall2 tail_index).
Qed.

Theorem nvec_le_almost_full : forall d, af (@nvec_le d).
Proof.
  intro d. eapply af_mono with
    (R := @vec_fall2 nat nat Nat.le d).
  - intros left right H. exact (vec_fall2_nvec_le d left right H).
  - apply af_vec_fall2. apply af_le_nat.
Qed.
