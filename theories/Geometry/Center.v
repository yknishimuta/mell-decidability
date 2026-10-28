From Coq Require Import Lia Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Periodic.
From Mell.Order Require Import PeriodicOrder.

Open Scope Z_scope.

Definition Center {d} (set : ZSet d) : ZSet d :=
  fun value =>
    forall offset, Difference set offset ->
      exists radius : nat, forall n : nat,
        set (zvec_add offset
          (zvec_nsmul (radius + n)%nat value)).

Lemma zvec_nsmul_succ_sub : forall d radius (value : ZVec d),
    zvec_sub (zvec_nsmul (S radius) value)
      (zvec_nsmul radius value) = value.
Proof.
  intros d radius value. apply zvec_ext. intro index.
  unfold zvec_sub.
  rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl).
  repeat rewrite nth_zvec_nsmul. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma zvec_nsmul_add_vectors : forall d coefficient
    (left right : ZVec d),
    zvec_nsmul coefficient (zvec_add left right) =
      zvec_add (zvec_nsmul coefficient left)
        (zvec_nsmul coefficient right).
Proof.
  intros d coefficient left right. apply zvec_ext. intro index.
  rewrite nth_zvec_nsmul. unfold zvec_add.
  repeat rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl).
  repeat rewrite nth_zvec_nsmul. ring.
Qed.

Theorem center_in_difference : forall d (set : ZSet d) value,
    Periodic set -> Center set value -> Difference set value.
Proof.
  intros d set value Hperiodic Hcenter.
  destruct (Hcenter (zvec_zero d) (difference_zero d set Hperiodic))
    as [radius Htail].
  exists (zvec_nsmul (S radius) value),
    (zvec_nsmul radius value). repeat split.
  - replace (zvec_nsmul (S radius) value) with
      (zvec_add (zvec_zero d)
        (zvec_nsmul (radius + 1)%nat value)).
    + apply Htail.
    + rewrite zvec_add_zero_left. f_equal. lia.
  - replace (zvec_nsmul radius value) with
      (zvec_add (zvec_zero d)
        (zvec_nsmul (radius + 0)%nat value)).
    + apply Htail.
    + rewrite zvec_add_zero_left. f_equal. lia.
  - symmetry. apply zvec_nsmul_succ_sub.
Qed.

Theorem center_add : forall d (set : ZSet d) left right,
    Periodic set ->
    Center set left -> Center set right ->
    Center set (zvec_add left right).
Proof.
  intros d set left right Hperiodic Hleft Hright offset Hoffset.
  destruct Hperiodic as [Hzero Hadd].
  destruct (Hleft offset Hoffset) as [left_radius Hleft_tail].
  destruct (Hright (zvec_zero d)
    (difference_zero d set (conj Hzero Hadd)))
    as [right_radius Hright_tail].
  exists (left_radius + right_radius)%nat. intro n.
  specialize (Hleft_tail (right_radius + n)%nat).
  specialize (Hright_tail (left_radius + n)%nat).
  apply Hadd with
    (left := zvec_add offset
      (zvec_nsmul (left_radius + (right_radius + n))%nat left))
    (right := zvec_add (zvec_zero d)
      (zvec_nsmul (right_radius + (left_radius + n))%nat right))
    in Hleft_tail; [|exact Hright_tail].
  replace (left_radius + (right_radius + n))%nat with
    (left_radius + right_radius + n)%nat in Hleft_tail by lia.
  replace (right_radius + (left_radius + n))%nat with
    (left_radius + right_radius + n)%nat in Hleft_tail by lia.
  rewrite zvec_add_zero_left in Hleft_tail.
  rewrite zvec_add_assoc in Hleft_tail.
  rewrite <- zvec_nsmul_add_vectors in Hleft_tail.
  exact Hleft_tail.
Qed.
