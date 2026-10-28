From Coq Require Import Vector VectorSpec ZArith Lia.
From Mell.Core Require Import Vector.

Open Scope Z_scope.

Definition Periodic {d} (set : ZVec d -> Prop) : Prop :=
  set (zvec_zero d) /\
  forall left right, set left -> set right -> set (zvec_add left right).

Fixpoint zvec_nsmul {d} (coefficient : nat) (value : ZVec d) : ZVec d :=
  match coefficient with
  | O => zvec_zero d
  | S coefficient' => zvec_add value (zvec_nsmul coefficient' value)
  end.

Lemma periodic_nsmul : forall d (set : ZVec d -> Prop),
    Periodic set -> forall coefficient value,
    set value -> set (zvec_nsmul coefficient value).
Proof.
  intros d set [Hzero Hadd] coefficient; induction coefficient; intros value Hvalue.
  - exact Hzero.
  - cbn. apply Hadd; [exact Hvalue | apply IHcoefficient; exact Hvalue].
Qed.

Lemma nth_zvec_nsmul : forall d coefficient (value : ZVec d) index,
    Vector.nth (zvec_nsmul coefficient value) index =
      Z.of_nat coefficient * Vector.nth value index.
Proof.
  intros d coefficient; induction coefficient; intros value index.
  - change (Vector.nth (zvec_zero d) index = Z.of_nat 0 * Vector.nth value index).
    unfold zvec_zero.
    rewrite (const_nth Z 0 d index); reflexivity.
  - change (Vector.nth (zvec_add value (zvec_nsmul coefficient value)) index =
      Z.of_nat (S coefficient) * Vector.nth value index).
    unfold zvec_add.
    rewrite (nth_map2 Z.add value (zvec_nsmul coefficient value)
      index index index eq_refl eq_refl), IHcoefficient.
    rewrite Nat2Z.inj_succ; ring.
Qed.
