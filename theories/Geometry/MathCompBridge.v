From Coq Require Import List Vector VectorSpec ZArith QArith Qring Lia.
From Mell.Core Require Import Vector.

Open Scope Z_scope.
Open Scope Q_scope.

Definition QVec (d : nat) := Fin.t d -> Q.

Definition qvec_eq {d} (left right : QVec d) : Prop :=
  forall index, left index == right index.

Definition qvec_zero (d : nat) : QVec d := fun _ => 0.
Definition qvec_add {d} (left right : QVec d) : QVec d :=
  fun index => left index + right index.
Definition qvec_scale {d} (scalar : Q) (value : QVec d) : QVec d :=
  fun index => scalar * value index.

Definition q_of_nat (value : nat) : Q := inject_Z (Z.of_nat value).

Definition zvec_to_qvec {d} (value : ZVec d) : QVec d :=
  fun index => inject_Z (Vector.nth value index).

Definition nvec_to_qvec {d} (value : NVec d) : QVec d :=
  fun index => q_of_nat (Vector.nth value index).

Lemma qvec_eq_refl : forall d (value : QVec d), qvec_eq value value.
Proof. intros d value index; reflexivity. Qed.

Lemma qvec_eq_sym : forall d (left right : QVec d),
    qvec_eq left right -> qvec_eq right left.
Proof. intros d left right H index; symmetry; apply H. Qed.

Lemma qvec_eq_trans : forall d (x y z : QVec d),
    qvec_eq x y -> qvec_eq y z -> qvec_eq x z.
Proof. intros d x y z Hxy Hyz index; transitivity (y index); auto. Qed.

Lemma nvec_zvec_qvec_commute : forall d (value : NVec d),
    qvec_eq (zvec_to_qvec (nvec_to_zvec value)) (nvec_to_qvec value).
Proof.
  intros d value index. unfold zvec_to_qvec, nvec_to_qvec, nvec_to_zvec.
  rewrite (nth_map Z.of_nat value index index eq_refl); reflexivity.
Qed.

Lemma zvec_to_qvec_add : forall d (left right : ZVec d),
    qvec_eq (zvec_to_qvec (zvec_add left right))
      (qvec_add (zvec_to_qvec left) (zvec_to_qvec right)).
Proof.
  intros d left right index. unfold zvec_to_qvec, zvec_add, qvec_add.
  rewrite (nth_map2 Z.add left right index index index eq_refl eq_refl).
  rewrite inject_Z_plus; reflexivity.
Qed.

Fixpoint zvec_rsum {d} (values : list (ZVec d)) : ZVec d :=
  match values with
  | List.nil => zvec_zero d
  | List.cons value values' => zvec_add value (zvec_rsum values')
  end.

Fixpoint qvec_rsum {d} (values : list (QVec d)) : QVec d :=
  match values with
  | List.nil => qvec_zero d
  | List.cons value values' => qvec_add value (qvec_rsum values')
  end.

Lemma zvec_to_qvec_rsum : forall d (values : list (ZVec d)),
    qvec_eq (zvec_to_qvec (zvec_rsum values))
      (qvec_rsum (List.map zvec_to_qvec values)).
Proof.
  intros d values; induction values as [|value values IH]; intro index.
  - change (inject_Z (Vector.nth (Vector.const 0%Z d) index) == 0).
    rewrite const_nth; reflexivity.
  - unfold zvec_rsum; fold (@zvec_rsum d).
    unfold qvec_rsum; fold (@qvec_rsum d).
    unfold zvec_to_qvec, zvec_add, qvec_add.
    rewrite (nth_map2 Z.add value (zvec_rsum values)
      index index index eq_refl eq_refl), inject_Z_plus.
    apply Qplus_comp; [reflexivity | apply IH].
Qed.

(* Keep the MathComp representation behind this small adapter: the remainder of
   the development uses Coq's standard [Q], while later polyhedral lemmas can
   consume rows over MathComp's exact rational field. *)
From mathcomp Require Import all_ssreflect all_algebra.

Module MathCompRationalAdapter.
  Import GRing.Theory.
  Local Open Scope ring_scope.

  Definition row (d : nat) : Type := 'rV[rat]_d.
  Definition zero (d : nat) : row d := 0.
  Definition add {d : nat} (left right : row d) : row d := left + right.
  Definition scale {d : nat} (coefficient : rat) (value : row d) : row d :=
    coefficient *: value.

  Fixpoint rsum {d : nat} (values : seq (row d)) : row d :=
    if values is value :: values' then add value (rsum values') else zero d.

  Lemma addA : forall d (x y z : row d),
      add x (add y z) = add (add x y) z.
  Proof. by move=> d x y z; rewrite /add addrA. Qed.

  Lemma rsum_cat : forall d (left right : seq (row d)),
      rsum (left ++ right) = add (rsum left) (rsum right).
  Proof.
    move=> d left; elim: left => [|value left IH] right /=.
    - by rewrite /add /zero add0r.
    - by rewrite IH /add addrA.
  Qed.
End MathCompRationalAdapter.
