From Coq Require Import QArith ZArith Lia.
From mathcomp Require Import all_ssreflect all_algebra.

Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.

Definition z_to_int (value : BinNums.Z) : int :=
  match value with
  | BinNums.Z0 => Posz 0
  | BinNums.Zpos p => Posz (Pos.to_nat p)
  | BinNums.Zneg p => Negz (Nat.pred (Pos.to_nat p))
  end.

Definition int_to_z (value : int) : BinNums.Z :=
  match value with
  | Posz n => Z.of_nat n
  | Negz n => Z.opp (Z.of_nat (S n))
  end.

Lemma int_to_z_to_int : forall value, int_to_z (z_to_int value) = value.
Proof.
  intros [|p|p]; cbn; first reflexivity.
  - now rewrite positive_nat_Z.
  - f_equal. apply SuccNat2Pos.inv.
    symmetry. apply Nat.succ_pred_pos, Pos2Nat.is_pos.
Qed.

Lemma z_to_int_to_z : forall value, z_to_int (int_to_z value) = value.
Proof.
  intros [n|n]; cbn.
  - destruct n; cbn; [reflexivity|]. now rewrite SuccNat2Pos.id_succ.
  - now rewrite SuccNat2Pos.id_succ.
Qed.

Lemma int_to_z_injective : forall left right,
    int_to_z left = int_to_z right -> left = right.
Proof.
  intros left right Heq. rewrite <- (z_to_int_to_z left),
    <- (z_to_int_to_z right). now rewrite Heq.
Qed.

Lemma z_to_int_injective : forall left right,
    z_to_int left = z_to_int right -> left = right.
Proof.
  intros left right Heq. rewrite <- (int_to_z_to_int left),
    <- (int_to_z_to_int right). now rewrite Heq.
Qed.

Lemma int_to_z_opp : forall value,
    int_to_z (- value)%R = Z.opp (int_to_z value).
Proof.
  intros [[|value]|value]; reflexivity.
Qed.

Lemma z_to_int_opp : forall value,
    z_to_int (Z.opp value) = (- z_to_int value)%R.
Proof.
  intro value. apply int_to_z_injective.
  rewrite int_to_z_to_int. rewrite int_to_z_opp.
  rewrite int_to_z_to_int. reflexivity.
Qed.

Lemma int_to_z_add : forall left right,
    int_to_z (left + right)%R = Z.add (int_to_z left) (int_to_z right).
Proof.
  intros [left|left] [right|right].
  - cbn. now rewrite Nat2Z.inj_add.
  - change (
      int_to_z
        (if (ltn right left)
         then Posz (left - right.+1)%N
         else Negz (right - left)%N) =
        Z.sub (Z.of_nat left) (Z.of_nat right.+1)).
    destruct (ltn right left) eqn:Horder.
    + unfold int_to_z. move/ltP: Horder => Horder.
      change (Z.of_nat (left - right.+1)%coq_nat =
        Z.sub (Z.of_nat left) (Z.of_nat right.+1)).
      rewrite Nat2Z.inj_sub; lia.
    + unfold int_to_z.
      have Hle : (left <= right)%coq_nat.
        apply/leP. rewrite leqNgt. change (~~ ltn right left).
        rewrite Horder. reflexivity.
      change (Z.opp (Z.of_nat (right - left).+1) =
        Z.sub (Z.of_nat left) (Z.of_nat right.+1)).
      rewrite Nat2Z.inj_succ Nat2Z.inj_sub; lia.
  - change (
      int_to_z
        (if (ltn left right)
         then Posz (right - left.+1)%N
         else Negz (left - right)%N) =
        Z.add (Z.opp (Z.of_nat left.+1)) (Z.of_nat right)).
    destruct (ltn left right) eqn:Horder.
    + unfold int_to_z. move/ltP: Horder => Horder.
      rewrite Nat2Z.inj_sub; [ring|lia].
    + unfold int_to_z.
      have Hle : (right <= left)%coq_nat.
        apply/leP. rewrite leqNgt. change (~~ ltn left right).
        rewrite Horder. reflexivity.
      rewrite !Nat2Z.inj_succ.
      rewrite Nat2Z.inj_sub; last exact Hle.
      unfold Z.succ.
      ring.
  - cbn.
    change (Z.opp (Z.of_nat (left + right).+2) =
      Z.add (Z.opp (Z.of_nat left.+1)) (Z.opp (Z.of_nat right.+1))).
    rewrite !Nat2Z.inj_succ Nat2Z.inj_add. ring.
Qed.

Lemma z_to_int_zero : z_to_int Z.zero = (0 : int).
Proof. reflexivity. Qed.

Lemma z_to_int_one : z_to_int Z.one = (1 : int).
Proof. reflexivity. Qed.

Lemma z_to_int_add : forall left right,
    z_to_int (Z.add left right) = (z_to_int left + z_to_int right)%R.
Proof.
  intros left right. apply int_to_z_injective.
  rewrite int_to_z_to_int int_to_z_add !int_to_z_to_int. reflexivity.
Qed.

Lemma z_to_int_sub : forall left right,
    z_to_int (Z.sub left right) = (z_to_int left - z_to_int right)%R.
Proof.
  intros left right. unfold Z.sub. rewrite z_to_int_add z_to_int_opp.
  reflexivity.
Qed.

Lemma int_to_z_le_iff : forall left right,
    Z.le (int_to_z left) (int_to_z right) <->
      is_true ((left <= right)%R).
Proof.
  intros [left|left] [right|right]; cbn.
  - split; intro Horder; [apply/leP|move/leP: Horder]; lia.
  - split; intro Horder; [lia|discriminate].
  - split; intro Horder; [reflexivity|lia].
  - split; intro Horder; [apply/leP|move/leP: Horder]; lia.
Qed.

Lemma int_to_z_lt_iff : forall left right,
    Z.lt (int_to_z left) (int_to_z right) <->
      is_true ((left < right)%R).
Proof.
  intros [left|left] [right|right]; cbn.
  - split; intro Horder; [apply/ltP|move/ltP: Horder]; lia.
  - split; intro Horder; [lia|discriminate].
  - split; intro Horder; [reflexivity|lia].
  - split; intro Horder; [apply/ltP|move/ltP: Horder]; lia.
Qed.

Lemma z_to_int_le_iff : forall left right,
    Z.le left right <-> is_true ((z_to_int left <= z_to_int right)%R).
Proof.
  intros left right.
  have Horder := int_to_z_le_iff (z_to_int left) (z_to_int right).
  now rewrite !int_to_z_to_int in Horder.
Qed.

Lemma z_to_int_lt_iff : forall left right,
    Z.lt left right <-> is_true ((z_to_int left < z_to_int right)%R).
Proof.
  intros left right.
  have Horder := int_to_z_lt_iff (z_to_int left) (z_to_int right).
  now rewrite !int_to_z_to_int in Horder.
Qed.

Lemma z_to_int_nonnegative_iff : forall value,
    Z.le Z.zero value <-> is_true (((0 : int) <= z_to_int value)%R).
Proof. intro value. apply z_to_int_le_iff. Qed.

Lemma z_to_int_positive_iff : forall value,
    Z.lt Z.zero value <-> is_true (((0 : int) < z_to_int value)%R).
Proof. intro value. apply z_to_int_lt_iff. Qed.

Lemma int_to_z_mul : forall left right,
    int_to_z (left * right)%R = Z.mul (int_to_z left) (int_to_z right).
Proof.
  intros [left|left] [right|right].
  - cbn. now rewrite Nat2Z.inj_mul.
  - rewrite NegzE. rewrite mulrN. rewrite int_to_z_opp.
    rewrite <- PoszM. cbn.
    destruct left; cbn; [ring|].
    f_equal. apply Pos2Nat.inj.
    rewrite SuccNat2Pos.id_succ. rewrite Pos2Nat.inj_mul.
    rewrite !SuccNat2Pos.id_succ.
    change (S (Nat.add right (Nat.mul left (S right))) =
      Nat.mul (S left) (S right)).
    rewrite Nat.mul_succ_l. lia.
  - rewrite NegzE. rewrite mulNr. rewrite int_to_z_opp.
    rewrite <- PoszM. cbn.
    destruct right; [rewrite <- mulnE; rewrite muln0; reflexivity|]. cbn.
    f_equal. apply Pos2Nat.inj.
    rewrite SuccNat2Pos.id_succ. rewrite Pos2Nat.inj_mul.
    rewrite !SuccNat2Pos.id_succ.
    change (S (Nat.add right (Nat.mul left (S right))) =
      Nat.mul (S left) (S right)).
    rewrite Nat.mul_succ_l. lia.
  - rewrite !NegzE. rewrite mulrNN.
    rewrite <- PoszM. cbn.
    f_equal. apply Pos2Nat.inj.
    rewrite SuccNat2Pos.id_succ. rewrite Pos2Nat.inj_mul.
    rewrite !SuccNat2Pos.id_succ.
    change (S (Nat.add right (Nat.mul left (S right))) =
      Nat.mul (S left) (S right)).
    rewrite Nat.mul_succ_l. lia.
Qed.

Lemma z_to_int_mul : forall left right,
    z_to_int (Z.mul left right) = (z_to_int left * z_to_int right)%R.
Proof.
  intros left right. apply int_to_z_injective.
  rewrite int_to_z_to_int. rewrite int_to_z_mul.
  rewrite !int_to_z_to_int. reflexivity.
Qed.

Definition positive_to_int (value : positive) : int :=
  Posz (Pos.to_nat value).

Definition positive_of_positive_int (value : int) : positive :=
  match value with
  | Posz n => Pos.of_nat n
  | Negz _ => 1%positive
  end.

Definition q_to_rat (value : Q) : rat :=
  fracq (z_to_int (Qnum value), positive_to_int (Qden value)).

Definition rat_to_q (value : rat) : Q :=
  Qmake (int_to_z (numq value)) (positive_of_positive_int (denq value)).

Lemma positive_to_int_nonzero : forall value,
    positive_to_int value != (0 : int).
Proof.
  intro value. apply/eqP. intro Heq.
  unfold positive_to_int in Heq.
  inversion Heq. pose proof (Pos2Nat.is_pos value). lia.
Qed.

Theorem q_to_rat_eq_iff : forall left right : Q,
    (q_to_rat left = q_to_rat right <-> Qeq left right).
Proof.
  intros [left_num left_den] [right_num right_den].
  unfold q_to_rat. cbn. split; intro Heq.
  - have Heqb :
      fracq (z_to_int left_num, positive_to_int left_den) ==
      fracq (z_to_int right_num, positive_to_int right_den) by
        apply/eqP.
    rewrite fracq_eq in Heqb;
      try apply positive_to_int_nonzero.
    move/eqP: Heqb => Heqcross.
    change (z_to_int left_num * z_to_int (Z.pos right_den) =
      z_to_int right_num * z_to_int (Z.pos left_den))%R in Heqcross.
    rewrite <- !z_to_int_mul in Heqcross.
    apply z_to_int_injective in Heqcross. exact Heqcross.
  - apply/eqP. rewrite fracq_eq;
      try apply positive_to_int_nonzero.
    apply/eqP.
    change (z_to_int left_num * z_to_int (Z.pos right_den) =
      z_to_int right_num * z_to_int (Z.pos left_den))%R.
    rewrite <- !z_to_int_mul. f_equal. exact Heq.
Qed.

Lemma rat_denominator_positive_shape : forall value,
    exists n, denq value = Posz (S n).
Proof.
  intro value. destruct (denq value) as [n|n] eqn:Hden.
  - destruct n as [|n].
    + move: (denq_gt0 value). by rewrite Hden.
    + now exists n.
  - move: (denq_gt0 value). by rewrite Hden.
Qed.

Theorem rat_to_q_to_rat : forall value : rat,
    q_to_rat (rat_to_q value) = value.
Proof.
  intro value.
  destruct (rat_denominator_positive_shape value) as [n Hden].
  unfold q_to_rat, rat_to_q, positive_of_positive_int.
  rewrite Hden. cbn.
  rewrite z_to_int_to_z.
  transitivity (fracq (valq value)); [|apply valqK].
  apply f_equal. rewrite (surjective_pairing (valq value)).
  apply (proj2 (pair_equal_spec _ _ _ _)).
  split; [reflexivity|].
  unfold denq in Hden.
  rewrite Hden. destruct n; [reflexivity|].
  unfold positive_to_int.
  rewrite Pos2Nat.inj_succ.
  rewrite Nat2Pos.id; [reflexivity|lia].
Qed.

Theorem q_to_rat_to_q : forall value : Q,
    Qeq (rat_to_q (q_to_rat value)) value.
Proof.
  intro value.
  apply (proj1 (q_to_rat_eq_iff _ _)).
  apply rat_to_q_to_rat.
Qed.

Lemma positive_to_int_mul : forall left right,
    positive_to_int (Pos.mul left right) =
      (positive_to_int left * positive_to_int right)%R.
Proof.
  intros left right.
  change (z_to_int (Z.mul (Z.pos left) (Z.pos right)) =
    (z_to_int (Z.pos left) * z_to_int (Z.pos right))%R).
  apply z_to_int_mul.
Qed.

Lemma q_to_rat_zero : q_to_rat 0 = (0 : rat).
Proof. reflexivity. Qed.

Lemma q_to_rat_one : q_to_rat 1 = (1 : rat).
Proof. reflexivity. Qed.

Lemma q_to_rat_opp : forall value : Q,
    q_to_rat (Qopp value) = (- q_to_rat value)%R.
Proof.
  intros [num den].
  unfold q_to_rat, Qopp. cbn.
  rewrite oppq_frac. unfold oppq_subdef.
  rewrite z_to_int_opp. reflexivity.
Qed.

Lemma q_to_rat_add : forall left right : Q,
    q_to_rat (Qplus left right) =
      (q_to_rat left + q_to_rat right)%R.
Proof.
  intros [left_num left_den] [right_num right_den].
  unfold q_to_rat, Qplus. cbn.
  rewrite addq_frac; try apply positive_to_int_nonzero.
  rewrite addq_subdefE.
  rewrite z_to_int_add !z_to_int_mul positive_to_int_mul.
  reflexivity.
Qed.

Lemma q_to_rat_sub : forall left right : Q,
    q_to_rat (Qminus left right) =
      (q_to_rat left - q_to_rat right)%R.
Proof.
  intros left right. unfold Qminus.
  rewrite q_to_rat_add q_to_rat_opp. reflexivity.
Qed.

Lemma q_to_rat_mul : forall left right : Q,
    q_to_rat (Qmult left right) =
      (q_to_rat left * q_to_rat right)%R.
Proof.
  intros [left_num left_den] [right_num right_den].
  unfold q_to_rat, Qmult. cbn.
  rewrite mulq_frac; try apply positive_to_int_nonzero.
  rewrite mulq_subdefE.
  rewrite !z_to_int_mul positive_to_int_mul.
  reflexivity.
Qed.

Lemma q_to_rat_inv : forall value : Q,
    q_to_rat (Qinv value) = (q_to_rat value)^-1%R.
Proof.
  intros [[|num|num] den].
  - change (q_to_rat 0 = (q_to_rat (Qmake Z0 den))^-1)%R.
    rewrite q_to_rat_zero.
    have Hrat_zero : q_to_rat (Qmake Z0 den) = (0 : rat).
      rewrite <- q_to_rat_zero.
      apply (proj2 (q_to_rat_eq_iff _ _)). reflexivity.
    rewrite Hrat_zero invr0. reflexivity.
  - have Hnonzero : ~ Qeq (Qmake (Z.pos num) den) 0 by discriminate.
    have Hrat_nonzero :
        q_to_rat (Qmake (Z.pos num) den) != (0 : rat).
      apply/eqP. intro Hrat_zero.
      apply Hnonzero.
      apply (proj1 (q_to_rat_eq_iff _ _)).
      rewrite q_to_rat_zero. exact Hrat_zero.
    apply (mulfI Hrat_nonzero).
    rewrite <- q_to_rat_mul.
    transitivity (1 : rat).
    + rewrite <- q_to_rat_one.
      apply (proj2 (q_to_rat_eq_iff _ _)).
      apply Qmult_inv_r. exact Hnonzero.
    + rewrite mulrV //.
  - have Hnonzero : ~ Qeq (Qmake (Z.neg num) den) 0 by discriminate.
    have Hrat_nonzero :
        q_to_rat (Qmake (Z.neg num) den) != (0 : rat).
      apply/eqP. intro Hrat_zero.
      apply Hnonzero.
      apply (proj1 (q_to_rat_eq_iff _ _)).
      rewrite q_to_rat_zero. exact Hrat_zero.
    apply (mulfI Hrat_nonzero).
    rewrite <- q_to_rat_mul.
    transitivity (1 : rat).
    + rewrite <- q_to_rat_one.
      apply (proj2 (q_to_rat_eq_iff _ _)).
      apply Qmult_inv_r. exact Hnonzero.
    + rewrite mulrV //.
Qed.

Lemma q_to_rat_div : forall left right : Q,
    q_to_rat (Qdiv left right) =
      (q_to_rat left / q_to_rat right)%R.
Proof.
  intros left right. unfold Qdiv.
  rewrite q_to_rat_mul q_to_rat_inv. reflexivity.
Qed.

Lemma q_to_rat_inject_Z : forall value : Z,
    q_to_rat (inject_Z value) = ((z_to_int value)%:~R : rat).
Proof.
  intro value. unfold q_to_rat, inject_Z. cbn.
  rewrite fracqE divr1. reflexivity.
Qed.

Lemma positive_to_int_positive : forall value,
    is_true (((0 : int) < positive_to_int value)%R).
Proof.
  intro value.
  apply (proj1 (z_to_int_positive_iff (Z.pos value))).
  exact (Pos2Z.is_pos value).
Qed.

Lemma positive_to_rat_positive : forall value,
    is_true (((0 : rat) < (positive_to_int value)%:~R)%R).
Proof.
  intro value. rewrite ltr0z. apply positive_to_int_positive.
Qed.

Theorem q_to_rat_le_iff : forall left right : Q,
    Qle left right <->
      is_true ((q_to_rat left <= q_to_rat right)%R).
Proof.
  intros [left_num left_den] [right_num right_den].
  unfold q_to_rat, Qle. cbn. rewrite !fracqE.
  rewrite ler_pdivl_mulr; last apply positive_to_rat_positive.
  rewrite [(_ / _ * _)%R]mulrAC.
  rewrite ler_pdivr_mulr; last apply positive_to_rat_positive.
  rewrite -!rmorphM /= ler_int.
  change (Z.le (Z.mul left_num (Z.pos right_den))
      (Z.mul right_num (Z.pos left_den)) <->
    is_true (((z_to_int left_num * z_to_int (Z.pos right_den)) <=
      (z_to_int right_num * z_to_int (Z.pos left_den)))%R)).
  rewrite <- !z_to_int_mul.
  apply z_to_int_le_iff.
Qed.

Theorem q_to_rat_lt_iff : forall left right : Q,
    Qlt left right <->
      is_true ((q_to_rat left < q_to_rat right)%R).
Proof.
  intros [left_num left_den] [right_num right_den].
  unfold q_to_rat, Qlt. cbn. rewrite !fracqE.
  rewrite ltr_pdivl_mulr; last apply positive_to_rat_positive.
  rewrite [(_ / _ * _)%R]mulrAC.
  rewrite ltr_pdivr_mulr; last apply positive_to_rat_positive.
  rewrite -!rmorphM /= ltr_int.
  change (Z.lt (Z.mul left_num (Z.pos right_den))
      (Z.mul right_num (Z.pos left_den)) <->
    is_true (((z_to_int left_num * z_to_int (Z.pos right_den)) <
      (z_to_int right_num * z_to_int (Z.pos left_den)))%R)).
  rewrite <- !z_to_int_mul.
  apply z_to_int_lt_iff.
Qed.

Corollary q_to_rat_nonnegative_iff : forall value : Q,
    Qle 0 value <-> is_true (((0 : rat) <= q_to_rat value)%R).
Proof.
  intro value. rewrite <- q_to_rat_zero. apply q_to_rat_le_iff.
Qed.

Corollary q_to_rat_positive_iff : forall value : Q,
    Qlt 0 value <-> is_true (((0 : rat) < q_to_rat value)%R).
Proof.
  intro value. rewrite <- q_to_rat_zero. apply q_to_rat_lt_iff.
Qed.

Corollary q_to_rat_nonpositive_iff : forall value : Q,
    Qle value 0 <-> is_true ((q_to_rat value <= (0 : rat))%R).
Proof.
  intro value. rewrite <- q_to_rat_zero. apply q_to_rat_le_iff.
Qed.

Corollary q_to_rat_negative_iff : forall value : Q,
    Qlt value 0 <-> is_true ((q_to_rat value < (0 : rat))%R).
Proof.
  intro value. rewrite <- q_to_rat_zero. apply q_to_rat_lt_iff.
Qed.

Corollary q_to_rat_inject_Z_le_iff : forall left right : Z,
    Z.le left right <->
      is_true ((q_to_rat (inject_Z left) <=
        q_to_rat (inject_Z right))%R).
Proof.
  intros left right. rewrite !q_to_rat_inject_Z ler_int.
  apply z_to_int_le_iff.
Qed.

Corollary q_to_rat_inject_Z_lt_iff : forall left right : Z,
    Z.lt left right <->
      is_true ((q_to_rat (inject_Z left) <
        q_to_rat (inject_Z right))%R).
Proof.
  intros left right. rewrite !q_to_rat_inject_Z ltr_int.
  apply z_to_int_lt_iff.
Qed.

Lemma q_to_rat_mul_positive_le_iff : forall left right factor : Q,
    Qlt 0 factor ->
    (Qle left right <->
      is_true (((q_to_rat left * q_to_rat factor) <=
        (q_to_rat right * q_to_rat factor))%R)).
Proof.
  intros left right factor Hfactor.
  have Hrat_factor : is_true (((0 : rat) < q_to_rat factor)%R).
    apply (proj1 (q_to_rat_positive_iff factor)). exact Hfactor.
  rewrite q_to_rat_le_iff.
  rewrite (ler_pmul2r Hrat_factor). reflexivity.
Qed.

Lemma q_to_rat_mul_positive_lt_iff : forall left right factor : Q,
    Qlt 0 factor ->
    (Qlt left right <->
      is_true (((q_to_rat left * q_to_rat factor) <
        (q_to_rat right * q_to_rat factor))%R)).
Proof.
  intros left right factor Hfactor.
  have Hrat_factor : is_true (((0 : rat) < q_to_rat factor)%R).
    apply (proj1 (q_to_rat_positive_iff factor)). exact Hfactor.
  rewrite q_to_rat_lt_iff.
  rewrite (ltr_pmul2r Hrat_factor). reflexivity.
Qed.

Corollary rat_to_q_nonnegative : forall value : rat,
    is_true (((0 : rat) <= value)%R) -> Qle 0 (rat_to_q value).
Proof.
  intros value Hvalue.
  apply (proj2 (q_to_rat_nonnegative_iff (rat_to_q value))).
  now rewrite rat_to_q_to_rat.
Qed.

Corollary rat_to_q_positive : forall value : rat,
    is_true (((0 : rat) < value)%R) -> Qlt 0 (rat_to_q value).
Proof.
  intros value Hvalue.
  apply (proj2 (q_to_rat_positive_iff (rat_to_q value))).
  now rewrite rat_to_q_to_rat.
Qed.
