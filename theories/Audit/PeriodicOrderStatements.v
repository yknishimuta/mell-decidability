From Coq Require Import List Vector ZArith Lia Program.Equality.
From KruskalAfProp Require Import af.af.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Periodic.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.

Set Printing Implicit.
Check @Periodic.
Check @PeriodicLe.
Check @FinitelyGeneratedPeriodic.
Check @zvec_generated.
Check @KruskalAfProp.af.af.afs.
Check periodic_order_wqo_iff_finitely_generated.

Definition audit_z1 (z : Z) : ZVec 1 :=
  @Vector.cons Z z 0 (@Vector.nil Z).

Definition audit_mixed_periodic : ZSet 1 :=
  zvec_generated [audit_z1 (-1); audit_z1 1].

Example audit_mixed_periodic_wqo :
    @afs (ZVec 1) audit_mixed_periodic (PeriodicLe audit_mixed_periodic).
Proof.
  apply finitely_generated_periodic_wqo.
  exists [audit_z1 (-1); audit_z1 1]. split.
  - intros generator Hin. apply generated_generator. exact Hin.
  - reflexivity.
Qed.

Example audit_zero_dimension :
    FinitelyGeneratedPeriodic (fun _ : ZVec 0 => True).
Proof.
  exists []. split; [intros generator Hin; contradiction|].
  intro value. split.
  - intro Htrue. dependent destruction value. apply generated_zero.
  - intro Hgenerated. exact I.
Qed.

Definition audit_zero_only {d} : ZSet d := fun value => value = zvec_zero d.

Example audit_zero_only_generated : forall d,
    FinitelyGeneratedPeriodic (@audit_zero_only d).
Proof.
  intro d. exists []. split; [intros generator Hin; contradiction|].
  intro value. split.
  - intros ->. apply generated_zero.
  - intros [coefficients H]. dependent destruction coefficients.
    unfold audit_zero_only. cbn in H. symmetry. exact H.
Qed.

Definition audit_z2 (x y : Z) : ZVec 2 :=
  @Vector.cons Z x 1 (@Vector.cons Z y 0 (@Vector.nil Z)).

Definition audit_nonfg (value : ZVec 2) : Prop :=
  value = zvec_zero 2 \/
  exists x y, value = audit_z2 x y /\ 0 < x /\ 0 < y.

Example audit_nonfg_periodic : Periodic audit_nonfg.
Proof.
  split.
  - left. reflexivity.
  - intros left right Hleft Hright.
    destruct Hleft as [Hleft_zero|
      [left_x [left_y [Hleft_eq [Hleft_x Hleft_y]]]]].
    + subst left.
      rewrite zvec_add_zero_left. exact Hright.
    + subst left.
      destruct Hright as [Hright_zero|
        [right_x [right_y [Hright_eq [Hright_x Hright_y]]]]].
      * subst right.
        rewrite zvec_add_zero_right. right.
        exists left_x, left_y. repeat split; assumption.
      * subst right. right.
        exists (left_x + right_x), (left_y + right_y).
        repeat split; try lia.
Qed.

Definition audit_antichain (n : nat) : ZVec 2 :=
  audit_z2 1 (Z.of_nat (S n)).

Example audit_antichain_member : forall n, audit_nonfg (audit_antichain n).
Proof. intro n. right. exists 1, (Z.of_nat (S n)). repeat split; lia. Qed.

Example audit_antichain_incomparable : forall n m, (n < m)%nat ->
    ~ PeriodicLe audit_nonfg (audit_antichain n) (audit_antichain m).
Proof.
  intros n m Hlt.
  assert (Hzlt : (Z.of_nat (S n) < Z.of_nat (S m))%Z) by lia.
  unfold PeriodicLe, audit_nonfg, audit_antichain,
    audit_z2, zvec_sub, zvec_zero. cbn.
  intros [Hzero|[x [y [Heq [Hx Hy]]]]].
  - pose proof (f_equal
      (fun value : ZVec 2 => Vector.nth value (Fin.FS Fin.F1)) Hzero)
      as Hcoordinate.
    change ((Z.of_nat (S m) - Z.of_nat (S n))%Z = 0%Z) in Hcoordinate.
    lia.
  - pose proof (f_equal
      (fun value : ZVec 2 => Vector.nth value Fin.F1) Heq)
      as Hcoordinate. change (0%Z = x) in Hcoordinate. lia.
Qed.

Example audit_antichain_reverse_incomparable : forall n m, (n < m)%nat ->
    ~ PeriodicLe audit_nonfg (audit_antichain m) (audit_antichain n).
Proof.
  intros n m Hlt.
  assert (Hzlt : (Z.of_nat (S n) < Z.of_nat (S m))%Z) by lia.
  unfold PeriodicLe, audit_nonfg, audit_antichain,
    audit_z2, zvec_sub, zvec_zero. cbn.
  intros [Hzero|[x [y [Heq [Hx Hy]]]]].
  - pose proof (f_equal
      (fun value : ZVec 2 => Vector.nth value (Fin.FS Fin.F1)) Hzero)
      as Hcoordinate.
    change ((Z.of_nat (S n) - Z.of_nat (S m))%Z = 0%Z) in Hcoordinate.
    lia.
  - pose proof (f_equal
      (fun value : ZVec 2 => Vector.nth value Fin.F1) Heq)
      as Hcoordinate. change (0%Z = x) in Hcoordinate. lia.
Qed.

Definition audit_full_group {d} : ZSet d := fun _ => True.

Example audit_full_group_periodic : forall d, Periodic (@audit_full_group d).
Proof.
  intro d. split.
  - exact I.
  - intros left right Hleft Hright. exact I.
Qed.

Example audit_full_group_finitely_generated : forall d,
    FinitelyGeneratedPeriodic (@audit_full_group d).
Proof.
  intro d. apply (proj1 (periodic_order_wqo_iff_finitely_generated
    d (@audit_full_group d) (audit_full_group_periodic d))).
  apply afs_full. intros left right Hleft Hright.
  unfold PeriodicLe, audit_full_group. exact I.
Qed.

(* T10_B_PUBLIC_TYPE *)
Set Printing All.
Check periodic_order_wqo_iff_finitely_generated.
Unset Printing All.

(* T10_B_ASSUMPTIONS *)
Print Assumptions af_finite_cover_classic.
Print Assumptions restricted_af_finite_cover_classic.
Print Assumptions orthant_order_wqo.
Print Assumptions periodic_order_wqo_iff_finitely_generated.
