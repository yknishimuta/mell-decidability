From Coq Require Import Lia List Program.Equality QArith QArith.Qabs Vector
  VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone MathCompBridge Periodic
  QConeCore LatticeGordanInterface.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.
Set Printing Implicit.

Check @Difference.
Check @ClosedLinearization.
Check @closed_linearization_spec.
Check @FullPeriodic.
Check @PolyhedralFullPeriodic.
Check @Linearization.
Check @full_periodic_iff_linearization_fixed.
Check @AsymptoticallyDefinable.
Check @difference_is_integer_additive_group.
Check @integer_additive_group_periodic_le_total.
Check @integer_additive_group_order_wqo.
Check @difference_group_finitely_generated.

Definition l0_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition l0_z2 (left right : Z) : ZVec 2 :=
  @Vector.cons Z left 1 (@Vector.cons Z right 0 (@Vector.nil Z)).

Definition paper_positive_periodic (value : ZVec 2) : Prop :=
  (Vector.nth value Fin.F1 = 0%Z /\
    Vector.nth value (Fin.FS Fin.F1) = 0%Z) \/
  ((0 < Vector.nth value Fin.F1)%Z /\
    (0 < Vector.nth value (Fin.FS Fin.F1))%Z).

Definition paper_open_quadrant_cone (value : QVec 2) : Prop :=
  QVecEq value (qvec_zero 2) \/
  ((0 < value Fin.F1)%Q /\ (0 < value (Fin.FS Fin.F1))%Q).

Lemma paper_positive_is_periodic : Periodic paper_positive_periodic.
Proof.
  split.
  - left. split; reflexivity.
  - intros left right Hleft Hright. unfold paper_positive_periodic in *.
    unfold zvec_add.
    rewrite (nth_map2 Z.add left right Fin.F1 Fin.F1 Fin.F1
      eq_refl eq_refl).
    rewrite (nth_map2 Z.add left right (Fin.FS Fin.F1) (Fin.FS Fin.F1)
      (Fin.FS Fin.F1) eq_refl eq_refl).
    destruct Hleft as [[Hl0 Hl1]|[Hl0 Hl1]];
      destruct Hright as [[Hr0 Hr1]|[Hr0 Hr1]]; [left|right|right|right];
      split; lia.
Qed.

Lemma paper_open_quadrant_is_rational_cone :
    RationalCone paper_open_quadrant_cone.
Proof.
  constructor.
  - constructor.
    + left. apply qvec_eq_refl.
    + intros left right Hleft Hright.
      destruct Hleft as [Hleft|[Hleft0 Hleft1]];
        destruct Hright as [Hright|[Hright0 Hright1]].
      * left. intro index. unfold qvec_add, qvec_zero.
        setoid_rewrite (Hleft index). setoid_rewrite (Hright index).
        reflexivity.
      * right. split; unfold qvec_add.
        -- setoid_rewrite (Hleft Fin.F1). setoid_rewrite Qplus_0_l.
           exact Hright0.
        -- setoid_rewrite (Hleft (Fin.FS Fin.F1)).
           setoid_rewrite Qplus_0_l. exact Hright1.
      * right. split; unfold qvec_add.
        -- setoid_rewrite (Hright Fin.F1). setoid_rewrite Qplus_0_r.
           exact Hleft0.
        -- setoid_rewrite (Hright (Fin.FS Fin.F1)).
           setoid_rewrite Qplus_0_r. exact Hleft1.
      * right. split; unfold qvec_add;
          setoid_replace 0 with (0 + 0)%Q by reflexivity;
          now apply Qplus_lt_compat.
    + intros coefficient value Hcoefficient Hvalue.
      destruct Hvalue as [Hzero|[Hpositive0 Hpositive1]].
      * left. intro index. unfold qvec_scale, qvec_zero.
        setoid_rewrite (Hzero index). apply Qmult_0_r.
      * destruct (Qlt_le_dec 0 coefficient) as [Hpositive|Hnonpositive].
        -- right. split; unfold qvec_scale;
             now apply Qmult_lt_0_compat.
        -- left. assert (Hcoefficient_zero : coefficient == 0).
           { now apply Qle_antisym. }
           intro index. unfold qvec_scale, qvec_zero.
           setoid_rewrite Hcoefficient_zero. apply Qmult_0_l.
  - intros left right Heq. split; intro Hvalue.
    + destruct Hvalue as [Hzero|[Hpositive0 Hpositive1]].
      * left. intro index. transitivity (left index).
        -- symmetry. apply Heq.
        -- apply Hzero.
      * right. split.
        -- setoid_rewrite <- (Heq Fin.F1). exact Hpositive0.
        -- setoid_rewrite <- (Heq (Fin.FS Fin.F1)). exact Hpositive1.
    + destruct Hvalue as [Hzero|[Hpositive0 Hpositive1]].
      * left. intro index. transitivity (right index).
        -- apply Heq.
        -- apply Hzero.
      * right. split.
        -- setoid_rewrite (Heq Fin.F1). exact Hpositive0.
        -- setoid_rewrite (Heq (Fin.FS Fin.F1)). exact Hpositive1.
Qed.

Lemma paper_positive_full_periodic : FullPeriodic paper_positive_periodic.
Proof.
  split; [exact paper_positive_is_periodic|].
  exists (fun _ : ZVec 2 => True), paper_open_quadrant_cone. split.
  - constructor; trivial.
  - split; [exact paper_open_quadrant_is_rational_cone|].
    intro value. split.
    + intro Hvalue. split; [exact I|]. destruct Hvalue as [Hzero|Hpositive].
      * left. intro index.
        refine (Fin.caseS' index (fun index => _) _ _).
        -- unfold zvec_to_qvec, qvec_zero. cbn. rewrite (proj1 Hzero).
           reflexivity.
        -- intro tail. refine (Fin.caseS' tail (fun tail => _) _ _).
           ++ unfold zvec_to_qvec, qvec_zero. cbn. rewrite (proj2 Hzero).
              reflexivity.
           ++ intro impossible. inversion impossible.
      * right. destruct Hpositive as [Hpositive0 Hpositive1]. split;
          unfold zvec_to_qvec; cbn; unfold Qlt; cbn; lia.
    + intros [_ Hcone]. destruct Hcone as [Hzero|Hpositive].
      * left. split.
        -- apply (proj1 (inject_Z_injective _ _)).
           exact (Hzero Fin.F1).
        -- apply (proj1 (inject_Z_injective _ _)).
           exact (Hzero (Fin.FS Fin.F1)).
      * right. destruct Hpositive as [Hpositive0 Hpositive1]. split;
          unfold zvec_to_qvec in *; cbn in *; unfold Qlt in *; cbn in *; lia.
Qed.

Example paper_example_2_3_is_full : FullPeriodic paper_positive_periodic.
Proof. exact paper_positive_full_periodic. Qed.

Example paper_example_2_3_is_linearization_fixed :
    SameSet paper_positive_periodic (Linearization paper_positive_periodic).
Proof.
  apply (proj1 (full_periodic_iff_linearization_fixed 2
    paper_positive_periodic paper_positive_is_periodic)).
  exact paper_positive_full_periodic.
Qed.

Example difference_dimension_zero_finitely_generated :
    FinitelyGeneratedGroup
      (Difference (@zvec_generated 0 [])).
Proof. apply difference_group_finitely_generated, generated_periodic. Qed.

Example difference_zero_monoid_finitely_generated :
    FinitelyGeneratedGroup
      (Difference (@zvec_generated 1 [])).
Proof. apply difference_group_finitely_generated, generated_periodic. Qed.

Example difference_twoN_finitely_generated :
    FinitelyGeneratedGroup
      (Difference (zvec_generated [l0_z1 2])).
Proof. apply difference_group_finitely_generated, generated_periodic. Qed.

Example difference_N2_finitely_generated :
    FinitelyGeneratedGroup
      (Difference (zvec_generated [l0_z2 1 0; l0_z2 0 1])).
Proof. apply difference_group_finitely_generated, generated_periodic. Qed.

Example difference_mixed_sign_finitely_generated :
    FinitelyGeneratedGroup
      (Difference (zvec_generated [l0_z1 2; l0_z1 (-3)])).
Proof. apply difference_group_finitely_generated, generated_periodic. Qed.

Example difference_low_rank_finitely_generated :
    FinitelyGeneratedGroup
      (Difference (zvec_generated [l0_z2 1 0])).
Proof. apply difference_group_finitely_generated, generated_periodic. Qed.

Definition l0_gap_periodic (value : ZVec 1) : Prop :=
  Vector.nth value Fin.F1 = 0%Z \/ (2 <= Vector.nth value Fin.F1)%Z.

Lemma l0_gap_is_periodic : Periodic l0_gap_periodic.
Proof.
  split.
  - left. reflexivity.
  - intros left right Hleft Hright. unfold l0_gap_periodic in *.
    unfold zvec_add.
    rewrite (nth_map2 Z.add left right Fin.F1 Fin.F1 Fin.F1 eq_refl eq_refl).
    destruct Hleft, Hright; lia.
Qed.

Lemma l0_gap_one_not_member : ~ l0_gap_periodic (l0_z1 1).
Proof. unfold l0_gap_periodic, l0_z1; cbn; lia. Qed.

Lemma l0_gap_one_in_difference : Difference l0_gap_periodic (l0_z1 1).
Proof.
  exists (l0_z1 3), (l0_z1 2). split.
  - right. unfold l0_z1; cbn; lia.
  - split.
    + right. unfold l0_z1; cbn; lia.
    + reflexivity.
Qed.

Lemma l0_gap_one_in_cone : Cone l0_gap_periodic (zvec_to_qvec (l0_z1 1)).
Proof.
  apply cleared_cone_gen. exists 2%nat, (l0_z1 2).
  split.
  - lia.
  - split.
    + right. unfold l0_z1; cbn; lia.
    + intro index. refine (Fin.caseS' index (fun index => _) _ _).
      * reflexivity.
      * intro impossible. inversion impossible.
Qed.

Lemma l0_gap_one_in_cone_closure :
    QClosure (Cone l0_gap_periodic) (zvec_to_qvec (l0_z1 1)).
Proof.
  intros delta Hdelta. exists (zvec_to_qvec (l0_z1 1)). split.
  - exact l0_gap_one_in_cone.
  - intro index. refine (Fin.caseS' index (fun index => _) _ _).
    + cbn. exact Hdelta.
    + intro impossible. inversion impossible.
Qed.

Example closed_linearization_can_strictly_enlarge :
    ~ l0_gap_periodic (l0_z1 1) /\
    ClosedLinearization l0_gap_periodic (l0_z1 1).
Proof.
  split; [exact l0_gap_one_not_member|]. split.
  - exact l0_gap_one_in_difference.
  - exact l0_gap_one_in_cone_closure.
Qed.

Print FullPeriodic.
Print PolyhedralFullPeriodic.
Print Assumptions full_periodic_iff_linearization_fixed.
Print Assumptions paper_positive_full_periodic.
Print Assumptions closed_linearization_spec.
Print Assumptions difference_group_finitely_generated.
