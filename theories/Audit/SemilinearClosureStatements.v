From Coq Require Import List Vector ZArith QArith Lia PeanoNat.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation Formula QuantifierFree Closure.
From Mell.Presburger Require Import Semantics.
From Mell.Geometry Require Import RationalDefinability.
From Mell.Presburger Require Import NatSemilinear.

Import ListNotations.
Open Scope nat_scope.

Set Printing Implicit.

Check SemiCode.
Check @denote.
Check @compile_membership.
Check @compile_membership_correct.
Check @presburger_nat_semilinear.
Check MiniCooper.Theory.qe.
Check MiniCooper.Theory.interpret_qe.
Check @zero_outside_scoped.
Check @zero_outside_correct_on_nat_env.
Check @qf_semicode.
Check @QDefinable.

Check semilinear_finite_union.
Check semilinear_minkowski_sum.
Check semilinear_product.
Check semilinear_projection.
Check semilinear_intersection.
Check semilinear_complement.
Check qdefinable_projection.
Check qdefinable_intersection.

Definition t10a_v0 : NVec 1 :=
  @Coq.Vectors.Vector.cons nat 0 0 (@Coq.Vectors.Vector.nil nat).

Definition t10a_v2 : NVec 1 :=
  @Coq.Vectors.Vector.cons nat 2 0 (@Coq.Vectors.Vector.nil nat).

Definition t10a_v3 : NVec 1 :=
  @Coq.Vectors.Vector.cons nat 3 0 (@Coq.Vectors.Vector.nil nat).

Definition t10a_v5 : NVec 1 :=
  @Coq.Vectors.Vector.cons nat 5 0 (@Coq.Vectors.Vector.nil nat).

Definition t10a_empty_vector : NVec 0 := @Coq.Vectors.Vector.nil nat.

Example t10a_empty_finite_union :
    Semilinear (fun _ : NVec 1 => False).
Proof.
  exists []. intro value. split.
  - contradiction.
  - intro Hdenote. exfalso. exact (denote_empty 1 value Hdenote).
Qed.

Example t10a_zero_period :
    linear_denote (t10a_v0, [t10a_v0]) t10a_v0.
Proof. exists [37], t10a_v0. split; reflexivity. Qed.

Example t10a_nontrivial_minkowski :
    linear_denote (component_minkowski (t10a_v2, []) (t10a_v3, []))
      t10a_v5.
Proof. exists [], t10a_v0. split; reflexivity. Qed.

Example t10a_dimension_zero_product :
    denote (semicode_product [(t10a_empty_vector, [])]
      [(t10a_empty_vector, [])]) t10a_empty_vector.
Proof.
  apply semicode_product_correct. split.
  - exists (t10a_empty_vector, []). split; [now left|].
    exists [], t10a_empty_vector. split; reflexivity.
  - exists (t10a_empty_vector, []). split; [now left|].
    exists [], t10a_empty_vector. split; reflexivity.
Qed.

Definition t10a_v23 : NVec 2 :=
  @Coq.Vectors.Vector.cons nat 2 1
    (@Coq.Vectors.Vector.cons nat 3 0 (@Coq.Vectors.Vector.nil nat)).

Definition t10a_v22 : NVec 2 :=
  @Coq.Vectors.Vector.cons nat 2 1
    (@Coq.Vectors.Vector.cons nat 2 0 (@Coq.Vectors.Vector.nil nat)).

Definition t10a_v32 : NVec 2 :=
  @Coq.Vectors.Vector.cons nat 3 1
    (@Coq.Vectors.Vector.cons nat 2 0 (@Coq.Vectors.Vector.nil nat)).

Definition t10a_duplicate_first (_ : Fin.t 2) : Fin.t 2 := Fin.F1.

Example t10a_projection_repeated_coordinate :
    nvec_project t10a_duplicate_first t10a_v23 = t10a_v22.
Proof. reflexivity. Qed.

Definition t10a_swap (index : Fin.t 2) : Fin.t 2 :=
  Fin.caseS' index (fun _ => Fin.t 2) (Fin.FS Fin.F1) (fun _ => Fin.F1).

Example t10a_projection_permuted_coordinates :
    nvec_project t10a_swap t10a_v23 = t10a_v32.
Proof. reflexivity. Qed.

Example t10a_nontrivial_product :
    denote (semicode_product [(t10a_v2, [])] [(t10a_v3, [])]) t10a_v23.
Proof.
  apply semicode_product_correct. split.
  - exists (t10a_v2, []). split; [now left|].
    exists [], t10a_v0. split; reflexivity.
  - exists (t10a_v3, []). split; [now left|].
    exists [], t10a_v0. split; reflexivity.
Qed.

Example t10a_two_three_intersection_is_six : forall n,
    (Nat.divide 2 n /\ Nat.divide 3 n) <-> Nat.divide 6 n.
Proof.
  intro n. rewrite <- Nat.lcm_divide_iff. reflexivity.
Qed.

Definition t10a_even_code : SemiCode 1 := [(t10a_v0, [t10a_v2])].
Definition t10a_three_code : SemiCode 1 := [(t10a_v0, [t10a_v3])].

Example t10a_two_three_intersection_semilinear :
    Semilinear (fun value =>
      denote t10a_even_code value /\ denote t10a_three_code value).
Proof.
  apply semilinear_intersection.
  - exists t10a_even_code. intro value. reflexivity.
  - exists t10a_three_code. intro value. reflexivity.
Qed.

Example t10a_not_even_is_odd : forall n,
    (~ Nat.Even n) <-> Nat.Odd n.
Proof.
  intro n. split.
  - intro Hnot_even. destruct (Nat.Even_Odd_dec n); auto. contradiction.
  - intros [half Hodd] [half' Heven]. lia.
Qed.

Example t10a_even_complement_semilinear :
    Semilinear (fun value => ~ denote t10a_even_code value).
Proof.
  apply semilinear_complement. exists t10a_even_code. intro value. reflexivity.
Qed.

Example t10a_empty_complement_is_semilinear :
    Semilinear (fun _ : NVec 0 => ~ False).
Proof.
  apply semilinear_complement. exists []. intro value. split.
  - contradiction.
  - intro Hdenote. exfalso. exact (denote_empty 0 value Hdenote).
Qed.

Example t10a_full_complement_is_semilinear :
    Semilinear (fun _ : NVec 0 => ~ True).
Proof.
  apply semilinear_complement. exists [(t10a_empty_vector, [])]. intro value.
  split.
  - intro Htrue.
    refine (Coq.Vectors.Vector.case0
      (fun value => denote [(t10a_empty_vector, [])] value) _ value).
    exists (t10a_empty_vector, []). split; [now left|].
    exists [], t10a_empty_vector. split; reflexivity.
  - intro Hdenote. exact I.
Qed.

Example t10a_negative_coordinate_rejected :
    ~ formula_semantics (fun _ => (-1)%Z)
        (compile_membership [(t10a_v0, [])]).
Proof.
  rewrite compile_membership_correct.
  intros [candidate [_ Hcoordinates]].
  specialize (Hcoordinates 0%nat ltac:(lia)). lia.
Qed.

Local Open Scope Q_scope.

Example t10a_rational_exists_and_debruijn :
    qformula_semantics
      (fun variable => if Nat.eqb variable 0%nat
        then inject_Z 2%Z else inject_Z 0%Z)
      (QFExists
        (QFAnd (QFEq (QTVar 0%nat) (QTConst (inject_Z 1%Z)))
          (QFEq (QTVar 1%nat) (QTConst (inject_Z 2%Z))))).
Proof. exists (inject_Z 1%Z). cbn. split; reflexivity. Qed.

Print Assumptions semilinear_finite_union.
Print Assumptions semilinear_minkowski_sum.
Print Assumptions semilinear_product.
Print Assumptions semilinear_projection.
Print Assumptions semilinear_intersection.
Print Assumptions semilinear_complement.
Print Assumptions qdefinable_projection.
Print Assumptions qdefinable_intersection.
