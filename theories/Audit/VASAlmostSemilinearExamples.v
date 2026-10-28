From Coq Require Import List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Periodic Cone.
From Mell.Order Require Import PeriodicOrder.
From Mell.VAS Require Import Runs Transformer AsymptoticRelation LinearReachRelation
  MinimalRunDecomposition PeriodicIntersection AlmostSemilinear
  LinearReachAlmostSemilinear.

Import ListNotations.

Definition task6c_n1 (value : nat) : NVec 1 :=
  @Vector.cons nat value 0 (@Vector.nil nat).

Definition task6c_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition task6c_zero_data : LinearRelationData 0 :=
  {| LinearBaseInput := nvec_zero 0;
     LinearBaseOutput := nvec_zero 0;
     LinearGenerators := [] |}.

Example task6c_empty_generators_asymptotic :
    AsymptoticallyDefinableNRelation
      (@GeneratedPeriodPair 0 []).
Proof. apply generated_period_pair_asymptotically_definable. Qed.

Example task6c_dimension_zero_restricted_reach :
    AlmostSemilinearNRelation
      (LinearReachRestricted ([] : PlainVAS 0) task6c_zero_data).
Proof. apply linear_reach_restricted_almost_semilinear. Qed.

Definition task6c_duplicate_generators : list (NVec 1 * NVec 1) :=
  [(task6c_n1 0, task6c_n1 0);
   (task6c_n1 1, task6c_n1 1);
   (task6c_n1 1, task6c_n1 1)].

Example task6c_zero_and_duplicate_generators :
    AsymptoticallyDefinableNRelation
      (GeneratedPeriodPair task6c_duplicate_generators).
Proof. apply generated_period_pair_asymptotically_definable. Qed.

Definition task6c_nonzero_base_data : LinearRelationData 1 :=
  {| LinearBaseInput := task6c_n1 2;
     LinearBaseOutput := task6c_n1 2;
     LinearGenerators := [(task6c_n1 1, task6c_n1 1)] |}.

Example task6c_nonzero_base_restricted_identity :
    AlmostSemilinearNRelation
      (LinearReachRestricted ([] : PlainVAS 1) task6c_nonzero_base_data).
Proof. apply linear_reach_restricted_almost_semilinear. Qed.

Definition task6c_twos : ZSet 1 := zvec_generated [task6c_z1 2].
Definition task6c_threes : ZSet 1 := zvec_generated [task6c_z1 3].

Example task6c_common_multiple_cone_intersection : forall point,
    Cone (fun value => task6c_twos value /\ task6c_threes value) point <->
    Cone task6c_twos point /\ Cone task6c_threes point.
Proof.
  intro point. apply periodic_cone_intersection;
    apply generated_periodic.
Qed.

Definition task6c_x_axis : ZSet 2 :=
  zvec_generated
    [@Vector.cons Z 1%Z 1%nat
      (@Vector.cons Z 0%Z 0%nat (@Vector.nil Z))].
Definition task6c_y_axis : ZSet 2 :=
  zvec_generated
    [@Vector.cons Z 0%Z 1%nat
      (@Vector.cons Z 1%Z 0%nat (@Vector.nil Z))].

Example task6c_distinct_direction_cone_intersection : forall point,
    Cone (fun value => task6c_x_axis value /\ task6c_y_axis value) point <->
    Cone task6c_x_axis point /\ Cone task6c_y_axis point.
Proof.
  intro point. apply periodic_cone_intersection;
    apply generated_periodic.
Qed.

Example task6c_empty_finite_union :
    AlmostSemilinearNRelation
      (fun source target : NVec 0 => exists relation : NRelation 0,
        List.In relation [] /\ relation source target).
Proof. apply almost_semilinear_nrelation_finite_union. constructor. Qed.

Definition task6c_zero_run : VASRun 0 := EmptyVASRun (nvec_zero 0).
Definition task6c_zero_component_relation : NRelation 0 :=
  LinearRunTransformerComponent ([] : PlainVAS 0) task6c_zero_data
    task6c_zero_run.

Example task6c_nonempty_finite_union :
    AlmostSemilinearNRelation
      (fun source target : NVec 0 => exists relation : NRelation 0,
        List.In relation [task6c_zero_component_relation;
          task6c_zero_component_relation] /\ relation source target).
Proof.
  apply almost_semilinear_nrelation_finite_union. repeat constructor.
  all: apply linear_run_transformer_component_almost_semilinear.
Qed.

Example task6c_qeq_noncanonical : ((2 # 2) == 1)%Q.
Proof. reflexivity. Qed.

Example task6c_intersection_zero :
    Periodic (fun value : ZVec 0 => value = zvec_zero 0) ->
    Periodic (fun value : ZVec 0 => value = zvec_zero 0) ->
    forall point,
      Cone (fun value : ZVec 0 =>
        value = zvec_zero 0 /\ value = zvec_zero 0) point <->
      Cone (fun value : ZVec 0 => value = zvec_zero 0) point /\
      Cone (fun value : ZVec 0 => value = zvec_zero 0) point.
Proof. intros HP HQ point. now apply periodic_cone_intersection. Qed.

Check periodic_intersection.
Check periodic_cone_intersection.
Check lemma_6_2_qdefinable_intersection.
Check lemma_6_2_asymptotically_definable_intersection.
Check nrelation_as_z_intersection.
Check asymptotically_definable_nrelation_intersection.
Check generated_period_pair_asymptotically_definable.
Check LinearTransformerPeriodIntersection.
Check linear_transformer_period_intersection_asymptotically_definable.
Check AlmostSemilinearNRelation.
Check linear_run_transformer_component_almost_semilinear.
Check almost_semilinear_nrelation_finite_union.
Check linear_reach_restricted_almost_semilinear.

Print Assumptions periodic_cone_intersection.
Print Assumptions lemma_6_2_asymptotically_definable_intersection.
Print Assumptions asymptotically_definable_nrelation_intersection.
Print Assumptions generated_period_pair_asymptotically_definable.
Print Assumptions linear_transformer_period_intersection_asymptotically_definable.
Print Assumptions linear_run_transformer_component_almost_semilinear.
Print Assumptions almost_semilinear_nrelation_finite_union.
Print Assumptions linear_reach_restricted_almost_semilinear.
