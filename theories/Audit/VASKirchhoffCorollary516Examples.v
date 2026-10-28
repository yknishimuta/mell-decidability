From Mell.VAS Require Import Runs Transformer AsymptoticRelation
  Intraproductions ProductionGraphFiniteness KirchhoffRelation
  FiniteKirchhoffRelations KirchhoffCorollary516.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge.
From Coq Require Import List QArith.

Open Scope Q_scope.

Check production_kirchhoff_positive_scale.
Check capacity_cone_union_kirchhoff.
Check GammaInputSupportMask.
Check GammaOutputSupportMask.
Check production_kirchhoff_same_signature_support.
Check finite_production_kirchhoff_relation_representatives.
Check finite_production_kirchhoff_union_qdefinable.
Check capacity_transformer_cone_qdefinable.
Check corollary_5_16_capacity_transformer_asymptotically_definable.
Check transformer_along_run_asymptotically_definable.

Example regression_dimension_zero_capacity_corollary
    (system : PlainVAS 0) (capacity : NVec 0) :
    AsymptoticallyDefinableNRelation
      (CapacityTransformer system capacity).
Proof.
  apply corollary_5_16_capacity_transformer_asymptotically_definable.
Qed.

Example regression_dimension_zero_run_transformer
    (system : PlainVAS 0) (run : VASRun 0) :
    AsymptoticallyDefinableNRelation
      (TransformerAlongRun system run).
Proof.
  apply transformer_along_run_asymptotically_definable.
Qed.

Example regression_positive_scale_is_strictly_positive_only :
    forall d system gamma (input output : QVec d),
      ProductionKirchhoffRelation system gamma input output ->
      ProductionKirchhoffRelation system gamma
        (qvec_scale 1 input) (qvec_scale 1 output).
Proof.
  intros. apply production_kirchhoff_positive_scale; [reflexivity|assumption].
Qed.

Example regression_support_masks_are_finitely_enumerated :
    forall d (gamma : ProductionTriple d),
      List.In (GammaInputSupportMask gamma) (all_bounded_masks d) /\
      List.In (GammaOutputSupportMask gamma) (all_bounded_masks d).
Proof.
  intros. split; apply all_bounded_masks_complete.
Qed.

Example regression_empty_action_capacity_transformer :
    forall d (capacity : NVec d),
      AsymptoticallyDefinableNRelation
        (CapacityTransformer (@nil (ZVec d)) capacity).
Proof.
  intros. apply corollary_5_16_capacity_transformer_asymptotically_definable.
Qed.

Example regression_zero_is_not_an_allowed_positive_scale : ~ (0 < (0 : Q)).
Proof. intro H. exact (Qlt_irrefl 0 H). Qed.

Definition task5d_nvec1 (value : nat) : NVec 1 :=
  @Vector.cons nat value 0 (@Vector.nil nat).

Definition task5d_gamma_empty_input : ProductionTriple 1 :=
  {| GammaInput := task5d_nvec1 0;
     GammaCapacity := task5d_nvec1 0;
     GammaOutput := task5d_nvec1 1 |}.

Definition task5d_gamma_positive_input : ProductionTriple 1 :=
  {| GammaInput := task5d_nvec1 1;
     GammaCapacity := task5d_nvec1 0;
     GammaOutput := task5d_nvec1 1 |}.

Example regression_graph_key_must_retain_input_support :
    GammaInputSupportMask task5d_gamma_empty_input <>
    GammaInputSupportMask task5d_gamma_positive_input.
Proof.
  intro Heq.
  pose proof (f_equal (fun mask => Vector.nth mask Fin.F1) Heq) as Hnth.
  cbn in Hnth. discriminate.
Qed.

Print Assumptions capacity_cone_union_kirchhoff.
Print Assumptions production_kirchhoff_positive_scale.
Print Assumptions production_kirchhoff_same_signature_support.
Print Assumptions finite_production_kirchhoff_relation_representatives.
Print Assumptions capacity_transformer_cone_qdefinable.
Print Assumptions corollary_5_16_capacity_transformer_asymptotically_definable.
Print Assumptions transformer_along_run_asymptotically_definable.
