From Coq Require Import List.
From Mell.Core Require Import Vector.
From Mell.VAS Require Import Runs Transformer AsymptoticRelation
  LinearReachRelation MinimalRunDecomposition KirchhoffCorollary516
  PeriodicIntersection AlmostSemilinear.

Import ListNotations.

Definition LinearTransformerPeriodIntersection {d}
    (system : PlainVAS d) (data : LinearRelationData d)
    (rho : VASRun d) : NRelation d :=
  fun offset_input offset_output =>
    TransformerAlongRun system rho offset_input offset_output /\
    GeneratedPeriodPair (LinearGenerators data) offset_input offset_output.

Theorem linear_transformer_period_intersection_asymptotically_definable :
    forall d (system : PlainVAS d) (data : LinearRelationData d)
      (rho : VASRun d),
      AsymptoticallyDefinableNRelation
        (LinearTransformerPeriodIntersection system data rho).
Proof.
  intros d system data rho.
  apply asymptotically_definable_nrelation_intersection.
  - apply transformer_along_run_asymptotically_definable.
  - apply generated_period_pair_asymptotically_definable.
Qed.

Definition LinearRunAlmostComponent {d}
    (system : PlainVAS d) (data : LinearRelationData d) (rho : VASRun d) :
    AlmostSemilinearNComponent d :=
  {| AlmostBaseInput := RunSource rho;
     AlmostBaseOutput := RunTarget rho;
     AlmostPeriodRelation := LinearTransformerPeriodIntersection system data rho |}.

Theorem linear_run_transformer_component_almost_semilinear : forall d
    (system : PlainVAS d) (data : LinearRelationData d) (rho : VASRun d),
    AlmostSemilinearNRelation
      (LinearRunTransformerComponent system data rho).
Proof.
  intros d system data rho.
  exists [LinearRunAlmostComponent system data rho]. split.
  - constructor; [apply linear_transformer_period_intersection_asymptotically_definable|constructor].
  - intros source target. split.
    + intros [offset_input [offset_output
        [Hperiod [Htransformer [Hsource Htarget]]]]].
      exists (LinearRunAlmostComponent system data rho). split; [now left|].
      exists offset_input, offset_output. cbn. repeat split; assumption.
    + intros [component [[Heq|Hin] Hcomponent]]; [|contradiction].
      subst component. destruct Hcomponent as [offset_input [offset_output
        [[Htransformer Hperiod] [Hsource Htarget]]]].
      exists offset_input, offset_output. repeat split; assumption.
Qed.

Theorem linear_reach_restricted_almost_semilinear : forall d
    (system : PlainVAS d) (data : LinearRelationData d),
    AlmostSemilinearNRelation (LinearReachRestricted system data).
Proof.
  intros d system data.
  destruct (lemma_6_1_linear_reach_decomposition d system data)
    as [basis [Hbasis [Hcover Hdecomposition]]].
  exists (List.map (LinearRunAlmostComponent system data) basis). split.
  - apply List.Forall_forall. intros component Hin.
    apply in_map_iff in Hin as [rho [<- Hin]].
    apply linear_transformer_period_intersection_asymptotically_definable.
  - intros source target. rewrite Hdecomposition. split.
    + intros [rho [Hin Hcomponent]].
      exists (LinearRunAlmostComponent system data rho). split.
      * apply in_map. exact Hin.
      * destruct Hcomponent as [offset_input [offset_output
          [Hperiod [Htransformer [Hsource Htarget]]]]].
        exists offset_input, offset_output. cbn. repeat split; assumption.
    + intros [component [Hin Hcomponent]].
      apply in_map_iff in Hin as [rho [<- Hin]].
      exists rho. split; [exact Hin|].
      destruct Hcomponent as [offset_input [offset_output
        [[Htransformer Hperiod] [Hsource Htarget]]]].
      exists offset_input, offset_output. repeat split; assumption.
Qed.
