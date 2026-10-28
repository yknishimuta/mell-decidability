From Coq Require Import List Vector.
From KruskalAfProp Require Import af.af af.af_tools.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Order Require Import AlmostFullBridge PeriodicOrder.
From Mell.VAS Require Import Runs JancarOrder LinearReachRelation.

Import ListNotations.

Definition ValidLinearRun {d} (system : PlainVAS d) :=
  { run : VASRun d | ValidVASRun system run }.

Definition DecoratedLinearRun {d} (system : PlainVAS d)
    (data : LinearRelationData d) :=
  (ValidLinearRun system * NVec (List.length (LinearGenerators data)))%type.

Definition DecoratedRunValue {d} {system : PlainVAS d}
    {data : LinearRelationData d}
    (decorated : DecoratedLinearRun system data) : VASRun d :=
  proj1_sig (fst decorated).

Definition DecoratedRunCoefficients {d} {system : PlainVAS d}
    {data : LinearRelationData d}
    (decorated : DecoratedLinearRun system data) :
    NVec (List.length (LinearGenerators data)) := snd decorated.

Definition DecoratedLinearRunValid {d} {system : PlainVAS d}
    {data : LinearRelationData d}
    (decorated : DecoratedLinearRun system data) : Prop :=
  exists period_input period_output,
    GeneratedPeriodPairBy (LinearGenerators data)
      (DecoratedRunCoefficients decorated) period_input period_output /\
    RunSource (DecoratedRunValue decorated) =
      nvec_add (LinearBaseInput data) period_input /\
    RunTarget (DecoratedRunValue decorated) =
      nvec_add (LinearBaseOutput data) period_output.

Definition DecoratedLinearRunLe {d} {system : PlainVAS d}
    {data : LinearRelationData d}
    (left right : DecoratedLinearRun system data) : Prop :=
  JancarRunLe (DecoratedRunValue left) (DecoratedRunValue right) /\
  nvec_le (DecoratedRunCoefficients left)
    (DecoratedRunCoefficients right).

Lemma decorated_linear_run_valid_omega : forall d system data decorated,
    @DecoratedLinearRunValid d system data decorated ->
    LinearOmegaRun system data (DecoratedRunValue decorated).
Proof.
  intros d system data [[run Hvalid] coefficients]
    [period_input [period_output [Hperiod [Hsource Htarget]]]].
  split; [exact Hvalid|]. exists period_input, period_output.
  split; [now exists coefficients|]. now split.
Qed.

Lemma linear_omega_run_has_decoration : forall d system data run,
    @LinearOmegaRun d system data run ->
    exists decorated : DecoratedLinearRun system data,
      DecoratedLinearRunValid decorated /\ DecoratedRunValue decorated = run.
Proof.
  intros d system data run [Hvalid
    [period_input [period_output [[coefficients Hperiod]
      [Hsource Htarget]]]]].
  exists (exist _ run Hvalid, coefficients). split.
  - exists period_input, period_output. split; [exact Hperiod|].
    now split.
  - reflexivity.
Qed.

Theorem decorated_linear_run_le_implies_linear_run_le : forall d
    (system : PlainVAS d) (data : LinearRelationData d)
    (left right : DecoratedLinearRun system data),
    DecoratedLinearRunValid left ->
    DecoratedLinearRunValid right ->
    DecoratedLinearRunLe left right ->
    LinearRunLe data (DecoratedRunValue left) (DecoratedRunValue right).
Proof.
  intros d system data left right
    [left_input [left_output [Hleft [Hleft_source Hleft_target]]]]
    [right_input [right_output [Hright [Hright_source Hright_target]]]]
    [Hjancar Hcoefficients].
  destruct (generated_period_pair_by_difference d (LinearGenerators data)
    (DecoratedRunCoefficients left) (DecoratedRunCoefficients right)
    left_input left_output right_input right_output
    Hcoefficients Hleft Hright)
    as [delta [delta_input [delta_output
      [_ [Hdelta [Hinput Houtput]]]]]].
  split; [exact Hjancar|]. exists delta_input, delta_output. split.
  - now exists delta.
  - split.
    + rewrite Hright_source, Hleft_source, Hinput.
      symmetry. apply nvec_add_assoc_linear.
    + rewrite Hright_target, Hleft_target, Houtput.
      symmetry. apply nvec_add_assoc_linear.
Qed.

Theorem decorated_linear_run_wqo : forall d
    (system : PlainVAS d) (data : LinearRelationData d),
    @afs (@DecoratedLinearRun d system data)
      (@DecoratedLinearRunValid d system data)
      (@DecoratedLinearRunLe d system data).
Proof.
  intros d system data. apply af_sub_rel_afs.
  apply af_af_sub_rel.
  unfold DecoratedLinearRunLe, DecoratedRunValue, DecoratedRunCoefficients.
  eapply af_mono; [|exact (af_product
    (@afs_af_sub_rel (VASRun d) (ValidVASRun system) (@JancarRunLe d)
      (jancar_run_wqo d system))
    (nvec_le_almost_full (List.length (LinearGenerators data))))].
  intros [[left Hleft] left_coefficients]
    [[right Hright] right_coefficients]. cbn.
  tauto.
Qed.

Theorem decorated_linear_run_finite_cover : forall d
    (system : PlainVAS d) (data : LinearRelationData d),
    exists basis : list
      { decorated : DecoratedLinearRun system data |
        DecoratedLinearRunValid decorated },
      forall decorated :
        { decorated : DecoratedLinearRun system data |
          DecoratedLinearRunValid decorated },
        exists base,
          List.In base basis /\
          DecoratedLinearRunLe (proj1_sig base) (proj1_sig decorated).
Proof.
  intros d system data.
  apply restricted_af_finite_cover_classic.
  apply decorated_linear_run_wqo.
Qed.

Theorem linear_omega_finite_cover : forall d
    (system : PlainVAS d) (data : LinearRelationData d),
    exists basis : list (VASRun d),
      (forall rho,
        List.In rho basis -> LinearOmegaRun system data rho) /\
      (forall sigma,
        LinearOmegaRun system data sigma ->
        exists rho,
          List.In rho basis /\ LinearRunLe data rho sigma).
Proof.
  intros d system data.
  destruct (decorated_linear_run_finite_cover d system data)
    as [decorated_basis Hcover].
  set (basis := List.map
    (fun base => DecoratedRunValue (proj1_sig base)) decorated_basis).
  exists basis. split.
  - intros rho Hin. unfold basis in Hin. apply in_map_iff in Hin.
    destruct Hin as [base [<- Hbase]].
    now apply decorated_linear_run_valid_omega, proj2_sig.
  - intros sigma Homega.
    destruct (linear_omega_run_has_decoration d system data sigma Homega)
      as [decorated [Hdecorated Hvalue]].
    set (element := exist (@DecoratedLinearRunValid d system data)
      decorated Hdecorated).
    destruct (Hcover element) as [base [Hbase Hle]].
    exists (DecoratedRunValue (proj1_sig base)). split.
    + unfold basis. apply in_map_iff.
      exists base. split; [reflexivity|exact Hbase].
    + rewrite <- Hvalue.
      apply decorated_linear_run_le_implies_linear_run_le.
      * apply proj2_sig.
      * exact Hdecorated.
      * exact Hle.
Qed.

Definition StrictLinearRunLe {d} (data : LinearRelationData d)
    (left right : VASRun d) : Prop :=
  LinearRunLe data left right /\ ~ LinearRunLe data right left.
