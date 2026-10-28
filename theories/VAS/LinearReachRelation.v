From Coq Require Import Arith Fin Lia List Program.Equality Vector.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.VAS Require Import Runs JancarOrder Transformer TransformerJancar.

Import ListNotations.

Record LinearRelationData (d : nat) := {
  LinearBaseInput : NVec d;
  LinearBaseOutput : NVec d;
  LinearGenerators : list (NVec d * NVec d)
}.

Arguments LinearBaseInput {d} _.
Arguments LinearBaseOutput {d} _.
Arguments LinearGenerators {d} _.

Fixpoint GeneratedInput {d} (generators : list (NVec d * NVec d)) :
    NVec (List.length generators) -> NVec d :=
  match generators as values return NVec (List.length values) -> NVec d with
  | [] => fun _ => nvec_zero d
  | (input, _) :: tail => fun coefficients =>
      nvec_add (nvec_scale (Vector.hd coefficients) input)
        (GeneratedInput tail (Vector.tl coefficients))
  end.

Fixpoint GeneratedOutput {d} (generators : list (NVec d * NVec d)) :
    NVec (List.length generators) -> NVec d :=
  match generators as values return NVec (List.length values) -> NVec d with
  | [] => fun _ => nvec_zero d
  | (_, output) :: tail => fun coefficients =>
      nvec_add (nvec_scale (Vector.hd coefficients) output)
        (GeneratedOutput tail (Vector.tl coefficients))
  end.

Definition GeneratedPeriodPairBy {d}
    (generators : list (NVec d * NVec d))
    (coefficients : NVec (List.length generators))
    (input output : NVec d) : Prop :=
  GeneratedInput generators coefficients = input /\
  GeneratedOutput generators coefficients = output.

Definition GeneratedPeriodPair {d}
    (generators : list (NVec d * NVec d))
    (input output : NVec d) : Prop :=
  exists coefficients, GeneratedPeriodPairBy generators coefficients input output.

Definition LinearRelationContains {d} (data : LinearRelationData d)
    (source target : NVec d) : Prop :=
  exists period_input period_output,
    GeneratedPeriodPair (LinearGenerators data) period_input period_output /\
    source = nvec_add (LinearBaseInput data) period_input /\
    target = nvec_add (LinearBaseOutput data) period_output.

Definition LinearOmegaRun {d} (system : PlainVAS d)
    (data : LinearRelationData d) (run : VASRun d) : Prop :=
  ValidVASRun system run /\
  LinearRelationContains data (RunSource run) (RunTarget run).

Definition LinearRunLe {d} (data : LinearRelationData d)
    (rho sigma : VASRun d) : Prop :=
  JancarRunLe rho sigma /\
  exists period_input period_output,
    GeneratedPeriodPair (LinearGenerators data) period_input period_output /\
    RunSource sigma = nvec_add (RunSource rho) period_input /\
    RunTarget sigma = nvec_add (RunTarget rho) period_output.

Lemma nvec_add_assoc_linear : forall d (x y z : NVec d),
    nvec_add (nvec_add x y) z = nvec_add x (nvec_add y z).
Proof.
  intros d x y z. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Hindex; subst index'. unfold nvec_add.
  repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma generated_input_zero : forall d generators,
    @GeneratedInput d generators (nvec_zero (List.length generators)) =
    nvec_zero d.
Proof.
  intros d generators. induction generators as [|[input output] tail IH]; cbn.
  - reflexivity.
  - change (nvec_add (nvec_scale 0 input)
      (GeneratedInput tail (nvec_zero (List.length tail))) = nvec_zero d).
    rewrite IH, nvec_scale_zero, nvec_add_zero_left_local. reflexivity.
Qed.

Lemma generated_output_zero : forall d generators,
    @GeneratedOutput d generators (nvec_zero (List.length generators)) =
    nvec_zero d.
Proof.
  intros d generators. induction generators as [|[input output] tail IH]; cbn.
  - reflexivity.
  - change (nvec_add (nvec_scale 0 output)
      (GeneratedOutput tail (nvec_zero (List.length tail))) = nvec_zero d).
    rewrite IH, nvec_scale_zero, nvec_add_zero_left_local. reflexivity.
Qed.

Lemma generated_input_add : forall d (generators : list (NVec d * NVec d))
    (left right : NVec (List.length generators)),
    GeneratedInput generators (nvec_add left right) =
    nvec_add (GeneratedInput generators left) (GeneratedInput generators right).
Proof.
  intros d generators. induction generators as [|[input output] tail IH];
    intros left right.
  - cbn. now rewrite nvec_add_zero_left_local.
  - refine (Vector.caseS' left (fun left =>
      GeneratedInput ((input, output) :: tail) (nvec_add left right) =
      nvec_add (GeneratedInput ((input, output) :: tail) left)
        (GeneratedInput ((input, output) :: tail) right)) _).
    intros left_head left_tail.
    refine (Vector.caseS' right (fun right =>
      GeneratedInput ((input, output) :: tail)
        (nvec_add (@Vector.cons nat left_head _ left_tail) right) =
      nvec_add
        (GeneratedInput ((input, output) :: tail)
          (@Vector.cons nat left_head _ left_tail))
        (GeneratedInput ((input, output) :: tail) right)) _).
    intros right_head right_tail. cbn.
    rewrite IH, nvec_scale_add_coeff, nvec_add_shuffle. reflexivity.
Qed.

Lemma generated_output_add : forall d (generators : list (NVec d * NVec d))
    (left right : NVec (List.length generators)),
    GeneratedOutput generators (nvec_add left right) =
    nvec_add (GeneratedOutput generators left) (GeneratedOutput generators right).
Proof.
  intros d generators. induction generators as [|[input output] tail IH];
    intros left right.
  - cbn. now rewrite nvec_add_zero_left_local.
  - refine (Vector.caseS' left (fun left =>
      GeneratedOutput ((input, output) :: tail) (nvec_add left right) =
      nvec_add (GeneratedOutput ((input, output) :: tail) left)
        (GeneratedOutput ((input, output) :: tail) right)) _).
    intros left_head left_tail.
    refine (Vector.caseS' right (fun right =>
      GeneratedOutput ((input, output) :: tail)
        (nvec_add (@Vector.cons nat left_head _ left_tail) right) =
      nvec_add
        (GeneratedOutput ((input, output) :: tail)
          (@Vector.cons nat left_head _ left_tail))
        (GeneratedOutput ((input, output) :: tail) right)) _).
    intros right_head right_tail. cbn.
    rewrite IH, nvec_scale_add_coeff, nvec_add_shuffle. reflexivity.
Qed.

Lemma generated_period_pair_by_zero : forall d generators,
    GeneratedPeriodPairBy generators
      (nvec_zero (List.length generators)) (nvec_zero d) (nvec_zero d).
Proof.
  intros d generators. split; [apply generated_input_zero|apply generated_output_zero].
Qed.

Lemma generated_period_pair_zero : forall d generators,
    GeneratedPeriodPair generators (nvec_zero d) (nvec_zero d).
Proof. intros. exists (nvec_zero (List.length generators)). apply generated_period_pair_by_zero. Qed.

Lemma generated_period_pair_by_add : forall d
    (generators : list (NVec d * NVec d))
    (left right : NVec (List.length generators))
    left_input left_output right_input right_output,
    GeneratedPeriodPairBy generators left left_input left_output ->
    GeneratedPeriodPairBy generators right right_input right_output ->
    GeneratedPeriodPairBy generators (nvec_add left right)
      (nvec_add left_input right_input) (nvec_add left_output right_output).
Proof.
  intros d generators left right left_input left_output right_input right_output
    [Hli Hlo] [Hri Hro]. split.
  - rewrite generated_input_add, Hli, Hri. reflexivity.
  - rewrite generated_output_add, Hlo, Hro. reflexivity.
Qed.

Lemma generated_period_pair_add : forall d
    (generators : list (NVec d * NVec d))
    left_input left_output right_input right_output,
    GeneratedPeriodPair generators left_input left_output ->
    GeneratedPeriodPair generators right_input right_output ->
    GeneratedPeriodPair generators
      (nvec_add left_input right_input) (nvec_add left_output right_output).
Proof.
  intros d generators li lo ri ro [lc Hleft] [rc Hright].
  exists (nvec_add lc rc). now apply generated_period_pair_by_add.
Qed.

Lemma generated_period_pair_periodic : forall d generators,
    PeriodicNRelation (@GeneratedPeriodPair d generators).
Proof.
  intros d generators. split; [apply generated_period_pair_zero|].
  intros. now apply generated_period_pair_add.
Qed.

Lemma generated_period_pair_by_difference : forall d
    (generators : list (NVec d * NVec d))
    (lower upper : NVec (List.length generators))
    lower_input lower_output upper_input upper_output,
    nvec_le lower upper ->
    GeneratedPeriodPairBy generators lower lower_input lower_output ->
    GeneratedPeriodPairBy generators upper upper_input upper_output ->
    exists delta delta_input delta_output,
      upper = nvec_add lower delta /\
      GeneratedPeriodPairBy generators delta delta_input delta_output /\
      upper_input = nvec_add lower_input delta_input /\
      upper_output = nvec_add lower_output delta_output.
Proof.
  intros d generators lower upper lower_input lower_output upper_input upper_output
    Hle Hlower Hupper.
  destruct (nvec_le_exists_offset (List.length generators) lower upper Hle)
    as [delta Hupper_coefficients].
  set (delta_input := GeneratedInput generators delta).
  set (delta_output := GeneratedOutput generators delta).
  exists delta, delta_input, delta_output. split; [exact Hupper_coefficients|].
  split; [split; reflexivity|].
  destruct Hlower as [Hlower_input Hlower_output].
  destruct Hupper as [Hupper_input Hupper_output].
  split.
  - rewrite <- Hupper_input, Hupper_coefficients, generated_input_add,
      Hlower_input. reflexivity.
  - rewrite <- Hupper_output, Hupper_coefficients, generated_output_add,
      Hlower_output. reflexivity.
Qed.

Lemma linear_run_le_refl : forall d (data : LinearRelationData d) run,
    LinearRunLe data run run.
Proof.
  intros d data run. split; [apply jancar_run_le_refl|].
  exists (nvec_zero d), (nvec_zero d). split.
  - apply generated_period_pair_zero.
  - now rewrite !nvec_add_zero_right_local.
Qed.

Lemma linear_run_le_trans : forall d (data : LinearRelationData d) x y z,
    LinearRunLe data x y -> LinearRunLe data y z -> LinearRunLe data x z.
Proof.
  intros d data x y z [Hxy [xi [xo [Hxp [Hxs Hxt]]]]]
    [Hyz [yi [yo [Hyp [Hys Hyt]]]]]. split.
  - eapply jancar_run_le_trans; eauto.
  - exists (nvec_add xi yi), (nvec_add xo yo). split.
    + now apply generated_period_pair_add.
    + split.
      * rewrite Hys, Hxs. apply nvec_add_assoc_linear.
      * rewrite Hyt, Hxt. apply nvec_add_assoc_linear.
Qed.

Lemma linear_run_le_jancar : forall d (data : LinearRelationData d) rho sigma,
    LinearRunLe data rho sigma -> JancarRunLe rho sigma.
Proof. intros d data rho sigma [H _]. exact H. Qed.

Lemma linear_omega_run_valid : forall d system data run,
    @LinearOmegaRun d system data run -> ValidVASRun system run.
Proof. intros d system data run [H _]. exact H. Qed.

Lemma linear_omega_run_direction : forall d system data run,
    @LinearOmegaRun d system data run ->
    LinearRelationContains data (RunSource run) (RunTarget run).
Proof. intros d system data run [_ H]. exact H. Qed.

Lemma linear_omega_run_intro : forall d system data run,
    ValidVASRun system run ->
    LinearRelationContains data (RunSource run) (RunTarget run) ->
    @LinearOmegaRun d system data run.
Proof. now split. Qed.

Lemma linear_omega_run_upward : forall d system data rho sigma,
    @LinearOmegaRun d system data rho ->
    LinearRunLe data rho sigma ->
    ValidVASRun system sigma ->
    LinearOmegaRun system data sigma.
Proof.
  intros d system data rho sigma [Hvalidrho
    [ri [ro [Hrp [Hrs Hrt]]]]]
    [_ [di [do [Hdp [Hss Hst]]]]] Hvalidsigma.
  split; [exact Hvalidsigma|].
  exists (nvec_add ri di), (nvec_add ro do). split.
  - now apply generated_period_pair_add.
  - split.
    + rewrite Hss, Hrs. apply nvec_add_assoc_linear.
    + rewrite Hst, Hrt. apply nvec_add_assoc_linear.
Qed.

Theorem linear_run_le_transformer_period_witness : forall d system data
    (rho sigma : VASRun d),
    ValidVASRun system rho ->
    ValidVASRun system sigma ->
    LinearRunLe data rho sigma ->
    exists period_input period_output,
      GeneratedPeriodPair (LinearGenerators data) period_input period_output /\
      RunSource sigma = nvec_add (RunSource rho) period_input /\
      RunTarget sigma = nvec_add (RunTarget rho) period_output /\
      TransformerAlongRun system rho period_input period_output.
Proof.
  intros d system data rho sigma Hvalidrho Hvalidsigma
    [Hjancar [period_input [period_output
      [Hperiod [Hsource Htarget]]]]].
  destruct (jancar_run_le_transformer d system rho sigma
    Hvalidrho Hvalidsigma Hjancar)
    as [actual_input [actual_output
      [Hactual_source [Hactual_target Htransformer]]]].
  assert (actual_input = period_input) as ->.
  { apply nvec_add_left_cancel_transformer with (base := RunSource rho).
    now rewrite <- Hactual_source, <- Hsource. }
  assert (actual_output = period_output) as ->.
  { apply nvec_add_left_cancel_transformer with (base := RunTarget rho).
    now rewrite <- Hactual_target, <- Htarget. }
  exists period_input, period_output. repeat split; assumption.
Qed.
