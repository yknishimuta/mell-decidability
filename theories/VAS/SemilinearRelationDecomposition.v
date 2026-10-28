From Coq Require Import List Vector VectorSpec.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation Closure.
From Mell.VAS Require Import Runs Transformer LinearReachRelation
  MinimalRunDecomposition AlmostSemilinear LinearReachAlmostSemilinear.

Import ListNotations.
Module StdVector := Coq.Vectors.Vector.

Definition npair_pack {d} (source target : NVec d) : NVec (d + d) :=
  StdVector.append source target.

Definition npair_left {d} (pair : NVec (d + d)) : NVec d :=
  fst (StdVector.splitat d pair).

Definition npair_right {d} (pair : NVec (d + d)) : NVec d :=
  snd (StdVector.splitat d pair).

Lemma npair_left_pack : forall d (source target : NVec d),
    npair_left (npair_pack source target) = source.
Proof. intros; unfold npair_left, npair_pack; now rewrite VectorSpec.splitat_append. Qed.

Lemma npair_right_pack : forall d (source target : NVec d),
    npair_right (npair_pack source target) = target.
Proof. intros; unfold npair_right, npair_pack; now rewrite VectorSpec.splitat_append. Qed.

Lemma npair_pack_split : forall d (pair : NVec (d + d)),
    npair_pack (npair_left pair) (npair_right pair) = pair.
Proof.
  intros d pair. unfold npair_pack, npair_left, npair_right.
  destruct (StdVector.splitat d pair) as [source target] eqn:Hsplit.
  now apply VectorSpec.append_splitat in Hsplit.
Qed.
Lemma npair_left_add : forall d (left right : NVec (d + d)),
    npair_left (nvec_add left right) =
    nvec_add (npair_left left) (npair_left right).
Proof.
  intros d left right.
  unfold npair_left.
  destruct (StdVector.splitat d left) as [left1 left2] eqn:Hleft.
  destruct (StdVector.splitat d right) as [right1 right2] eqn:Hright.
  apply VectorSpec.append_splitat in Hleft, Hright. subst left right.
  rewrite nvec_add_append_local, VectorSpec.splitat_append. reflexivity.
Qed.

Lemma npair_right_add : forall d (left right : NVec (d + d)),
    npair_right (nvec_add left right) =
    nvec_add (npair_right left) (npair_right right).
Proof.
  intros d left right.
  unfold npair_right.
  destruct (StdVector.splitat d left) as [left1 left2] eqn:Hleft.
  destruct (StdVector.splitat d right) as [right1 right2] eqn:Hright.
  apply VectorSpec.append_splitat in Hleft, Hright. subst left right.
  rewrite nvec_add_append_local, VectorSpec.splitat_append. reflexivity.
Qed.

Lemma npair_pack_add : forall d
    (source1 target1 source2 target2 : NVec d),
    nvec_add (npair_pack source1 target1) (npair_pack source2 target2) =
    npair_pack (nvec_add source1 source2) (nvec_add target1 target2).
Proof. intros; unfold npair_pack; apply nvec_add_append_local. Qed.

Lemma npair_left_zero : forall d,
    npair_left (nvec_zero (d + d)) = nvec_zero d.
Proof.
  intro d. rewrite nvec_zero_append_local.
  unfold npair_left. now rewrite VectorSpec.splitat_append.
Qed.

Lemma npair_right_zero : forall d,
    npair_right (nvec_zero (d + d)) = nvec_zero d.
Proof.
  intro d. rewrite nvec_zero_append_local.
  unfold npair_right. now rewrite VectorSpec.splitat_append.
Qed.

Lemma npair_left_scale : forall d coefficient (value : NVec (d + d)),
    npair_left (nvec_scale coefficient value) =
    nvec_scale coefficient (npair_left value).
Proof.
  intros d coefficient value. unfold npair_left.
  destruct (StdVector.splitat d value) as [left right] eqn:Hvalue.
  apply VectorSpec.append_splitat in Hvalue. subst value.
  rewrite nvec_scale_append, VectorSpec.splitat_append. reflexivity.
Qed.

Lemma npair_right_scale : forall d coefficient (value : NVec (d + d)),
    npair_right (nvec_scale coefficient value) =
    nvec_scale coefficient (npair_right value).
Proof.
  intros d coefficient value. unfold npair_right.
  destruct (StdVector.splitat d value) as [left right] eqn:Hvalue.
  apply VectorSpec.append_splitat in Hvalue. subst value.
  rewrite nvec_scale_append, VectorSpec.splitat_append. reflexivity.
Qed.

Definition SemilinearNRelation {d} (relation : NRelation d) : Prop :=
  Semilinear (fun pair : NVec (d + d) =>
    relation (npair_left pair) (npair_right pair)).

Fixpoint split_period_generators {d}
    (periods : list (NVec (d + d))) : list (NVec d * NVec d) :=
  match periods with
  | [] => []
  | period :: tail =>
      (npair_left period, npair_right period) :: split_period_generators tail
  end.

Definition linear_component_relation_data {d}
    (component : LinearComponent (d + d)) : LinearRelationData d :=
  {| LinearBaseInput := npair_left (fst component);
     LinearBaseOutput := npair_right (fst component);
     LinearGenerators := split_period_generators (snd component) |}.

Lemma generated_pair_weighted_sum : forall (d : nat)
    (periods : list (NVec (d + d)))
    (coefficients : NVec (List.length (split_period_generators periods))),
    weighted_sum (StdVector.to_list coefficients) periods =
      Some (npair_pack
        (GeneratedInput
          (split_period_generators periods) coefficients)
        (GeneratedOutput
          (split_period_generators periods) coefficients)).
Proof.
  intros d periods. induction periods as [|period periods IH]; intro coefficients.
  - refine (StdVector.case0 (fun coefficients => _) _ coefficients).
    cbn. unfold npair_pack. rewrite <- nvec_zero_append_local. reflexivity.
  - refine (StdVector.caseS' coefficients (fun coefficients => _) _).
    intros coefficient tail.
    cbn [StdVector.to_list weighted_sum GeneratedInput GeneratedOutput
      split_period_generators].
    change
      (match weighted_sum (StdVector.to_list tail) periods with
       | Some value => Some (nvec_add (nvec_scale coefficient period) value)
       | None => None
       end =
       Some (npair_pack
         (nvec_add (nvec_scale coefficient (npair_left period))
           (GeneratedInput (split_period_generators periods) tail))
         (nvec_add (nvec_scale coefficient (npair_right period))
           (GeneratedOutput (split_period_generators periods) tail)))).
    rewrite IH.
    rewrite <- (npair_pack_split d period) at 1.
    unfold npair_pack.
    rewrite nvec_scale_append, nvec_add_append_local. reflexivity.
Qed.

Lemma weighted_sum_generated_period_pair : forall d
    (periods : list (NVec (d + d))) coefficients contribution,
    weighted_sum coefficients periods = Some contribution ->
    GeneratedPeriodPair (split_period_generators periods)
      (npair_left contribution) (npair_right contribution).
Proof.
  intros d periods. induction periods as [|period periods IH];
    intros [|coefficient coefficients] contribution Hsum; cbn in Hsum;
    try discriminate.
  - inversion Hsum; subst contribution.
    rewrite npair_left_zero, npair_right_zero. apply generated_period_pair_zero.
  - destruct (weighted_sum coefficients periods) as [tail|] eqn:Htail;
      try discriminate.
    inversion Hsum; subst contribution.
    destruct (IH coefficients tail Htail) as [tail_coefficients [Hinput Houtput]].
    exists (StdVector.cons nat coefficient _ tail_coefficients). split; cbn.
    + rewrite Hinput, npair_left_add, npair_left_scale. reflexivity.
    + rewrite Houtput, npair_right_add, npair_right_scale. reflexivity.
Qed.

Theorem linear_component_relation_data_correct : forall d
    (component : LinearComponent (d + d)) source target,
    linear_denote component (npair_pack source target) <->
    LinearRelationContains (linear_component_relation_data component)
      source target.
Proof.
  intros d [base periods] source target. cbn [linear_component_relation_data].
  split.
  - intros [coefficients [contribution [Hsum Hvalue]]].
    pose proof (weighted_sum_generated_period_pair d periods coefficients
      contribution Hsum) as Hperiod.
    exists (npair_left contribution), (npair_right contribution).
    split; [exact Hperiod|]. split.
    + pose proof (f_equal (@npair_left d) Hvalue) as Hleft.
      rewrite npair_left_pack, npair_left_add in Hleft. exact Hleft.
    + pose proof (f_equal (@npair_right d) Hvalue) as Hright.
      rewrite npair_right_pack, npair_right_add in Hright. exact Hright.
  - intros [period_input [period_output
      [[coefficients [Hinput Houtput]] [Hsource Htarget]]]].
    change (GeneratedInput (split_period_generators periods) coefficients =
      period_input) in Hinput.
    change (GeneratedOutput (split_period_generators periods) coefficients =
      period_output) in Houtput.
    change (source = nvec_add (npair_left base) period_input) in Hsource.
    change (target = nvec_add (npair_right base) period_output) in Htarget.
    exists (StdVector.to_list coefficients),
      (npair_pack period_input period_output). split.
    + pose proof (generated_pair_weighted_sum d periods coefficients) as Hsum.
      now rewrite Hinput, Houtput in Hsum.
    + subst source target.
      symmetry.
      change (nvec_add base (npair_pack period_input period_output) =
        npair_pack (nvec_add (npair_left base) period_input)
          (nvec_add (npair_right base) period_output)).
      rewrite <- (npair_pack_split d base) at 1. apply npair_pack_add.
Qed.

Theorem semilinear_nrelation_finite_linear_decomposition : forall d
    (relation : NRelation d),
    SemilinearNRelation relation ->
    exists data : list (LinearRelationData d),
      forall source target,
        relation source target <->
        exists component,
          List.In component data /\
          LinearRelationContains component source target.
Proof.
  intros d relation [code Hcode].
  exists (List.map (@linear_component_relation_data d) code).
  intros source target.
  specialize (Hcode (npair_pack source target)).
  rewrite npair_left_pack, npair_right_pack in Hcode.
  rewrite Hcode. unfold denote. split.
  - intros [component [Hin Hlinear]].
    exists (linear_component_relation_data component). split.
    + now apply in_map.
    + now apply (proj1 (linear_component_relation_data_correct d component source target)).
  - intros [data [Hin Hlinear]].
    apply in_map_iff in Hin as [component [<- Hin]].
    exists component. split; [exact Hin|].
    now apply (proj2 (linear_component_relation_data_correct d component source target)).
Qed.

Definition PlainVASReachRelation {d} (system : PlainVAS d) : NRelation d :=
  fun source target => PlainVASReach system source target.

Theorem plain_vas_reach_inter_semilinear : forall d
    (system : PlainVAS d) (relation : NRelation d),
    SemilinearNRelation relation ->
    AlmostSemilinearNRelation
      (fun source target =>
        relation source target /\ PlainVASReach system source target).
Proof.
  intros d system relation Hsemilinear.
  destruct (semilinear_nrelation_finite_linear_decomposition
    d relation Hsemilinear) as [data Hdata].
  pose (components := List.map
    (fun component => LinearReachRestricted system component) data).
  assert (Hcomponents : List.Forall AlmostSemilinearNRelation components).
  { unfold components. apply List.Forall_forall. intros selected Hin.
    apply in_map_iff in Hin as [component [<- Hin]].
    apply linear_reach_restricted_almost_semilinear. }
  pose proof (almost_semilinear_nrelation_finite_union
    d components Hcomponents) as Hunion.
  eapply almost_semilinear_nrelation_congr; [|exact Hunion].
  intros source target. rewrite Hdata. split.
  - intros [selected [Hin Hselected]].
    unfold components in Hin. apply in_map_iff in Hin as [component [<- Hin]].
    unfold LinearReachRestricted in Hselected.
    destruct Hselected as [Hreach Hlinear].
    split; [exists component; now split|exact Hreach].
  - intros [[component [Hin Hlinear]] Hreach].
    exists (LinearReachRestricted system component). split.
    + unfold components. now apply in_map.
    + now split.
Qed.
