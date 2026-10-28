From Coq Require Import Lia List Vector VectorSpec.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation Closure LinearEquations.
From Mell.VAS Require Import StatefulVAS SemilinearRelationDecomposition
  Runs Transformer LinearReachRelation AlmostSemilinear AlmostSemilinearProjection
  AlmostSemilinearCoordinateProjection Corollary63.

Import ListNotations.
Module StdVector := Coq.Vectors.Vector.

Definition StatefulRelationSemilinear {d q}
    (relation : SConfig d q -> SConfig d q -> Prop) : Prop :=
  forall source_state target_state,
    SemilinearNRelation (fun source target =>
      relation (source_state, source) (target_state, target)).

Definition StatefulRelationAlmostSemilinear {d q}
    (relation : SConfig d q -> SConfig d q -> Prop) : Prop :=
  forall source_state target_state,
    AlmostSemilinearNRelation (fun source target =>
      relation (source_state, source) (target_state, target)).

Definition StatefulSemilinear {d q} (set : SConfig d q -> Prop) : Prop :=
  forall state, Semilinear (fun counters => set (state, counters)).

Definition StatefulAlmostSemilinear {d q} (set : SConfig d q -> Prop) : Prop :=
  forall state, AlmostSemilinearNSet (fun counters => set (state, counters)).

Definition pad_counter_period {d q} (system : VAS d q) (value : NVec d) :
    NVec (stateful_encoded_dimension d q system) :=
  StdVector.append (StdVector.append value (nvec_zero q))
    (nvec_zero (List.length system)).

Fixpoint lift_generators {d q} (system : VAS d q)
    (generators : list (NVec d * NVec d)) :
    list (NVec (stateful_encoded_dimension d q system) *
          NVec (stateful_encoded_dimension d q system)) :=
  match generators with
  | [] => []
  | generator :: tail =>
      (pad_counter_period system (fst generator),
       pad_counter_period system (snd generator)) ::
      lift_generators system tail
  end.

Definition lift_linear_data {d q} (system : VAS d q)
    (source_state target_state : Fin.t q) (data : LinearRelationData d) :
    LinearRelationData (stateful_encoded_dimension d q system) :=
  {| LinearBaseInput := encode_vas_config system source_state
       (LinearBaseInput data);
     LinearBaseOutput := encode_vas_config system target_state
       (LinearBaseOutput data);
     LinearGenerators := lift_generators system (LinearGenerators data) |}.

Lemma pad_counter_period_zero : forall d q (system : VAS d q),
    pad_counter_period system (nvec_zero d) =
    nvec_zero (stateful_encoded_dimension d q system).
Proof.
  intros. unfold pad_counter_period, stateful_encoded_dimension.
  rewrite <- !nvec_zero_append_local. reflexivity.
Qed.
Lemma pad_counter_period_add : forall d q (system : VAS d q) left right,
    pad_counter_period system (nvec_add left right) =
    nvec_add (pad_counter_period system left) (pad_counter_period system right).
Proof.
  intros. unfold pad_counter_period, stateful_encoded_dimension.
  rewrite !nvec_add_append_local, !nvec_add_zero_right_local. reflexivity.
Qed.

Lemma pad_counter_period_scale : forall d q (system : VAS d q) coefficient value,
    pad_counter_period system (nvec_scale coefficient value) =
    nvec_scale coefficient (pad_counter_period system value).
Proof.
  intros. unfold pad_counter_period, stateful_encoded_dimension.
  rewrite !nvec_scale_append, !nvec_scale_zero_vector. reflexivity.
Qed.

Lemma lifted_coefficients_to_original : forall d q (system : VAS d q)
    generators
    (coefficients : NVec (List.length (lift_generators system generators))),
    exists original : NVec (List.length generators),
      GeneratedInput (lift_generators system generators) coefficients =
        pad_counter_period system (GeneratedInput generators original) /\
      GeneratedOutput (lift_generators system generators) coefficients =
        pad_counter_period system (GeneratedOutput generators original).
Proof.
  intros d q system generators. induction generators as [|[gi go] tail IH];
    intro coefficients.
  - refine (StdVector.case0 (fun coefficients => _) _ coefficients).
    exists (nvec_zero 0). cbn. split; symmetry; apply pad_counter_period_zero.
  - refine (StdVector.caseS' coefficients (fun coefficients => _) _).
    intros coefficient rest. destruct (IH rest) as [original [Hinput Houtput]].
    exists (StdVector.cons nat coefficient _ original).
    change
      (nvec_add (nvec_scale coefficient (pad_counter_period system gi))
        (GeneratedInput (lift_generators system tail) rest) =
       pad_counter_period system
         (nvec_add (nvec_scale coefficient gi) (GeneratedInput tail original)) /\
       nvec_add (nvec_scale coefficient (pad_counter_period system go))
        (GeneratedOutput (lift_generators system tail) rest) =
       pad_counter_period system
         (nvec_add (nvec_scale coefficient go) (GeneratedOutput tail original))).
    split.
    + rewrite Hinput. unfold pad_counter_period, stateful_encoded_dimension.
      rewrite !nvec_scale_append, !nvec_scale_zero_vector,
        !nvec_add_append_local, !nvec_add_zero_right_local. reflexivity.
    + rewrite Houtput. unfold pad_counter_period, stateful_encoded_dimension.
      rewrite !nvec_scale_append, !nvec_scale_zero_vector,
        !nvec_add_append_local, !nvec_add_zero_right_local. reflexivity.
Qed.

Lemma original_coefficients_to_lifted : forall d q (system : VAS d q)
    generators (coefficients : NVec (List.length generators)),
    exists lifted : NVec (List.length (lift_generators system generators)),
      GeneratedInput (lift_generators system generators) lifted =
        pad_counter_period system (GeneratedInput generators coefficients) /\
      GeneratedOutput (lift_generators system generators) lifted =
        pad_counter_period system (GeneratedOutput generators coefficients).
Proof.
  intros d q system generators. induction generators as [|[gi go] tail IH];
    intro coefficients.
  - refine (StdVector.case0 (fun coefficients => _) _ coefficients).
    exists (nvec_zero 0). cbn. split; symmetry; apply pad_counter_period_zero.
  - refine (StdVector.caseS' coefficients (fun coefficients => _) _).
    intros coefficient rest. destruct (IH rest) as [lifted [Hinput Houtput]].
    exists (StdVector.cons nat coefficient _ lifted).
    change
      (nvec_add (nvec_scale coefficient (pad_counter_period system gi))
        (GeneratedInput (lift_generators system tail) lifted) =
       pad_counter_period system
         (nvec_add (nvec_scale coefficient gi) (GeneratedInput tail rest)) /\
       nvec_add (nvec_scale coefficient (pad_counter_period system go))
        (GeneratedOutput (lift_generators system tail) lifted) =
       pad_counter_period system
         (nvec_add (nvec_scale coefficient go) (GeneratedOutput tail rest))).
    split.
    + rewrite Hinput. unfold pad_counter_period, stateful_encoded_dimension.
      rewrite !nvec_scale_append, !nvec_scale_zero_vector,
        !nvec_add_append_local, !nvec_add_zero_right_local. reflexivity.
    + rewrite Houtput. unfold pad_counter_period, stateful_encoded_dimension.
      rewrite !nvec_scale_append, !nvec_scale_zero_vector,
        !nvec_add_append_local, !nvec_add_zero_right_local. reflexivity.
Qed.

Lemma generated_period_pair_map_pad_iff : forall d q (system : VAS d q)
    generators input output,
    GeneratedPeriodPair (lift_generators system generators)
      (pad_counter_period system input) (pad_counter_period system output) <->
    GeneratedPeriodPair generators input output.
Proof.
  intros d q system generators input output. split.
  - intros [coefficients [Hinput Houtput]].
    destruct (lifted_coefficients_to_original d q system generators coefficients)
      as [original [Ei Eo]].
    rewrite Ei in Hinput. rewrite Eo in Houtput.
    apply StdVector.append_inj in Hinput as [Hinput _].
    apply StdVector.append_inj in Hinput as [Hinput _].
    apply StdVector.append_inj in Houtput as [Houtput _].
    apply StdVector.append_inj in Houtput as [Houtput _].
    exists original. now split.
  - intros [coefficients [Hinput Houtput]].
    destruct (original_coefficients_to_lifted d q system generators coefficients)
      as [lifted [Ei Eo]].
    exists lifted. split.
    + transitivity (pad_counter_period system
        (GeneratedInput generators coefficients)).
      * exact Ei.
      * now rewrite Hinput.
    + transitivity (pad_counter_period system
        (GeneratedOutput generators coefficients)).
      * exact Eo.
      * now rewrite Houtput.
Qed.

Lemma encode_config_add_period : forall d q (system : VAS d q) state
    base period,
    nvec_add (encode_vas_config system state base)
      (pad_counter_period system period) =
    encode_vas_config system state (nvec_add base period).
Proof.
  intros. unfold encode_vas_config, pad_counter_period,
    stateful_encoded_dimension. rewrite !nvec_add_append_local,
    !nvec_add_zero_right_local. reflexivity.
Qed.

Lemma lift_linear_data_correct : forall d q (system : VAS d q)
    source_state target_state data source target,
    LinearRelationContains data source target <->
    LinearRelationContains (lift_linear_data system source_state target_state data)
      (encode_vas_config system source_state source)
      (encode_vas_config system target_state target).
Proof.
  intros d q system source_state target_state data source target. split.
  - intros [pi [po [Hperiod [Hs Ht]]]].
    exists (pad_counter_period system pi), (pad_counter_period system po).
    split.
    + cbn [lift_linear_data].
      apply (proj2 (generated_period_pair_map_pad_iff d q system
        (LinearGenerators data) pi po)). exact Hperiod.
    + split; subst; symmetry; apply encode_config_add_period.
  - intros [pi [po [[coefficients [Hpi Hpo]] [Hs Ht]]]].
    cbn [lift_linear_data] in Hs, Ht.
    destruct (lifted_coefficients_to_original d q system
      (LinearGenerators data) coefficients) as [original [Ei Eo]].
    change (GeneratedInput
      (lift_generators system (LinearGenerators data)) coefficients = pi) in Hpi.
    change (GeneratedOutput
      (lift_generators system (LinearGenerators data)) coefficients = po) in Hpo.
    exists (GeneratedInput (LinearGenerators data) original),
      (GeneratedOutput (LinearGenerators data) original). split.
    + exists original. split; reflexivity.
    + split.
      * rewrite Ei in Hpi. rewrite Eo in Hpo.
        rewrite <- Hpi in Hs.
        change (encode_vas_config system source_state source =
          nvec_add (encode_vas_config system source_state (LinearBaseInput data))
            (pad_counter_period system
              (GeneratedInput (LinearGenerators data) original))) in Hs.
        rewrite encode_config_add_period in Hs.
        unfold encode_vas_config in Hs.
        apply StdVector.append_inj in Hs as [Hs _].
        apply StdVector.append_inj in Hs as [Hs _].
        exact Hs.
      * rewrite Ei in Hpi. rewrite Eo in Hpo.
        rewrite <- Hpo in Ht.
        change (encode_vas_config system target_state target =
          nvec_add (encode_vas_config system target_state (LinearBaseOutput data))
            (pad_counter_period system
              (GeneratedOutput (LinearGenerators data) original))) in Ht.
        rewrite encode_config_add_period in Ht.
        unfold encode_vas_config in Ht.
        apply StdVector.append_inj in Ht as [Ht _].
        apply StdVector.append_inj in Ht as [Ht _].
        exact Ht.
Qed.

Lemma lift_linear_data_relation_iff : forall d q (system : VAS d q)
    source_state target_state data encoded_source encoded_target,
    LinearRelationContains
      (lift_linear_data system source_state target_state data)
      encoded_source encoded_target <->
    exists source target,
      LinearRelationContains data source target /\
      encoded_source = encode_vas_config system source_state source /\
      encoded_target = encode_vas_config system target_state target.
Proof.
  intros d q system source_state target_state data encoded_source encoded_target.
  split.
  - intros [pi [po [[coefficients [Hpi Hpo]] [Hs Ht]]]].
    destruct (lifted_coefficients_to_original d q system
      (LinearGenerators data) coefficients) as [original [Ei Eo]].
    change (GeneratedInput
      (lift_generators system (LinearGenerators data)) coefficients = pi) in Hpi.
    change (GeneratedOutput
      (lift_generators system (LinearGenerators data)) coefficients = po) in Hpo.
    rewrite Ei in Hpi. rewrite Eo in Hpo.
    exists (nvec_add (LinearBaseInput data)
        (GeneratedInput (LinearGenerators data) original)),
      (nvec_add (LinearBaseOutput data)
        (GeneratedOutput (LinearGenerators data) original)).
    split.
    + exists (GeneratedInput (LinearGenerators data) original),
        (GeneratedOutput (LinearGenerators data) original).
      repeat split; try reflexivity. exists original. split; reflexivity.
    + split.
      * rewrite <- Hpi in Hs.
        change (encoded_source =
          nvec_add (encode_vas_config system source_state (LinearBaseInput data))
            (pad_counter_period system
              (GeneratedInput (LinearGenerators data) original))) in Hs.
        rewrite encode_config_add_period in Hs. exact Hs.
      * rewrite <- Hpo in Ht.
        change (encoded_target =
          nvec_add (encode_vas_config system target_state (LinearBaseOutput data))
            (pad_counter_period system
              (GeneratedOutput (LinearGenerators data) original))) in Ht.
        rewrite encode_config_add_period in Ht. exact Ht.
  - intros [source [target [Hlinear [Hs Ht]]]]. subst.
    now apply (proj1 (lift_linear_data_correct d q system source_state
      target_state data source target)).
Qed.

Definition linear_data_component {d} (data : LinearRelationData d) :
    LinearComponent (d + d) :=
  (npair_pack (LinearBaseInput data) (LinearBaseOutput data),
   List.map (fun generator => npair_pack (fst generator) (snd generator))
     (LinearGenerators data)).

Lemma split_period_generators_pack : forall d generators,
    split_period_generators
      (List.map (fun generator : NVec d * NVec d =>
        npair_pack (fst generator) (snd generator)) generators) = generators.
Proof.
  intros d generators. induction generators as [|[input output] tail IH]; cbn;
    [reflexivity|]. rewrite IH. unfold npair_left, npair_right.
  now rewrite VectorSpec.splitat_append.
Qed.

Lemma linear_data_component_correct : forall d (data : LinearRelationData d)
    (source target : NVec d),
    linear_denote (linear_data_component data) (npair_pack source target) <->
    LinearRelationContains data source target.
Proof.
  intros d [base_input base_output generators] source target.
  pose proof (linear_component_relation_data_correct d
    (linear_data_component
      {| LinearBaseInput := base_input; LinearBaseOutput := base_output;
         LinearGenerators := generators |}) source target) as H.
  replace (linear_component_relation_data
    (linear_data_component
      {| LinearBaseInput := base_input; LinearBaseOutput := base_output;
         LinearGenerators := generators |})) with
    {| LinearBaseInput := base_input; LinearBaseOutput := base_output;
       LinearGenerators := generators |} in H.
  - exact H.
  - unfold linear_component_relation_data, linear_data_component. cbn.
    rewrite split_period_generators_pack. unfold npair_left, npair_right.
    now rewrite VectorSpec.splitat_append.
Qed.

Lemma finite_linear_relation_union_semilinear : forall d
    (data : list (LinearRelationData d)),
    SemilinearNRelation (fun source target => exists component,
      List.In component data /\ LinearRelationContains component source target).
Proof.
  intros d data. exists (List.map linear_data_component data).
  intros pair. unfold denote. split.
  - intros [item [Hin Hlinear]]. exists (linear_data_component item). split;
      [now apply in_map|].
    pose proof (proj2 (linear_data_component_correct d item _ _) Hlinear) as H.
    now rewrite npair_pack_split in H.
  - intros [component [Hin Hlinear]]. apply in_map_iff in Hin as [item [<- Hin]].
    exists item. split; [exact Hin|].
    apply (proj1 (linear_data_component_correct d item _ _)).
    rewrite npair_pack_split. exact Hlinear.
Qed.

Definition LiftStatePairRelation {d q} (system : VAS d q)
    (source_state target_state : Fin.t q) (relation : NRelation d) :
    NRelation (stateful_encoded_dimension d q system) :=
  fun encoded_source encoded_target => exists source target,
    relation source target /\
    encoded_source = encode_vas_config system source_state source /\
    encoded_target = encode_vas_config system target_state target.

Theorem lift_state_pair_relation_semilinear : forall d q (system : VAS d q)
    source_state target_state relation,
    SemilinearNRelation relation ->
    SemilinearNRelation
      (LiftStatePairRelation system source_state target_state relation).
Proof.
  intros d q system source_state target_state relation Hsemilinear.
  destruct (semilinear_nrelation_finite_linear_decomposition d relation
    Hsemilinear) as [data Hdata].
  pose proof (finite_linear_relation_union_semilinear
    (stateful_encoded_dimension d q system)
    (List.map (lift_linear_data system source_state target_state) data)) as Hlift.
  unfold LiftStatePairRelation.
  destruct Hlift as [code Hcode]. exists code. intro pair.
  rewrite <- Hcode. split.
  - intros [source [target [HR [Hsource Htarget]]]]. subst.
    apply Hdata in HR. destruct HR as [original [Hin Hlinear]].
    exists (lift_linear_data system source_state target_state original). split;
      [now apply in_map|]. apply lift_linear_data_relation_iff.
    now exists source, target.
  - intros [component [Hin Hlinear]].
    apply in_map_iff in Hin as [original [<- Hin]].
    apply lift_linear_data_relation_iff in Hlinear.
    destruct Hlinear as [source [target [Hlinear [Hs Ht]]]].
    exists source, target. repeat split; try assumption.
    now apply (proj2 (Hdata _ _)); exists original.
Qed.

Definition encoded_counter_selection {d q} (system : VAS d q) :
    Fin.t d -> Fin.t (stateful_encoded_dimension d q system) :=
  fun index => Fin.L (List.length system) (Fin.L q index).

Lemma project_lift_state_pair_relation : forall d q (system : VAS d q)
    source_state target_state relation source target,
    ProjectNRelation (encoded_counter_selection system)
      (LiftStatePairRelation system source_state target_state relation)
      source target <-> relation source target.
Proof.
  intros d q system source_state target_state relation source target. split.
  - intros [big_source [big_target
      [[x [y [HR [Esource Etarget]]]] [Hsource Htarget]]]].
    subst. assert (source = x).
    { apply StdVector.eq_nth_iff. intros index index' <-.
      rewrite Hsource. unfold encoded_counter_selection, encode_vas_config,
        stateful_encoded_dimension. repeat rewrite VectorSpec.nth_append_L.
      reflexivity. }
    assert (target = y).
    { apply StdVector.eq_nth_iff. intros index index' <-.
      rewrite Htarget. unfold encoded_counter_selection, encode_vas_config,
        stateful_encoded_dimension. repeat rewrite VectorSpec.nth_append_L.
      reflexivity. }
    now subst.
  - intro HR. exists (encode_vas_config system source_state source),
      (encode_vas_config system target_state target). split.
    + exists source, target. auto.
    + split; intro index; unfold encoded_counter_selection, encode_vas_config,
        stateful_encoded_dimension; repeat rewrite VectorSpec.nth_append_L;
        reflexivity.
Qed.

Lemma project_lift_state_pair_reach : forall d q (system : VAS d q)
    source_state target_state relation source target,
    ProjectNRelation (encoded_counter_selection system)
      (fun encoded_source encoded_target =>
        LiftStatePairRelation system source_state target_state relation
          encoded_source encoded_target /\
        PlainVASReach (erase_vas_states system) encoded_source encoded_target)
      source target <->
    relation source target /\
    VASReach system source_state source target_state target.
Proof.
  intros d q system source_state target_state relation source target. split.
  - intros [big_source [big_target
      [[[x [y [HR [Esource Etarget]]]] Hreach] [Hsource Htarget]]]].
    subst big_source big_target.
    assert (source = x).
    { apply StdVector.eq_nth_iff. intros index index' <-.
      rewrite Hsource. unfold encoded_counter_selection, encode_vas_config,
        stateful_encoded_dimension. repeat rewrite VectorSpec.nth_append_L.
      reflexivity. }
    assert (target = y).
    { apply StdVector.eq_nth_iff. intros index index' <-.
      rewrite Htarget. unfold encoded_counter_selection, encode_vas_config,
        stateful_encoded_dimension. repeat rewrite VectorSpec.nth_append_L.
      reflexivity. }
    subst. split; [exact HR|exact Hreach].
  - intros [HR Hreach].
    exists (encode_vas_config system source_state source),
      (encode_vas_config system target_state target). split.
    + split.
      * exists source, target. auto.
      * exact Hreach.
    + split; intro index; unfold encoded_counter_selection, encode_vas_config,
        stateful_encoded_dimension; repeat rewrite VectorSpec.nth_append_L;
        reflexivity.
Qed.

Theorem state_pair_reach_inter_semilinear : forall d q (system : VAS d q)
    source_state target_state relation,
    SemilinearNRelation relation ->
    AlmostSemilinearNRelation (fun source target =>
      relation source target /\
      VASReach system source_state source target_state target).
Proof.
  intros d q system source_state target_state relation Hsemilinear.
  pose proof (plain_vas_reach_inter_semilinear
    (stateful_encoded_dimension d q system) (erase_vas_states system)
    (LiftStatePairRelation system source_state target_state relation)
    (lift_state_pair_relation_semilinear d q system source_state target_state
      relation Hsemilinear)) as Hbig.
  pose proof (almost_semilinear_nrelation_coordinate_projection
    (stateful_encoded_dimension d q system) d
    (encoded_counter_selection system) _ Hbig) as Hprojected.
  eapply almost_semilinear_nrelation_congr; [|exact Hprojected].
  intros source target. apply project_lift_state_pair_reach.
Qed.

Theorem vas_reach_relation_inter_semilinear :
  forall d q (system : VAS d q)
         (relation : SConfig d q -> SConfig d q -> Prop),
    StatefulRelationSemilinear relation ->
    StatefulRelationAlmostSemilinear
      (fun source target =>
        relation source target /\
        VASReach system (fst source) (snd source)
                   (fst target) (snd target)).
Proof.
  intros d q system relation Hsemilinear source_state target_state.
  cbn.
  apply state_pair_reach_inter_semilinear.
  apply Hsemilinear.
Qed.

Fixpoint fin_collect {A : Type} (q : nat) : (Fin.t q -> A) -> list A :=
  match q return (Fin.t q -> A) -> list A with
  | 0 => fun _ => []
  | S n => fun family =>
      family Fin.F1 :: fin_collect n (fun index => family (Fin.FS index))
  end.

Lemma fin_collect_forall : forall A q (family : Fin.t q -> A) predicate,
    (forall index, predicate (family index)) ->
    List.Forall predicate (fin_collect q family).
Proof.
  intros A q. induction q as [|q IH]; intros family predicate Hall; cbn.
  - constructor.
  - constructor; [apply Hall|]. apply IH. intro index. apply Hall.
Qed.

Lemma fin_collect_union_iff : forall d q
    (family : Fin.t q -> NVec d -> Prop) value,
    (exists set, List.In set (fin_collect q family) /\ set value) <->
    exists index, family index value.
Proof.
  intros d q. induction q as [|q IH]; intros family value; cbn.
  - split; intros [witness H]; [destruct H as [Hin _]; inversion Hin|].
    refine (Fin.case0 _ witness).
  - split.
    + intros [set [[<-|Hin] Hset]].
      * exists Fin.F1. exact Hset.
      * assert (Hmember : exists set,
            List.In set
              (fin_collect q (fun index => family (Fin.FS index))) /\
            set value).
        { exists set. now split. }
        apply (proj1 (IH (fun index => family (Fin.FS index)) value)) in
          Hmember as Htail.
        destruct Htail as [index Hindex]. exists (Fin.FS index). exact Hindex.
    + intros [index Hindex].
      refine (Fin.caseS' index (fun index =>
        family index value -> exists set,
          List.In set
            (family Fin.F1 ::
             fin_collect q (fun tail_index => family (Fin.FS tail_index))) /\
          set value) _ _ Hindex).
      * exists (family Fin.F1). now split; [left|].
      * intros tail_index Htail.
        assert (Hexists : exists index,
            family (Fin.FS index) value).
        { now exists tail_index. }
        apply (proj2 (IH (fun index => family (Fin.FS index)) value)) in
          Hexists as Hmember.
        destruct Hmember as [set [Hin Hset]].
        exists set. now split; [right|].
Qed.

Definition StatefulPostSlice {d q} (system : VAS d q)
    (source_set target_set : SConfig d q -> Prop)
    (source_state target_state : Fin.t q) : NVec d -> Prop :=
  fun target => target_set (target_state, target) /\
    exists source,
      source_set (source_state, source) /\
      VASReach system source_state source target_state target.

Lemma state_pair_post_inter_almost_semilinear : forall d q
    (system : VAS d q) (source_set target_set : SConfig d q -> Prop)
    source_state target_state,
    Semilinear (fun source => source_set (source_state, source)) ->
    Semilinear (fun target => target_set (target_state, target)) ->
    AlmostSemilinearNSet
      (StatefulPostSlice system source_set target_set source_state target_state).
Proof.
  intros d q system source_set target_set source_state target_state
    Hsource Htarget.
  pose proof (state_pair_reach_inter_semilinear d q system source_state
    target_state
    (NSetProductRelation (fun source => source_set (source_state, source))
      (fun target => target_set (target_state, target)))
    (semilinear_nset_product_relation d _ _ Hsource Htarget)) as Hrelation.
  pose proof (almost_semilinear_nrelation_target_projection d _ Hrelation)
    as Hprojection.
  eapply almost_semilinear_nset_congr; [|exact Hprojection].
  intro target. unfold NRelationTargetProjection, NSetProductRelation,
    StatefulPostSlice. split.
  - intros [source [[Hsource' Htarget'] Hreach]].
    split; [exact Htarget'|]. exists source. now split.
  - intros [Htarget' [source [Hsource' Hreach]]].
    exists source. repeat split; assumption.
Qed.

Theorem vas_post_inter_semilinear :
  forall d q (system : VAS d q)
         (source_set target_set : SConfig d q -> Prop),
    StatefulSemilinear source_set ->
    StatefulSemilinear target_set ->
    StatefulAlmostSemilinear
      (fun target =>
        target_set target /\
        exists source,
          source_set source /\
          VASReach system (fst source) (snd source)
                     (fst target) (snd target)).
Proof.
  intros d q system source_set target_set Hsource Htarget target_state.
  set (family := fun source_state : Fin.t q =>
    StatefulPostSlice system source_set target_set source_state target_state).
  assert (Hfamily : List.Forall AlmostSemilinearNSet
      (fin_collect q family)).
  { apply fin_collect_forall. intro source_state. unfold family.
    apply state_pair_post_inter_almost_semilinear;
      [apply Hsource|apply Htarget]. }
  pose proof (almost_semilinear_nset_finite_union d
    (fin_collect q family) Hfamily) as Hunion.
  eapply almost_semilinear_nset_congr; [|exact Hunion].
  intro target. rewrite fin_collect_union_iff. unfold family,
    StatefulPostSlice. cbn. split.
  - intros [source_state [Htarget' [source [Hsource' Hreach]]]].
    split; [exact Htarget'|]. exists (source_state, source). cbn.
    now split.
  - intros [Htarget' [[source_state source] [Hsource' Hreach]]].
    exists source_state. split; [exact Htarget'|].
    exists source. now split.
Qed.
