From Coq Require Import Arith Bool Fin Lia List Vector VectorSpec ZArith
  Classical_Prop.
From KruskalAfProp Require Import af.af af.af_tools.
From Mell.Core Require Import Vector.
From Mell.Order Require Import AlmostFullBridge.
From Mell.BVAS Require Import RunOrder.
From Mell.VAS Require Import Runs Intraproductions IntraproductionsLemma57
  ProductionGraph ProductionGraphPaths.

Import ListNotations.

(** Boolean presentation of the bounded-coordinate set. *)
Definition BoundedMask (d : nat) := Vector.t bool d.

Definition MaskOfWitness {d} (witness : NVec d) : BoundedMask d :=
  Vector.map (fun value => Nat.eqb value 0%nat) witness.

Definition ProjectMask {d} (mask : BoundedMask d)
    (configuration : NVec d) : NVec d :=
  Vector.map2 (fun (keep : bool) (value : nat) =>
    if keep then value else 0%nat)
    mask configuration.

Fixpoint all_bounded_masks (d : nat) : list (BoundedMask d) :=
  match d with
  | 0%nat => [@Vector.nil bool]
  | S n =>
      List.map (fun tail => @Vector.cons bool true n tail)
        (all_bounded_masks n) ++
      List.map (fun tail => @Vector.cons bool false n tail)
        (all_bounded_masks n)
  end.

Lemma all_bounded_masks_complete : forall d (mask : BoundedMask d),
    List.In mask (all_bounded_masks d).
Proof.
  intros d mask. induction mask as [|head n tail IH].
  - now left.
  - cbn. apply in_app_iff. destruct head.
    + left. apply in_map. exact IH.
    + right. apply in_map. exact IH.
Qed.

Lemma mask_of_witness_nth : forall d (witness : NVec d) index,
    Vector.nth (MaskOfWitness witness) index =
      Nat.eqb (Vector.nth witness index) 0%nat.
Proof.
  intros. unfold MaskOfWitness.
  rewrite (Vector.nth_map _ _ index index eq_refl). reflexivity.
Qed.

Lemma project_mask_nth : forall d (mask : BoundedMask d)
    (configuration : NVec d) index,
    Vector.nth (ProjectMask mask configuration) index =
      if Vector.nth mask index then Vector.nth configuration index else 0%nat.
Proof.
  intros. unfold ProjectMask.
  rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl).
  reflexivity.
Qed.

Lemma project_bounded_as_mask : forall d (witness configuration : NVec d),
    ProjectBounded witness configuration =
      ProjectMask (MaskOfWitness witness) configuration.
Proof.
  intros. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index other <-. rewrite project_bounded_nth, project_mask_nth,
    mask_of_witness_nth. destruct (Nat.eqb _ _); reflexivity.
Qed.

Lemma mask_of_lemma57_witness_spec : forall d system gamma witness index,
    @Lemma57Witness d system gamma witness ->
    (Vector.nth (MaskOfWitness witness) index = true <->
     BoundedGammaCoordinate system gamma index).
Proof.
  intros d system gamma witness index [_ Hmask].
  rewrite mask_of_witness_nth, Nat.eqb_eq. symmetry. apply Hmask.
Qed.

Lemma same_mask_project_bounded : forall d (left right : NVec d),
    MaskOfWitness left = MaskOfWitness right ->
    forall configuration,
      ProjectBounded left configuration = ProjectBounded right configuration.
Proof.
  intros d left right Hmask configuration.
  repeat rewrite project_bounded_as_mask. now rewrite Hmask.
Qed.

Definition FixedSpecialState {d} (capacity : NVec d)
    (mask : BoundedMask d) : NVec d := ProjectMask mask capacity.

Theorem production_graph_common_special_state : forall d system gamma witness
    capacity mask,
    @Lemma57Witness d system gamma witness ->
    GammaCapacity gamma = capacity -> MaskOfWitness witness = mask ->
    ProductionGraphSpecialState gamma witness =
      FixedSpecialState capacity mask.
Proof.
  intros d system gamma witness capacity mask _ Hcapacity Hmask.
  unfold ProductionGraphSpecialState, FixedSpecialState.
  rewrite project_bounded_as_mask, Hcapacity, Hmask. reflexivity.
Qed.

(** The total projected successor used to compare paths belonging to distinct
    production graphs with the same mask. *)
Definition ProjectedActionTarget {d} (mask : BoundedMask d)
    (source : NVec d) (action : ZVec d) : NVec d :=
  Vector.map2 (fun (keep : bool) (value : Z) =>
    if keep then Z.to_nat value else 0%nat)
    mask (Vector.map2 (fun (value : nat) (delta : Z) => Z.of_nat value + delta)
      source action).

Lemma projected_action_target_nth : forall d mask source action index,
    Vector.nth (@ProjectedActionTarget d mask source action) index =
      if Vector.nth mask index
      then Z.to_nat (Z.of_nat (Vector.nth source index) +
                     Vector.nth action index)
      else 0%nat.
Proof.
  intros. unfold ProjectedActionTarget.
  rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
    (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl).
  reflexivity.
Qed.

Lemma projected_plain_step : forall d system mask source action target,
    @PlainVASStep d system source action target ->
    ProjectedActionTarget mask (ProjectMask mask source) action =
      ProjectMask mask target.
Proof.
  intros d system mask source action target Hstep.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index other <-.
  rewrite projected_action_target_nth, !project_mask_nth.
  destruct (Vector.nth mask index) eqn:Hkeep; [|reflexivity].
  pose proof (proj1 (plain_vas_step_iff d system source action target) Hstep)
    as Hequation.
  pose proof (f_equal (fun value : ZVec d => Vector.nth value index)
    (proj2 Hequation)) as Hcoordinate.
  unfold zvec_add, nvec_to_zvec in Hcoordinate.
  rewrite (Vector.nth_map Z.of_nat _ index index eq_refl),
    (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (Vector.nth_map Z.of_nat _ index index eq_refl) in Hcoordinate.
  rewrite <- Hcoordinate, Nat2Z.id. reflexivity.
Qed.

Lemma production_graph_transition_projected_target : forall d system
    gamma witness mask source action target,
    @ProductionGraphTransition d system gamma witness source action target ->
    MaskOfWitness witness = mask ->
    target = ProjectedActionTarget mask source action.
Proof.
  intros d system gamma witness mask source action target
    [run [q [q' [_ [_ [Hstep [Hsource Htarget]]]]]]] Hmask.
  rewrite Htarget, project_bounded_as_mask, Hmask.
  rewrite Hsource, project_bounded_as_mask, Hmask.
  symmetry. exact (projected_plain_step d system mask q action q' Hstep).
Qed.

Theorem projected_step_deterministic_across_graphs : forall d system
    gamma1 gamma2 witness1 witness2 mask source action target1 target2,
    @ProductionGraphTransition d system gamma1 witness1 source action target1 ->
    ProductionGraphTransition system gamma2 witness2 source action target2 ->
    MaskOfWitness witness1 = mask -> MaskOfWitness witness2 = mask ->
    target1 = target2.
Proof.
  intros d system gamma1 gamma2 witness1 witness2 mask source action
    target1 target2 Hstep1 Hstep2 Hmask1 Hmask2.
  pose proof (production_graph_transition_projected_target d system gamma1
    witness1 mask source action target1 Hstep1 Hmask1) as Ht1.
  pose proof (production_graph_transition_projected_target d system gamma2
    witness2 mask source action target2 Hstep2 Hmask2) as Ht2.
  now rewrite Ht1, Ht2.
Qed.

Lemma projected_step_bounded_coordinate_equation : forall d system gamma
    witness mask source action target (index : Fin.t d),
    @ProductionGraphTransition d system gamma witness source action target ->
    MaskOfWitness witness = mask ->
    Vector.nth mask index = true ->
    Z.of_nat (Vector.nth target index) =
      Z.of_nat (Vector.nth source index) + Vector.nth action index.
Proof.
  intros d system gamma witness mask source action target index Htransition
    Hmask Hbounded.
  destruct Htransition as
    [run [q [q' [_ [_ [Hstep [Hsource Htarget]]]]]]].
  pose proof (proj1 (plain_vas_step_iff d system q action q') Hstep)
    as [_ Hequation].
  pose proof (f_equal (fun value : ZVec d => Vector.nth value index)
    Hequation) as Hcoordinate.
  unfold zvec_add, nvec_to_zvec in Hcoordinate.
  rewrite (Vector.nth_map Z.of_nat _ index index eq_refl),
    (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (Vector.nth_map Z.of_nat _ index index eq_refl) in Hcoordinate.
  rewrite Hsource, Htarget, !project_bounded_as_mask, !Hmask,
    !project_mask_nth, Hbounded.
  exact Hcoordinate.
Qed.

Lemma projected_step_unbounded_coordinate_zero : forall d system gamma
    witness mask source action target (index : Fin.t d),
    @ProductionGraphTransition d system gamma witness source action target ->
    MaskOfWitness witness = mask ->
    Vector.nth mask index = false ->
    Vector.nth source index = 0%nat /\ Vector.nth target index = 0%nat.
Proof.
  intros d system gamma witness mask source action target index Htransition
    Hmask Hunbounded.
  pose proof (production_graph_transition_states d system gamma witness
    source action target Htransition) as
    [[q [Hq Hsource]] [q' [Hq' Htarget]]].
  split.
  - rewrite Hsource, project_bounded_as_mask, Hmask, project_mask_nth,
      Hunbounded. reflexivity.
  - rewrite Htarget, project_bounded_as_mask, Hmask, project_mask_nth,
      Hunbounded. reflexivity.
Qed.

Fixpoint ProjectedWordTarget {d} (mask : BoundedMask d)
    (source : NVec d) (word : list (ZVec d)) : NVec d :=
  match word with
  | [] => source
  | action :: tail =>
      ProjectedWordTarget mask (ProjectedActionTarget mask source action) tail
  end.

Fixpoint ProjectedWordTrace {d} (mask : BoundedMask d)
    (source : NVec d) (word : list (ZVec d)) : list (NVec d) :=
  source ::
  match word with
  | [] => []
  | action :: tail =>
      ProjectedWordTrace mask (ProjectedActionTarget mask source action) tail
  end.

Lemma production_graph_path_projected_target : forall d system gamma witness
    mask source target word,
    @ProductionGraphPath d system gamma witness source target word ->
    MaskOfWitness witness = mask ->
    ProjectedWordTarget mask source word = target.
Proof.
  intros d system gamma witness mask source target word Hpath.
  induction Hpath as [state|source middle target action word
    Htransition Hpath IH]; intro Hmask; cbn; [reflexivity|].
  assert (Hmiddle : ProjectedActionTarget mask source action = middle).
  { symmetry. eapply production_graph_transition_projected_target; eauto. }
  rewrite Hmiddle. now apply IH.
Qed.

Theorem production_graph_word_determines_projected_trace : forall d system
    gamma1 gamma2 witness1 witness2 mask source target1 target2 word,
    @ProductionGraphPath d system gamma1 witness1 source target1 word ->
    ProductionGraphPath system gamma2 witness2 source target2 word ->
    MaskOfWitness witness1 = mask -> MaskOfWitness witness2 = mask ->
    target1 = target2.
Proof.
  intros. rewrite <- (production_graph_path_projected_target
    d system gamma1 witness1 mask source target1 word H H1),
    <- (production_graph_path_projected_target
      d system gamma2 witness2 mask source target2 word H0 H2).
  reflexivity.
Qed.

Theorem production_graph_word_prefix_deterministic_across_graphs : forall d
    system gamma1 gamma2 witness1 witness2 mask source
    prefix middle1 middle2,
    @ProductionGraphPath d system gamma1 witness1 source middle1 prefix ->
    ProductionGraphPath system gamma2 witness2 source middle2 prefix ->
    MaskOfWitness witness1 = mask -> MaskOfWitness witness2 = mask ->
    middle1 = middle2.
Proof.
  intros. eapply production_graph_word_determines_projected_trace; eauto.
Qed.

Definition SimpleProductionGraphPath {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness : NVec d)
    (mask : BoundedMask d) (source target : NVec d)
    (word : list (ZVec d)) : Prop :=
  ProductionGraphPath system gamma witness source target word /\
  NoDup (ProjectedWordTrace mask source word).

Lemma projected_word_trace_length : forall d mask source word,
    length (@ProjectedWordTrace d mask source word) = S (length word).
Proof.
  intros d mask source word. revert source.
  induction word as [|action tail IH]; intro source; cbn; [reflexivity|].
  now rewrite IH.
Qed.

Lemma production_graph_path_trace_states : forall d system gamma witness mask
    source target word,
    @ProductionGraphPath d system gamma witness source target word ->
    MaskOfWitness witness = mask ->
    ProductionGraphState system gamma witness source ->
    forall state,
      List.In state (ProjectedWordTrace mask source word) ->
      ProductionGraphState system gamma witness state.
Proof.
  intros d system gamma witness mask source target word Hpath.
  induction Hpath as [state|source middle target action word
    Htransition Hpath IH]; intros Hmask Hsource state0 Hin; cbn in Hin.
  - destruct Hin as [->|[]].
    exact Hsource.
  - destruct Hin as [->|Hin].
    + exact Hsource.
    + assert (Hmiddle : ProjectedActionTarget mask source action = middle).
      { symmetry. eapply production_graph_transition_projected_target; eauto. }
      rewrite Hmiddle in Hin. apply IH; [exact Hmask| |exact Hin].
      exact (proj2 (production_graph_transition_states d system gamma witness
        source action middle Htransition)).
Qed.

Lemma production_graph_path_trace_suffix : forall d system gamma witness mask
    source target word state,
    @ProductionGraphPath d system gamma witness source target word ->
    MaskOfWitness witness = mask ->
    List.In state (ProjectedWordTrace mask source word) ->
    exists prefix suffix,
      ProductionGraphPath system gamma witness state target suffix /\
      ProjectedWordTrace mask source word =
        prefix ++ ProjectedWordTrace mask state suffix.
Proof.
  intros d system gamma witness mask source target word state Hpath.
  induction Hpath as [current|source middle target action word
    Htransition Hpath IH]; intros Hmask Hin.
  - cbn in Hin. destruct Hin as [->|[]].
    exists [], []. split; [constructor|reflexivity].
  - cbn in Hin |- *.
    assert (Hmiddle : ProjectedActionTarget mask source action = middle).
    { symmetry. eapply production_graph_transition_projected_target; eauto. }
    rewrite Hmiddle in Hin |- *.
    destruct Hin as [Heq|Hin].
    + subst state. exists [], (action :: word). split.
      * econstructor; eauto.
      * cbn. now rewrite Hmiddle.
    + destruct (IH Hmask Hin) as [prefix [suffix [Hsuffix Htrace]]].
      exists (source :: prefix), suffix. split; [exact Hsuffix|].
      cbn. now rewrite Htrace.
Qed.

Theorem production_graph_path_has_simple_subpath : forall d system gamma
    witness mask source target word,
    @ProductionGraphPath d system gamma witness source target word ->
    MaskOfWitness witness = mask ->
    exists simple_word,
      SimpleProductionGraphPath system gamma witness mask
        source target simple_word.
Proof.
  intros d system gamma witness mask source target word Hpath.
  induction Hpath as [state|source middle target action word
    Htransition Hpath IH]; intro Hmask.
  - exists []. split; [constructor|constructor; [intro H; exact H|constructor]].
  - destruct (IH Hmask) as [simple_word [Hsimple_path Hnodup]].
    assert (Hmiddle : ProjectedActionTarget mask source action = middle).
    { symmetry. eapply production_graph_transition_projected_target; eauto. }
    destruct (in_dec nvec_eq_dec source
      (ProjectedWordTrace mask middle simple_word)) as [Hin|Hnotin].
    + destruct (production_graph_path_trace_suffix d system gamma witness mask
        middle target simple_word source Hsimple_path Hmask Hin)
        as [prefix [suffix [Hsuffix Htrace]]].
      exists suffix. split; [exact Hsuffix|].
      rewrite Htrace in Hnodup.
      exact (NoDup_app_remove_l prefix _ Hnodup).
    + exists (action :: simple_word). split.
      * econstructor; eauto.
      * cbn. rewrite Hmiddle. now constructor.
Qed.

Theorem production_graph_simple_path_from_special : forall d system gamma
    witness mask target,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    MaskOfWitness witness = mask ->
    ProductionGraphState system gamma witness target ->
    exists word,
      SimpleProductionGraphPath system gamma witness mask
        (ProductionGraphSpecialState gamma witness) target word.
Proof.
  intros d system gamma witness mask target Hvalid Hw Hmask Htarget.
  destruct (corollary_5_10_production_graph_strongly_connected d system gamma
    witness (ProductionGraphSpecialState gamma witness) target Hvalid Hw
    (production_graph_special_state_member d system gamma witness) Htarget)
    as [word Hpath].
  now apply production_graph_path_has_simple_subpath with (word := word).
Qed.

Fixpoint ForwardBad {X : Type} (relation : X -> X -> Prop)
    (values : list X) : Prop :=
  match values with
  | [] => True
  | value :: tail =>
      (forall later, List.In later tail -> ~ relation value later) /\
      ForwardBad relation tail
  end.

Fixpoint FiniteBranchTrace {X A : Type} (next : X -> A -> X)
    (source : X) (word : list A) : list X :=
  source ::
  match word with
  | [] => []
  | action :: tail => FiniteBranchTrace next (next source action) tail
  end.

Lemma projected_word_trace_finite_branch : forall d mask source word,
    @ProjectedWordTrace d mask source word =
      FiniteBranchTrace (ProjectedActionTarget mask) source word.
Proof.
  intros d mask source word. revert source.
  induction word as [|action tail IH]; intro source; cbn; [reflexivity|].
  now rewrite IH.
Qed.

Lemma forward_bad_lift : forall (X : Type) (relation : X -> X -> Prop)
    pivot values,
    (forall value, List.In value values -> ~ relation pivot value) ->
    ForwardBad relation values ->
    ForwardBad (fun left right =>
      relation left right \/ relation pivot left) values.
Proof.
  intros X relation pivot values. induction values as [|head tail IH];
    intros Hp Hbad; cbn in *; [exact I|].
  destruct Hbad as [Hhead Htail]. split.
  - intros later Hin [Hrel|Hrel].
    + exact (Hhead later Hin Hrel).
    + exact (Hp head (or_introl eq_refl) Hrel).
  - apply IH.
    + intros value Hin. apply Hp. now right.
    + exact Htail.
Qed.

Lemma finite_list_uniform_bound : forall (A : Type) (items : list A)
    (property : A -> nat -> Prop),
    (forall item, List.In item items -> exists bound, property item bound) ->
    exists bound,
      forall item, List.In item items ->
      exists item_bound,
        (item_bound <= bound)%nat /\ property item item_bound.
Proof.
  intros A items. induction items as [|head tail IH]; intros property Hall.
  - exists 0%nat. intros item [].
  - destruct (Hall head (or_introl eq_refl)) as [head_bound Hhead].
    destruct (IH property (fun item Hin => Hall item (or_intror Hin)))
      as [tail_bound Htail].
    exists (Nat.max head_bound tail_bound). intros item [<-|Hin].
    + exists head_bound. split; [apply Nat.le_max_l|exact Hhead].
    + destruct (Htail item Hin) as [item_bound [Hle Hproperty]].
      exists item_bound. split; [eapply Nat.le_trans; [exact Hle|apply Nat.le_max_r]|
        exact Hproperty].
Qed.

Theorem finite_branching_af_bad_paths_bounded : forall
    (X A : Type) (relation : X -> X -> Prop),
    af relation ->
    forall (alphabet : list A) (next : X -> A -> X) root,
    exists bound : nat,
      forall word,
        List.Forall (fun action => List.In action alphabet) word ->
        ForwardBad relation (FiniteBranchTrace next root word) ->
        (List.length word <= bound)%nat.
Proof.
  intros X A relation Haf.
  induction Haf as [relation Hfull|relation Hlift IH];
    intros alphabet next root.
  - exists 0%nat. intros word Hword Hbad.
    destruct word as [|action tail]; cbn; [lia|].
    cbn in Hbad. destruct Hbad as [Hroot _].
    exfalso. apply (Hroot (next root action)).
    + destruct tail; cbn; auto.
    + exact (Hfull root (next root action)).
  - assert (Hper_action : forall action, List.In action alphabet ->
        exists bound,
          forall tail,
            List.Forall (fun label => List.In label alphabet) tail ->
            ForwardBad (fun left right =>
              relation left right \/ relation root left)
              (FiniteBranchTrace next (next root action) tail) ->
            (List.length tail <= bound)%nat).
    { intros action Hin. exact (IH root alphabet next (next root action)). }
    destruct (finite_list_uniform_bound A alphabet
      (fun action bound =>
        forall tail,
          List.Forall (fun label => List.In label alphabet) tail ->
          ForwardBad (fun left right =>
            relation left right \/ relation root left)
            (FiniteBranchTrace next (next root action) tail) ->
          (List.length tail <= bound)%nat) Hper_action)
      as [common Hcommon].
    exists (S common). intros word Hword Hbad.
    destruct word as [|action tail]; cbn; [lia|].
    inversion Hword as [|? ? Haction Htail_labels]; subst.
    cbn in Hbad. destruct Hbad as [Hroot Htail].
    destruct (Hcommon action Haction) as [bound [Hbound Hproperty]].
    assert (Hlifted : ForwardBad
        (fun left right => relation left right \/ relation root left)
        (FiniteBranchTrace next (next root action) tail)).
    { apply forward_bad_lift; [exact Hroot|exact Htail]. }
    specialize (Hproperty tail Htail_labels Hlifted). lia.
Qed.

Lemma production_graph_path_actions : forall d system gamma witness
    source target word,
    @ProductionGraphPath d system gamma witness source target word ->
    List.Forall (fun action => List.In action system) word.
Proof.
  intros d system gamma witness source target word Hpath.
  induction Hpath; constructor; auto.
  now apply production_graph_transition_action with
    (gamma := gamma) (witness := witness)
    (source := source) (target := middle).
Qed.

Lemma forward_bad_of_nodup_antichain : forall (X : Type)
    (relation : X -> X -> Prop) values,
    NoDup values ->
    (forall left right,
      List.In left values -> List.In right values ->
      relation left right -> left = right) ->
    ForwardBad relation values.
Proof.
  intros X relation values. induction values as [|head tail IH];
    intros Hnodup Hanti; cbn; [exact I|].
  inversion Hnodup as [|? ? Hnotin Htail]; subst. split.
  - intros later Hin Hrel. apply Hnotin.
    assert (head = later) by (eapply Hanti; eauto; cbn; tauto).
    now subst.
  - apply IH; [exact Htail|].
    intros left right Hleft Hright Hrel.
    eapply Hanti; eauto; cbn; tauto.
Qed.

Lemma simple_production_graph_path_bad : forall d system gamma witness mask
    source target word,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    MaskOfWitness witness = mask ->
    ProductionGraphState system gamma witness source ->
    SimpleProductionGraphPath system gamma witness mask source target word ->
    ForwardBad nvec_le (ProjectedWordTrace mask source word).
Proof.
  intros d system gamma witness mask source target word Hvalid Hw Hmask
    Hsource [Hpath Hnodup].
  assert (Hstates : forall state,
      List.In state (ProjectedWordTrace mask source word) ->
      ProductionGraphState system gamma witness state).
  { eapply production_graph_path_trace_states; eauto. }
  apply forward_bad_of_nodup_antichain; [exact Hnodup|].
  intros left right Hleft Hright Hle.
  eapply corollary_5_11_projected_states_antichain; eauto.
Qed.

Theorem fixed_mask_simple_path_uniform_bound : forall d
    (system : PlainVAS d) (capacity : NVec d) (mask : BoundedMask d),
    exists bound : nat,
      forall gamma witness word target,
        ValidProductionTriple system gamma ->
        GammaCapacity gamma = capacity ->
        Lemma57Witness system gamma witness ->
        MaskOfWitness witness = mask ->
        SimpleProductionGraphPath system gamma witness mask
          (FixedSpecialState capacity mask) target word ->
        (List.length word <= bound)%nat.
Proof.
  intros d system capacity mask.
  destruct (finite_branching_af_bad_paths_bounded
    (NVec d) (ZVec d) nvec_le (nvec_le_almost_full d)
    system (ProjectedActionTarget mask) (FixedSpecialState capacity mask))
    as [bound Hbound].
  exists bound. intros gamma witness word target Hvalid Hcapacity Hw Hmask
    [Hpath Hnodup].
  apply Hbound.
  - exact (production_graph_path_actions d system gamma witness
      _ _ _ Hpath).
  - rewrite <- projected_word_trace_finite_branch.
    eapply simple_production_graph_path_bad; eauto.
    rewrite <- (production_graph_common_special_state d system gamma witness
      capacity mask Hw Hcapacity Hmask).
    apply production_graph_special_state_member.
    + exact (conj Hpath Hnodup).
Qed.

Fixpoint words_up_to {A : Type} (alphabet : list A) (bound : nat)
    : list (list A) :=
  match bound with
  | 0%nat => [[]]
  | S smaller =>
      [] :: List.flat_map (fun action =>
        List.map (fun word => action :: word)
          (words_up_to alphabet smaller)) alphabet
  end.

Lemma words_up_to_complete : forall (A : Type) (alphabet : list A) word bound,
    List.Forall (fun value => List.In value alphabet) word ->
    (List.length word <= bound)%nat ->
    List.In word (@words_up_to A alphabet bound).
Proof.
  intros A alphabet word. induction word as [|action tail IH];
    intros bound Hall Hlength; destruct bound as [|bound]; cbn in *.
  - now left.
  - now left.
  - lia.
  - inversion Hall as [|? ? Haction Htail]; subst.
    right. apply in_flat_map. exists action. split; [exact Haction|].
    apply in_map. apply IH; [exact Htail|lia].
Qed.

Theorem fixed_mask_production_states_uniform_finite : forall d
    (system : PlainVAS d) (capacity : NVec d) (mask : BoundedMask d),
    exists states : list (NVec d),
      forall gamma witness state,
        ValidProductionTriple system gamma ->
        GammaCapacity gamma = capacity ->
        Lemma57Witness system gamma witness ->
        MaskOfWitness witness = mask ->
        ProductionGraphState system gamma witness state ->
        List.In state states.
Proof.
  intros d system capacity mask.
  destruct (fixed_mask_simple_path_uniform_bound d system capacity mask)
    as [bound Hbound].
  exists (List.map (ProjectedWordTarget mask
    (FixedSpecialState capacity mask)) (words_up_to system bound)).
  intros gamma witness state Hvalid Hcapacity Hw Hmask Hstate.
  destruct (production_graph_simple_path_from_special d system gamma witness
    mask state Hvalid Hw Hmask Hstate) as [word Hsimple].
  assert (Hcommon : ProductionGraphSpecialState gamma witness =
      FixedSpecialState capacity mask).
  { eapply production_graph_common_special_state; eauto. }
  destruct Hsimple as [Hpath Hnodup].
  rewrite Hcommon in Hpath, Hnodup.
  assert (Hlength : (List.length word <= bound)%nat).
  { exact (Hbound gamma witness word state Hvalid Hcapacity Hw Hmask
      (conj Hpath Hnodup)). }
  assert (Hin : List.In word (words_up_to system bound)).
  { apply words_up_to_complete.
    - now apply production_graph_path_actions in Hpath.
    - exact Hlength. }
  apply in_map_iff. exists word. split; [|exact Hin].
  eapply production_graph_path_projected_target; eauto.
Qed.

Lemma finite_list_collect : forall (A B : Type) (items : list A)
    (property : A -> B -> Prop),
    (forall item, List.In item items ->
      exists values : list B,
        forall value, property item value -> List.In value values) ->
    exists values : list B,
      forall item value,
        List.In item items -> property item value -> List.In value values.
Proof.
  intros A B items. induction items as [|head tail IH]; intros property Hall.
  - exists []. intros item value [].
  - destruct (Hall head (or_introl eq_refl)) as [head_values Hhead].
    destruct (IH property (fun item Hin => Hall item (or_intror Hin)))
      as [tail_values Htail].
    exists (head_values ++ tail_values). intros item value [<-|Hin] Hproperty.
    + apply in_or_app. left. now apply Hhead.
    + apply in_or_app. right. eapply Htail; eauto.
Qed.

Theorem fixed_capacity_production_states_uniform_finite : forall d
    (system : PlainVAS d) (capacity : NVec d),
    exists states : list (NVec d),
      forall gamma witness state,
        ValidProductionTriple system gamma ->
        GammaCapacity gamma = capacity ->
        Lemma57Witness system gamma witness ->
        ProductionGraphState system gamma witness state ->
        List.In state states.
Proof.
  intros d system capacity.
  set (property := fun (mask : BoundedMask d) (state : NVec d) =>
    exists gamma witness,
      ValidProductionTriple system gamma /\
      GammaCapacity gamma = capacity /\
      Lemma57Witness system gamma witness /\
      MaskOfWitness witness = mask /\
      ProductionGraphState system gamma witness state).
  assert (Hall : forall mask, List.In mask (all_bounded_masks d) ->
      exists values : list (NVec d),
        forall state, property mask state -> List.In state values).
  { intros mask _.
    destruct (fixed_mask_production_states_uniform_finite
      d system capacity mask) as [values Hvalues].
    exists values. intros state
      [gamma [witness [Hvalid [Hcapacity [Hw [Hmask Hstate]]]]]].
    eapply Hvalues; eauto. }
  destruct (finite_list_collect (BoundedMask d) (NVec d)
    (all_bounded_masks d) property Hall) as [states Hstates].
  exists states. intros gamma witness state Hvalid Hcapacity Hw Hstate.
  eapply Hstates with (item := MaskOfWitness witness).
  - apply all_bounded_masks_complete.
  - unfold property. exists gamma, witness.
    split; [exact Hvalid|]. split; [exact Hcapacity|]. split; [exact Hw|].
    split; [reflexivity|exact Hstate].
Qed.

Theorem fixed_capacity_production_transitions_uniform_finite : forall d
    (system : PlainVAS d) (capacity : NVec d),
    exists edges : list (ProductionGraphEdge d),
      forall gamma witness source action target,
        ValidProductionTriple system gamma ->
        GammaCapacity gamma = capacity ->
        Lemma57Witness system gamma witness ->
        ProductionGraphTransition system gamma witness source action target ->
        List.In
          {| RunEdgeSource := source;
             RunEdgeAction := action;
             RunEdgeTarget := target |} edges.
Proof.
  intros d system capacity.
  destruct (fixed_capacity_production_states_uniform_finite d system capacity)
    as [states Hstates].
  exists (production_graph_edge_candidates states system).
  intros gamma witness source action target Hvalid Hcapacity Hw Htransition.
  apply production_graph_edge_candidates_spec.
  destruct (production_graph_transition_states d system gamma witness
    source action target Htransition) as [Hsource Htarget].
  repeat split.
  - eapply Hstates; eauto.
  - eapply production_graph_transition_action; eauto.
  - eapply Hstates; eauto.
Qed.

Fixpoint list_powerset {A : Type} (values : list A) : list (list A) :=
  match values with
  | [] => [[]]
  | value :: tail =>
      let subsets := list_powerset tail in
      subsets ++ List.map (fun subset => value :: subset) subsets
  end.

Lemma list_powerset_select_predicate : forall (A : Type)
    (predicate : A -> Prop) candidates,
    exists selected,
      List.In selected (list_powerset candidates) /\
      forall value,
        (List.In value selected <->
         List.In value candidates /\ predicate value).
Proof.
  intros A predicate candidates. induction candidates as [|head tail IH].
  - exists []. split; [now left|]. intro value. cbn. tauto.
  - destruct IH as [selected [Hselected Hspec]].
    destruct (classic (predicate head)) as [Hhead|Hhead].
    + exists (head :: selected). split.
      * cbn. apply in_or_app. right. apply in_map. exact Hselected.
      * intro value. cbn. rewrite Hspec. split.
        -- intros [->|[Hin Hpredicate]]; tauto.
        -- intros [[->|Hin] Hpredicate]; tauto.
    + exists selected. split.
      * cbn. apply in_or_app. now left.
      * intro value. rewrite Hspec. cbn. split.
        -- intros [Hin Hpredicate]. tauto.
        -- intros [[Heq|Hin] Hpredicate]; [subst; contradiction|tauto].
Qed.

Record ProductionGraphSignature (d : nat) := {
  SignatureMask : BoundedMask d;
  SignatureStates : list (NVec d);
  SignatureTransitions : list (ProductionGraphEdge d)
}.

Arguments SignatureMask {d} _.
Arguments SignatureStates {d} _.
Arguments SignatureTransitions {d} _.

Definition GraphSignatureRepresents {d}
    (signature : ProductionGraphSignature d)
    (system : PlainVAS d) (gamma : ProductionTriple d)
    (witness : NVec d) : Prop :=
  SignatureMask signature = MaskOfWitness witness /\
  ProductionGraphSpecialState gamma witness =
    FixedSpecialState (GammaCapacity gamma) (SignatureMask signature) /\
  (forall state,
    ProductionGraphState system gamma witness state <->
    List.In state (SignatureStates signature)) /\
  (forall source action target,
    ProductionGraphTransition system gamma witness source action target <->
    List.In
      {| RunEdgeSource := source;
         RunEdgeAction := action;
         RunEdgeTarget := target |}
      (SignatureTransitions signature)).

Definition production_graph_catalog {d}
    (masks : list (BoundedMask d))
    (states : list (NVec d))
    (edges : list (ProductionGraphEdge d)) :
    list (ProductionGraphSignature d) :=
  List.flat_map (fun mask =>
    List.flat_map (fun state_set =>
      List.map (fun edge_set =>
        {| SignatureMask := mask;
           SignatureStates := state_set;
           SignatureTransitions := edge_set |})
        (list_powerset edges))
      (list_powerset states))
    masks.

Lemma production_graph_catalog_member : forall d masks states edges
    mask state_set edge_set,
    List.In mask masks ->
    List.In state_set (list_powerset states) ->
    List.In edge_set (list_powerset edges) ->
    List.In
      {| SignatureMask := mask;
         SignatureStates := state_set;
         SignatureTransitions := edge_set |}
      (@production_graph_catalog d masks states edges).
Proof.
  intros d masks states edges mask state_set edge_set Hmask Hstates Hedges.
  unfold production_graph_catalog. apply in_flat_map. exists mask.
  split; [exact Hmask|]. apply in_flat_map. exists state_set.
  split; [exact Hstates|]. apply in_map. exact Hedges.
Qed.

Theorem graph_signature_witness_independent : forall d system gamma
    left right signature,
    @Lemma57Witness d system gamma left ->
    Lemma57Witness system gamma right ->
    GraphSignatureRepresents signature system gamma left ->
    GraphSignatureRepresents signature system gamma right.
Proof.
  intros d system gamma left right signature Hleft Hright
    [Hmask [Hspecial [Hstates Hedges]]].
  assert (Hmasks : MaskOfWitness left = MaskOfWitness right).
  { apply (proj1 (Vector.eq_nth_iff bool d _ _)).
    intros index other <-.
    repeat rewrite mask_of_witness_nth.
    destruct Hleft as [_ Hl], Hright as [_ Hr].
    destruct (classic (BoundedGammaCoordinate system gamma index)) as [Hb|Hu].
    - now rewrite (proj1 (Hl index) Hb), (proj1 (Hr index) Hb).
    - assert (Hln : Vector.nth left index <> 0%nat).
      { intro Hz. apply Hu, (proj2 (Hl index)), Hz. }
      assert (Hrn : Vector.nth right index <> 0%nat).
      { intro Hz. apply Hu, (proj2 (Hr index)), Hz. }
      apply Nat.eqb_neq in Hln. apply Nat.eqb_neq in Hrn.
      now rewrite Hln, Hrn. }
  split; [now rewrite <- Hmasks|]. split.
  - rewrite <- (production_graph_special_state_witness_independent
      d gamma left right system Hleft Hright). exact Hspecial.
  - split.
    + intro state. rewrite <-
        (production_graph_state_witness_independent d system gamma
          left right Hleft Hright state).
      apply Hstates.
    + intros source action target. rewrite <-
        (production_graph_transition_witness_independent d system gamma
          left right Hleft Hright source action target).
      apply Hedges.
Qed.

Theorem corollary_5_12_production_graph_class_finite : forall d
    (system : PlainVAS d) (capacity : NVec d),
    exists graph_catalog : list (ProductionGraphSignature d),
      forall gamma,
        ValidProductionTriple system gamma ->
        GammaCapacity gamma = capacity ->
        exists witness signature,
          Lemma57Witness system gamma witness /\
          List.In signature graph_catalog /\
          GraphSignatureRepresents signature system gamma witness.
Proof.
  intros d system capacity.
  destruct (fixed_capacity_production_states_uniform_finite d system capacity)
    as [state_universe Hstates_uniform].
  destruct (fixed_capacity_production_transitions_uniform_finite
    d system capacity) as [edge_universe Hedges_uniform].
  exists (production_graph_catalog (all_bounded_masks d)
    state_universe edge_universe).
  intros gamma Hvalid Hcapacity.
  destruct (lemma_5_7_bounded_coordinates_intraproduction
    d system gamma Hvalid) as [witness Hw].
  destruct (list_powerset_select_predicate (NVec d)
    (ProductionGraphState system gamma witness) state_universe)
    as [states [Hstates_power Hstates]].
  set (edge_predicate := fun edge : ProductionGraphEdge d =>
    ProductionGraphTransition system gamma witness
      (RunEdgeSource edge) (RunEdgeAction edge) (RunEdgeTarget edge)).
  destruct (list_powerset_select_predicate (ProductionGraphEdge d)
    edge_predicate edge_universe)
    as [edges [Hedges_power Hedges]].
  set (signature :=
    {| SignatureMask := MaskOfWitness witness;
       SignatureStates := states;
       SignatureTransitions := edges |}).
  exists witness, signature. split; [exact Hw|]. split.
  - apply production_graph_catalog_member.
    + apply all_bounded_masks_complete.
    + exact Hstates_power.
    + exact Hedges_power.
  - unfold signature, GraphSignatureRepresents; cbn.
    split; [reflexivity|]. split.
    + eapply production_graph_common_special_state; eauto; reflexivity.
    + split.
      * intro state. rewrite Hstates. split.
        -- intro Hstate. split; [|exact Hstate].
           eapply Hstates_uniform; eauto.
        -- tauto.
      * intros source action target. rewrite Hedges. unfold edge_predicate.
        split.
        -- intro Hedge. split; [|exact Hedge].
           eapply Hedges_uniform; eauto.
        -- tauto.
Qed.
