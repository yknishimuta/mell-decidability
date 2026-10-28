From Coq Require Import Arith Fin Lia List Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Semilinear Require Import Presentation.
From Mell.Order Require Import PeriodicOrder.
From Mell.VAS Require Import Runs Intraproductions IntraproductionsLemma57
  ProductionGraph ProductionGraphPaths ProductionGraphFiniteness GraphParikh.

Import ListNotations.
Open Scope Z_scope.

(** Least coordinatewise credit sufficient to execute a fixed action word.
    The definition is backwards: before [a :: w] one needs enough tokens so
    that after [a], the credit required by [w] remains. *)
Fixpoint WordRequiredCredit {d} (word : list (ZVec d)) : NVec d :=
  match word with
  | [] => nvec_zero d
  | action :: tail =>
      Vector.map2
        (fun required delta => Z.to_nat (Z.of_nat required - delta))
        (WordRequiredCredit tail) action
  end.

Definition ApplyVASAction {d} (source : NVec d) (action : ZVec d) : NVec d :=
  Vector.map2 (fun value delta => Z.to_nat (Z.of_nat value + delta))
    source action.

Lemma word_required_credit_step : forall d action tail source,
    nvec_le (@WordRequiredCredit d (action :: tail)) source ->
    (forall index,
      (0 <= Z.of_nat (Vector.nth source index) + Vector.nth action index)%Z) /\
    nvec_le (WordRequiredCredit tail) (ApplyVASAction source action).
Proof.
  intros d action tail source Hle. split; intro index.
  - specialize (Hle index). cbn in Hle. unfold nvec_le, ApplyVASAction in *.
    rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl) in Hle.
    destruct (Z_le_gt_dec 0
      (Z.of_nat (Vector.nth (WordRequiredCredit tail) index) -
       Vector.nth action index)).
    + apply Nat2Z.inj_le in Hle. rewrite Z2Nat.id in Hle by assumption. lia.
    + lia.
  - specialize (Hle index). cbn in Hle. unfold nvec_le, ApplyVASAction in *.
    repeat rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl)
      in Hle |- *.
    assert (Henabled :
      (0 <= Z.of_nat (Vector.nth source index) + Vector.nth action index)%Z).
    { rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl) in Hle.
      destruct (Z_le_gt_dec 0
        (Z.of_nat (Vector.nth (WordRequiredCredit tail) index) -
         Vector.nth action index)).
      - apply Nat2Z.inj_le in Hle. rewrite Z2Nat.id in Hle by assumption. lia.
      - lia. }
    assert (Hneeded :
      (Z.of_nat (Vector.nth (WordRequiredCredit tail) index) <=
       Z.of_nat (Vector.nth source index) + Vector.nth action index)%Z).
    { rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl) in Hle.
      destruct (Z_le_gt_dec 0
        (Z.of_nat (Vector.nth (WordRequiredCredit tail) index) -
         Vector.nth action index)).
      - apply Nat2Z.inj_le in Hle. rewrite Z2Nat.id in Hle by assumption. lia.
      - lia. }
    unfold ApplyVASAction.
    rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl).
    apply Nat2Z.inj_le. rewrite Z2Nat.id by exact Henabled. exact Hneeded.
Qed.
Lemma apply_vas_action_equation : forall d source action,
    (forall index,
      (0 <= Z.of_nat (Vector.nth source index) + Vector.nth action index)%Z) ->
    nvec_to_zvec (@ApplyVASAction d source action) =
      zvec_add (nvec_to_zvec source) action.
Proof.
  intros d source action Henabled.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index other <-.
  unfold ApplyVASAction, nvec_to_zvec, zvec_add.
  rewrite (Vector.nth_map Z.of_nat _ index index eq_refl),
    (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
    (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
    (Vector.nth_map Z.of_nat _ index index eq_refl), Z2Nat.id;
    [reflexivity|apply Henabled].
Qed.

Fixpoint ExecuteVASWord {d} (source : NVec d) (word : list (ZVec d))
    : list (NVec d) :=
  match word with
  | [] => []
  | action :: tail =>
      let target := ApplyVASAction source action in
      target :: ExecuteVASWord target tail
  end.

Lemma execute_vas_word_valid : forall d system word source,
    List.Forall (fun action => List.In action system) word ->
    nvec_le (@WordRequiredCredit d word) source ->
    ValidVASTargets system source (ExecuteVASWord source word).
Proof.
  intros d system word. induction word as [|action tail IH]; intros source Hall Hcredit;
    cbn in *; [exact I|].
  inversion Hall as [|? ? Haction Htail]; subst.
  destruct (word_required_credit_step d action tail source Hcredit)
    as [Henabled Hnext]. split.
  - assert (Heq : action = StepAction source (ApplyVASAction source action)).
    { apply step_equation_action, apply_vas_action_equation, Henabled. }
    now rewrite <- Heq.
  - now apply IH.
Qed.

Lemma execute_vas_word_actions : forall d source word,
    nvec_le (@WordRequiredCredit d word) source ->
    RunActionWord
      {| RunSource := source; RunTargets := @ExecuteVASWord d source word |} = word.
Proof.
  intros d source word. revert source. induction word as [|action tail IH];
    intros source Hcredit; cbn; [reflexivity|].
  destruct (word_required_credit_step d action tail source Hcredit)
    as [Henabled Hnext].
  assert (Heq : StepAction source (ApplyVASAction source action) = action).
  { symmetry. apply step_equation_action, apply_vas_action_equation, Henabled. }
  rewrite Heq. f_equal. now apply IH.
Qed.

Lemma production_graph_path_actions_in_system : forall d system gamma witness
    source target word,
    @ProductionGraphPath d system gamma witness source target word ->
    List.Forall (fun action => List.In action system) word.
Proof.
  intros d system gamma witness source target word Hpath. induction Hpath.
  - constructor.
  - constructor; [eapply production_graph_transition_action; eauto|assumption].
Qed.

Lemma production_graph_path_bounded_credit : forall d system gamma witness
    source target word (index : Fin.t d),
    @ProductionGraphPath d system gamma witness source target word ->
    Vector.nth witness index = 0%nat ->
    (Vector.nth (WordRequiredCredit word) index <=
     Vector.nth source index)%nat.
Proof.
  intros d system gamma witness source target word index Hpath.
  induction Hpath as [state|source middle target action word Hstep Hpath IH];
    intro Hzero; cbn.
  - unfold nvec_zero. rewrite Vector.const_nth. lia.
  - specialize (IH Hzero).
    rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl).
    assert (Hmask : Vector.nth (MaskOfWitness witness) index = true).
    { rewrite mask_of_witness_nth, Nat.eqb_eq. exact Hzero. }
    pose proof (projected_step_bounded_coordinate_equation d system gamma
      witness (MaskOfWitness witness) source action middle index Hstep eq_refl
      Hmask) as Heq.
    destruct (Z_le_gt_dec 0
      (Z.of_nat (Vector.nth (WordRequiredCredit word) index) -
       Vector.nth action index)).
    + apply Nat2Z.inj_le. rewrite Z2Nat.id by assumption. lia.
    + remember (Z.of_nat (Vector.nth (WordRequiredCredit word) index) -
        Vector.nth action index) as deficit eqn:Hdeficit.
      destruct deficit; cbn; lia.
Qed.

Lemma production_graph_special_cycle_credit_bounded : forall d system gamma
    witness word (index : Fin.t d),
    @ProductionGraphPath d system gamma witness
      (ProductionGraphSpecialState gamma witness)
      (ProductionGraphSpecialState gamma witness) word ->
    Vector.nth witness index = 0%nat ->
    (Vector.nth (WordRequiredCredit word) index <=
     Vector.nth (GammaCapacity gamma) index)%nat.
Proof.
  intros d system gamma witness word index Hpath Hzero.
  pose proof (production_graph_path_bounded_credit d system gamma witness
    _ _ word index Hpath Hzero) as Hcredit.
  unfold ProductionGraphSpecialState in Hcredit.
  rewrite project_bounded_nth, Hzero in Hcredit. cbn in Hcredit.
  exact Hcredit.
Qed.

Lemma nvec_coordinate_le_norm : forall d (value : NVec d) (index : Fin.t d),
    (Vector.nth value index <= nvec_norm value)%nat.
Proof.
  intros d value. induction value as [|head d tail IH].
  - intro index. inversion index.
  - intro index. refine (Fin.caseS' index (fun index =>
      (Vector.nth (@Vector.cons nat head d tail) index <=
       nvec_norm (@Vector.cons nat head d tail))%nat) _ _).
    + cbn. lia.
    + intro tail_index. cbn. specialize (IH tail_index). lia.
Qed.

Theorem production_graph_cycle_realizable_after_pumping : forall d system gamma
    witness trace,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    ProductionGraphEdgeTrace system gamma witness
      (ProductionGraphSpecialState gamma witness)
      (ProductionGraphSpecialState gamma witness) trace ->
    exists multiplier run,
      (0 < multiplier)%nat /\
      ValidVASRun system run /\
      RunSource run = nvec_add (GammaCapacity gamma)
        (nvec_scale multiplier witness) /\
      RunActionWord run = GraphTraceActionWord trace /\
      nvec_to_zvec (RunTarget run) =
        zvec_add
          (nvec_to_zvec (nvec_add (GammaCapacity gamma)
            (nvec_scale multiplier witness)))
          (ActionDisplacement (GraphTraceActionWord trace)).
Proof.
  intros d system gamma witness trace Hvalid Hw Htrace.
  pose proof (production_graph_edge_trace_to_path d system gamma witness
    _ _ trace Htrace) as Hpath.
  set (word := GraphTraceActionWord trace).
  set (credit := @WordRequiredCredit d word).
  set (multiplier := S (nvec_norm credit)).
  set (source := nvec_add (GammaCapacity gamma)
    (nvec_scale multiplier witness)).
  assert (Hcredit : nvec_le credit source).
  { intro index. unfold source, credit, multiplier.
    destruct (Nat.eq_dec (Vector.nth witness index) 0%nat) as [Hzero|Hnonzero].
    - pose proof (production_graph_special_cycle_credit_bounded d system gamma
        witness word index Hpath Hzero) as Hbounded.
      unfold nvec_add, nvec_scale.
      rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
        (Vector.nth_map _ _ index index eq_refl), Hzero. lia.
    - pose proof (nvec_coordinate_le_norm d credit index) as Hnorm.
      unfold credit in Hnorm.
      assert (Hpositive : (1 <= Vector.nth witness index)%nat) by lia.
      unfold nvec_add, nvec_scale.
      rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
        (Vector.nth_map _ _ index index eq_refl).
      unfold credit. nia. }
  set (run := {| RunSource := source; RunTargets := ExecuteVASWord source word |}).
  assert (Hactions : List.Forall (fun action => List.In action system) word).
  { exact (production_graph_path_actions_in_system d system gamma witness
      (ProductionGraphSpecialState gamma witness)
      (ProductionGraphSpecialState gamma witness) word Hpath). }
  assert (Hrun : ValidVASRun system run).
  { unfold run. now apply execute_vas_word_valid. }
  assert (Hword : RunActionWord run = word).
  { unfold run. now apply execute_vas_word_actions. }
  exists multiplier, run. repeat split.
  - unfold multiplier. lia.
  - exact Hrun.
  - unfold word in Hword. exact Hword.
  - rewrite (valid_run_target_displacement d system run Hrun).
    rewrite Hword. unfold run, source. cbn. reflexivity.
Qed.
