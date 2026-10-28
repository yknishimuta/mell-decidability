From Coq Require Import List Vector Lia Arith.PeanoNat Sorting.Permutation.
From KruskalTrees Require Import idx.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Contexts RunOrder.
From Mell.Semilinear Require Import Presentation.
From Mell.VAS Require Import JancarOrder.
From Mell.WSVAS Require Import Runs WitnessAlphabet.

Import ListNotations idx_notations.

Section FreeRuns.
Context {d : nat} (S : IBVAS d).

Fixpoint free_irun_sources (run : IRun d) : list (NVec d) :=
  match run with
  | irun_leaf value => [value]
  | irun_node _ children _ => free_iruns_sources children
  end
with free_iruns_sources (runs : IRuns d) : list (NVec d) :=
  match runs with
  | iruns_nil => []
  | iruns_cons run tail => free_irun_sources run ++ free_iruns_sources tail
  end.

Inductive ValidFreeIRun : IRun d -> Prop :=
| valid_free_leaf : forall value, ValidFreeIRun (irun_leaf value)
| valid_free_node : forall action children target,
    List.In action (system_actions S) ->
    ValidFreeIRuns children ->
    apply_action action (iruns_targets children) = Some target ->
    ValidFreeIRun (irun_node action children target)
with ValidFreeIRuns : IRuns d -> Prop :=
| valid_free_nil : ValidFreeIRuns iruns_nil
| valid_free_cons : forall run runs,
    ValidFreeIRun run -> ValidFreeIRuns runs ->
    ValidFreeIRuns (iruns_cons run runs).

Scheme ValidFreeIRun_ind' := Induction for ValidFreeIRun Sort Prop
with ValidFreeIRuns_ind' := Induction for ValidFreeIRuns Sort Prop.

Lemma free_iruns_sources_append : forall left right,
  free_iruns_sources (iruns_append left right) =
    free_iruns_sources left ++ free_iruns_sources right.
Proof.
  induction left; cbn; intro right; [reflexivity|].
  now rewrite IHleft, app_assoc.
Qed.

Lemma iruns_targets_append_free : forall (left right : IRuns d),
  iruns_targets (iruns_append left right) =
    iruns_targets left ++ iruns_targets right.
Proof.
  induction left; cbn; intro right; [reflexivity|].
  now rewrite IHleft.
Qed.

Lemma valid_free_iruns_append : forall left right,
  ValidFreeIRuns left -> ValidFreeIRuns right ->
  ValidFreeIRuns (iruns_append left right).
Proof.
  intros left right Hleft. induction Hleft; intro Hright; cbn.
  - exact Hright.
  - constructor; auto.
Qed.

Definition AllFreeSources (I : NVec d -> Prop) (runs : IRuns d) : Prop :=
  List.Forall I (free_iruns_sources runs).

Definition SourceShuffle (X I : NVec d -> Prop) (word : list (NVec d)) : Prop :=
  exists prefix special suffix,
    word = prefix ++ special :: suffix /\
    X special /\ List.Forall I prefix /\ List.Forall I suffix.

Definition ReachFromShuffle (X I : NVec d -> Prop) (target : NVec d) : Prop :=
  exists run,
    ValidFreeIRun run /\ irun_target run = target /\
    SourceShuffle X I (free_irun_sources run).

Definition ClosedUnderFreeRuns (I : NVec d -> Prop) : Prop :=
  forall run, ValidFreeIRun run -> List.Forall I (free_irun_sources run) ->
    I (irun_target run).

Inductive MarkedFreeIRun (X I : NVec d -> Prop) : IRun d -> Prop :=
| marked_free_leaf : forall value,
    X value -> MarkedFreeIRun X I (irun_leaf value)
| marked_free_node : forall action before main after target,
    List.In action (system_actions S) ->
    ValidFreeIRuns before -> ValidFreeIRuns after ->
    AllFreeSources I before -> AllFreeSources I after ->
    MarkedFreeIRun X I main ->
    apply_action action
      (iruns_targets (iruns_append before (iruns_cons main after))) = Some target ->
    MarkedFreeIRun X I
      (irun_node action (iruns_append before (iruns_cons main after)) target).

Lemma marked_free_valid : forall X I run,
  MarkedFreeIRun X I run -> ValidFreeIRun run.
Proof.
  intros X I run H. induction H.
  - constructor.
  - constructor; auto. apply valid_free_iruns_append; auto. constructor; auto.
Qed.

Lemma marked_free_source_shuffle : forall X I run,
  MarkedFreeIRun X I run -> SourceShuffle X I (free_irun_sources run).
Proof.
  intros X I run H. induction H.
  - exists [], value, []. cbn. repeat split; auto.
  - destruct IHMarkedFreeIRun as [prefix [special [suffix
      [Hword [HX [Hprefix Hsuffix]]]]]].
    exists (free_iruns_sources before ++ prefix), special,
      (suffix ++ free_iruns_sources after).
    cbn. rewrite free_iruns_sources_append. cbn. rewrite Hword.
    repeat split.
    + repeat rewrite <- app_assoc. reflexivity.
    + exact HX.
    + apply List.Forall_app. split; assumption.
    + apply List.Forall_app. split; assumption.
Qed.

Lemma marked_free_reach_from_shuffle : forall X I run,
  MarkedFreeIRun X I run ->
  ReachFromShuffle X I (irun_target run).
Proof.
  intros X I run H. exists run. split.
  - now apply marked_free_valid with X I.
  - split; [reflexivity|]. now apply marked_free_source_shuffle.
Qed.

Lemma source_shuffle_app_inv : forall X I left right,
  SourceShuffle X I (left ++ right) ->
  (SourceShuffle X I left /\ List.Forall I right) \/
  (List.Forall I left /\ SourceShuffle X I right).
Proof.
  intros X I left. induction left as [|head tail IH]; intros right Hshuffle.
  - right. split; [constructor|exact Hshuffle].
  - destruct Hshuffle as [prefix [special [suffix
      [Hword [HX [Hprefix Hsuffix]]]]]].
    destruct prefix as [|first prefix].
    + cbn in Hword. inversion Hword; subst head suffix.
      apply List.Forall_app in Hsuffix as [Htail Hright]. left. split.
      * exists [], special, tail. repeat split; auto.
      * exact Hright.
    + cbn in Hword. inversion Hword; subst first.
      assert (Htail_shuffle : SourceShuffle X I (tail ++ right)).
      { exists prefix, special, suffix. repeat split; auto.
        now inversion Hprefix. }
      destruct (IH right Htail_shuffle) as [[Hleft Hright]|[Hleft Hright]].
      * left. split; [|exact Hright].
        destruct Hleft as [left_prefix [left_special [left_suffix
          [Heq [HX' [Hpre Hsuf]]]]]].
        exists (head :: left_prefix), left_special, left_suffix.
        split; [cbn; now rewrite Heq|].
        repeat split; auto. constructor; [now inversion Hprefix|exact Hpre].
      * right. split; [|exact Hright].
        constructor; [now inversion Hprefix|exact Hleft].
Qed.

Lemma source_shuffle_singleton : forall X I value,
  SourceShuffle X I [value] -> X value.
Proof.
  intros X I value [prefix [special [suffix
    [Hword [HX [Hprefix Hsuffix]]]]]].
  pose proof (f_equal (@length _) Hword) as Hlength.
  rewrite length_app in Hlength. cbn in Hlength.
  destruct prefix as [|head prefix]; cbn in Hlength; [|lia].
  destruct suffix as [|head suffix]; cbn in Hlength; [|lia].
  now inversion Hword.
Qed.

Definition MarkedFreeIRunsSplit (X I : NVec d -> Prop)
    (runs : IRuns d) : Prop :=
  exists before main after,
    runs = iruns_append before (iruns_cons main after) /\
    ValidFreeIRuns before /\ ValidFreeIRuns after /\
    AllFreeSources I before /\ AllFreeSources I after /\
    MarkedFreeIRun X I main.

Lemma valid_free_source_shuffle_marked : forall X I run,
  ValidFreeIRun run ->
  SourceShuffle X I (free_irun_sources run) ->
  MarkedFreeIRun X I run.
Proof.
  intros X I run Hvalid.
  induction Hvalid using ValidFreeIRun_ind' with
    (P := fun run _ =>
      SourceShuffle X I (free_irun_sources run) -> MarkedFreeIRun X I run)
    (P0 := fun runs _ =>
      SourceShuffle X I (free_iruns_sources runs) ->
      MarkedFreeIRunsSplit X I runs).
  - intro Hshuffle. constructor. exact (source_shuffle_singleton X I value Hshuffle).
  - intro Hshuffle. destruct (IHHvalid Hshuffle)
      as [before [main [after
        [Heq [Hbefore [Hafter [HbeforeI [HafterI Hmain]]]]]]]].
    subst children. econstructor; eauto.
  - intro Hshuffle. destruct Hshuffle as [prefix [special [suffix [Hword _]]]].
    cbn in Hword. symmetry in Hword.
    apply app_eq_nil in Hword as [_ Hcontra]. discriminate.
  - intro Hshuffle. cbn in Hshuffle.
    destruct (source_shuffle_app_inv X I
      (free_irun_sources run) (free_iruns_sources runs) Hshuffle)
      as [[Hrun HtailI]|[HrunI Htail]].
    + exists iruns_nil, run, runs. cbn. repeat split; auto; constructor.
    + destruct (IHHvalid0 Htail) as [before [main [after
        [Heq [Hbefore [Hafter [HbeforeI [HafterI Hmain]]]]]]]].
      exists (iruns_cons run before), main, after. cbn. subst runs.
      repeat split; auto.
      * constructor; assumption.
      * unfold AllFreeSources in *. cbn. apply List.Forall_app; auto.
Qed.

Theorem marked_free_irun_iff_source_shuffle : forall X I run,
  MarkedFreeIRun X I run <->
  ValidFreeIRun run /\ SourceShuffle X I (free_irun_sources run).
Proof.
  intros X I run. split.
  - intro H. split.
    + now apply marked_free_valid with X I.
    + now apply marked_free_source_shuffle.
  - intros [Hvalid Hshuffle].
    now eapply valid_free_source_shuffle_marked.
Qed.

Theorem marked_reach_iff_reach_from_shuffle : forall X I target,
  (exists run, MarkedFreeIRun X I run /\ irun_target run = target) <->
  ReachFromShuffle X I target.
Proof.
  intros X I target. split.
  - intros [run [Hmarked <-]]. now apply marked_free_reach_from_shuffle.
  - intros [run [Hvalid [Htarget Hshuffle]]]. exists run. split; [|assumption].
    apply (proj2 (marked_free_irun_iff_source_shuffle X I run)). auto.
Qed.

End FreeRuns.

Section Simulation.
Context {d : nat} (S : IBVAS d) (code : SemiCode d).

Definition SimulationInvariant (value : NVec d) : Prop :=
  Reach S value \/ denote code value.

Lemma valid_irun_is_free : forall run,
  ValidIRun S run -> ValidFreeIRun S run.
Proof.
  intros run H. induction H using ValidIRun_ind' with
    (P0 := fun runs _ => ValidFreeIRuns S runs); constructor; auto.
Qed.

Lemma nvec_add_comm_sim : forall (left right : NVec d),
  nvec_add left right = nvec_add right left.
Proof.
  intros left right. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros i j Hij; subst j. unfold nvec_add.
  repeat rewrite (Vector.nth_map2 Nat.add _ _ i i i eq_refl eq_refl). lia.
Qed.

Lemma nvec_rsum_perm : forall (left right : list (NVec d)),
  Permutation left right -> nvec_rsum left = nvec_rsum right.
Proof.
  intros left right Hperm. induction Hperm; cbn; auto.
  - now rewrite IHHperm.
  - apply (proj1 (Vector.eq_nth_iff nat d _ _)). intros i j Hij; subst j.
    unfold nvec_add.
    repeat rewrite (Vector.nth_map2 Nat.add _ _ i i i eq_refl eq_refl). lia.
  - now rewrite IHHperm1, IHHperm2.
Qed.

Lemma apply_action_permutation : forall (action : Action d)
    (left right : list (NVec d)) (target : NVec d),
  Permutation left right ->
  apply_action action left = Some target ->
  apply_action action right = Some target.
Proof.
  intros action left right target Hperm Happly.
  unfold apply_action in Happly |- *.
  rewrite <- (Permutation_length Hperm).
  destruct (Nat.eqb (length left) (action_arity action)); [|discriminate].
  unfold add_displacement in Happly |- *.
  rewrite nvec_sum_rsum in Happly |- *.
  rewrite <- (nvec_rsum_perm left right Hperm). exact Happly.
Qed.

Lemma ws_step_star_trans : forall first middle last,
  WSVASStepStar (concrete_wsvas S code) first middle ->
  WSVASStepStar (concrete_wsvas S code) middle last ->
  WSVASStepStar (concrete_wsvas S code) first last.
Proof.
  intros first middle last H. induction H; intro Htail; auto.
  econstructor; eauto.
Qed.

Lemma ws_step_star_snoc : forall first middle last,
  WSVASStepStar (concrete_wsvas S code) first middle ->
  WSVASStep (concrete_wsvas S code) middle last ->
  WSVASStepStar (concrete_wsvas S code) first last.
Proof.
  intros. eapply ws_step_star_trans; [eassumption|].
  econstructor; [eassumption|constructor].
Qed.

Lemma side_targets_in_invariant : forall runs,
  ValidFreeIRuns S runs ->
  List.Forall (SimulationInvariant) (free_iruns_sources runs) ->
  ClosedUnderFreeRuns S (SimulationInvariant) ->
  List.Forall (SimulationInvariant) (iruns_targets runs).
Proof.
  intros runs Hvalid. induction Hvalid; intros Hall Hclosed; cbn in *.
  - constructor.
  - apply List.Forall_app in Hall as [Hrun Htail]. constructor.
    + apply Hclosed; assumption.
    + now apply IHHvalid.
Qed.

Lemma apply_action_length : forall (action : Action d) children target,
  apply_action action children = Some target ->
  length children = action_arity action.
Proof.
  intros action children target Happly. unfold apply_action in Happly.
  destruct (Nat.eqb (length children) (action_arity action)) eqn:Heq;
    [now apply Nat.eqb_eq|discriminate].
Qed.

Lemma action_at_in : forall index : idx (length (system_actions S)),
  List.In (action_at S index) (system_actions S).
Proof.
  intro index. unfold action_at, vas_nth_idx.
  rewrite <- Vector.to_list_of_list_opp.
  apply (proj1 (VectorSpec.to_list_In _ _ _ _)). apply VectorSpec.In_nth.
Qed.

Lemma marked_free_main_path : forall X run,
  MarkedFreeIRun S X (SimulationInvariant) run ->
  ClosedUnderFreeRuns S (SimulationInvariant) ->
  exists source,
    X source /\
    WSVASStepStar (concrete_wsvas S code) source (irun_target run).
Proof.
  intros X run Hmarked.
  induction Hmarked as [value HXvalue | action before main after target
    Haction Hbefore Hafter Hbefore_sources Hafter_sources Hmain IHmain Happly];
    intro Hclosed.
  - exists value. split; [assumption|constructor].
  - destruct (IHmain Hclosed) as [source [HX Hstar]].
    set (side_values := iruns_targets before ++ iruns_targets after).
    assert (Hside : List.Forall (SimulationInvariant) side_values).
    { unfold side_values. apply List.Forall_app. split;
        eapply side_targets_in_invariant; eauto. }
    assert (Hchildren :
      iruns_targets (iruns_append before (iruns_cons main after)) =
        iruns_targets before ++ irun_target main :: iruns_targets after).
    { rewrite iruns_targets_append_free. reflexivity. }
    assert (Hside_length : length side_values = Nat.pred (action_arity action)).
    { pose proof (apply_action_length action _ _ Happly) as Hlength.
      rewrite Hchildren, length_app in Hlength. cbn in Hlength.
      unfold side_values. rewrite length_app.
      pose proof (action_arity_positive action). lia. }
    destruct (vas_nth_idx_occurrence _ (system_actions S) action Haction)
      as [index Hindex].
    unfold action_at in Hindex. destruct Hindex.
    assert (Hstep : BVASSideStep S code (irun_target main) target).
    { exists index, side_values. split; [exact Hside_length|]. split.
      - exact Hside.
      -
      eapply apply_action_permutation; [|exact Happly].
      rewrite Hchildren. apply Permutation_sym.
      eapply Permutation_trans with
        (l' := irun_target main :: iruns_targets before ++ iruns_targets after).
      + apply perm_skip. unfold side_values. apply Permutation_refl.
      + apply Permutation_middle. }
    exists source. split; [exact HX|].
    eapply ws_step_star_snoc; [exact Hstar|].
    apply (proj1 (lemma_5_6_bvas_wsvas_step_iff S code _ _)); exact Hstep.
Qed.

Fixpoint leaf_runs (values : list (NVec d)) : IRuns d :=
  match values with
  | [] => iruns_nil
  | value :: tail => iruns_cons (irun_leaf value) (leaf_runs tail)
  end.

Lemma leaf_runs_targets : forall values,
  iruns_targets (leaf_runs values) = values.
Proof. induction values; cbn; congruence. Qed.

Lemma leaf_runs_sources : forall values,
  free_iruns_sources (leaf_runs values) = values.
Proof. induction values; cbn; congruence. Qed.

Lemma leaf_runs_valid : forall values,
  ValidFreeIRuns S (leaf_runs values).
Proof. induction values; cbn; constructor; auto; constructor. Qed.

Lemma leaf_runs_all : forall I values,
  List.Forall I values -> AllFreeSources I (leaf_runs values).
Proof. intros I values H. unfold AllFreeSources. now rewrite leaf_runs_sources. Qed.

Lemma extend_marked_by_step : forall X main target,
  MarkedFreeIRun S X SimulationInvariant main ->
  BVASSideStep S code (irun_target main) target ->
  exists extended,
    MarkedFreeIRun S X SimulationInvariant extended /\
    irun_target extended = target.
Proof.
  intros X main target Hmain [index [values [Hlength [Hvalues Hstep]]]].
  exists (irun_node (action_at S index)
    (iruns_cons main (leaf_runs values)) target). split; [|reflexivity].
  eapply marked_free_node with (before := iruns_nil) (after := leaf_runs values).
  - apply action_at_in.
  - constructor.
  - apply leaf_runs_valid.
  - constructor.
  - now apply leaf_runs_all.
  - exact Hmain.
  - cbn. now rewrite leaf_runs_targets.
Qed.

Lemma ws_star_extend_marked : forall X source target,
  WSVASStepStar (concrete_wsvas S code) source target ->
  forall run,
    MarkedFreeIRun S X SimulationInvariant run -> irun_target run = source ->
    exists extended,
      MarkedFreeIRun S X SimulationInvariant extended /\
      irun_target extended = target.
Proof.
  intros X source target Hstar. induction Hstar; intros run Hrun Htarget.
  - exists run. split; auto.
  - subst source.
    pose proof (proj2 (lemma_5_6_bvas_wsvas_step_iff S code _ _) H) as Haction.
    destruct (extend_marked_by_step X run middle Hrun
      Haction)
      as [next [Hnext Hnext_target]].
    eapply IHHstar; eauto.
Qed.

Theorem lemma_5_5_marked_bvas_wsvas_reach_iff :
  forall (X : NVec d -> Prop) target,
  ClosedUnderFreeRuns S (SimulationInvariant) ->
  (exists run,
      MarkedFreeIRun S X (SimulationInvariant) run /\
      irun_target run = target) <->
  exists source,
    X source /\
    WSVASStepStar (concrete_wsvas S code) source target.
Proof.
  intros X target Hclosed. split.
  - intros [run [Hmarked <-]]. now apply marked_free_main_path.
  - intros [source [HX Hstar]].
    destruct (ws_star_extend_marked X
      source target Hstar (irun_leaf source)) as [run [Hrun Htarget]].
    + constructor; exact HX.
    + reflexivity.
    + now exists run.
Qed.

Theorem lemma_5_5_bvas_wsvas_reach_iff :
  forall (X : NVec d -> Prop) target,
  ClosedUnderFreeRuns S (SimulationInvariant) ->
  ReachFromShuffle S X (SimulationInvariant) target <->
  exists source,
    X source /\
    WSVASStepStar (concrete_wsvas S code) source target.
Proof.
  intros X target Hclosed.
  rewrite <- (marked_reach_iff_reach_from_shuffle S X SimulationInvariant target).
  now apply lemma_5_5_marked_bvas_wsvas_reach_iff.
Qed.

End Simulation.
