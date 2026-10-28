From Coq Require Import List Vector ZArith Arith.PeanoNat Program.Equality Lia.
From KruskalTrees Require Import idx.
From KruskalAfProp Require Import af.af af.af_tools.
From KruskalHigmanProp Require Import embeddings.list_embed af.af_list_embed.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Order Require Import AlmostFullBridge.
From Mell.VAS Require Import Runs.

Import ListNotations idx_notations.

Definition ActionConfiguration (d : nat) := (ZVec d * NVec d)%type.

Definition ActionConfigurationLe {d : nat} :
    ActionConfiguration d -> ActionConfiguration d -> Prop :=
  fun left right => fst left = fst right /\ nvec_le (snd left) (snd right).

Definition RunAnnotatedWord {d} (run : VASRun d) :
    list (ActionConfiguration d) := RunSteps run.

Definition RunDirectionLe {d} (left right : VASRun d) : Prop :=
  nvec_le (RunSource left) (RunSource right) /\
  nvec_le (RunTarget left) (RunTarget right).

Fixpoint TraceTarget {d} (source : NVec d)
    (steps : list (ActionConfiguration d)) : NVec d :=
  match steps with [] => source | (_, target) :: tail => TraceTarget target tail end.

Fixpoint ConnectedTrace {d} (source : NVec d)
    (steps : list (ActionConfiguration d)) : Prop :=
  match steps with
  | [] => True
  | (action, target) :: tail =>
      action = StepAction source target /\ ConnectedTrace target tail
  end.

(** The paper's operational definition: [gap] is the additional subrun
    before the next matched transition, and [offset] is its nonnegative
    endpoint offset.  The final constructor supplies the last gap. *)
Inductive JancarGapDecomposition {d} :
    NVec d -> list (ActionConfiguration d) ->
    NVec d -> list (ActionConfiguration d) -> Prop :=
| jancar_gap_final : forall small_current big_current gap final_offset,
    TraceTarget big_current gap = nvec_add small_current final_offset ->
    JancarGapDecomposition small_current [] big_current gap
| jancar_gap_match : forall small_current action small_target small_tail
    big_current gap offset big_tail,
    TraceTarget big_current gap = nvec_add small_current offset ->
    JancarGapDecomposition small_target small_tail
      (nvec_add small_target offset) big_tail ->
    JancarGapDecomposition small_current
      ((action, small_target) :: small_tail) big_current
      (gap ++ (action, nvec_add small_target offset) :: big_tail).

Definition JancarRunLe {d} (left right : VASRun d) : Prop :=
  exists initial_offset,
    RunSource right = nvec_add (RunSource left) initial_offset /\
    JancarGapDecomposition (RunSource left) (RunAnnotatedWord left)
      (RunSource right) (RunAnnotatedWord right).

Definition HigmanRunEmbed {d} :
    list (ActionConfiguration d) -> list (ActionConfiguration d) -> Prop :=
  list_embed ActionConfigurationLe.

Lemma trace_target_app : forall d source left right,
    @TraceTarget d source (left ++ right) =
    TraceTarget (TraceTarget source left) right.
Proof. intros d source left; revert source; induction left as [|[]]; cbn; auto. Qed.

Lemma connected_trace_app : forall d source left right,
    @ConnectedTrace d source (left ++ right) <->
    ConnectedTrace source left /\ ConnectedTrace (TraceTarget source left) right.
Proof.
  intros d source left; revert source.
  induction left as [|[action target] tail IH]; intros source right; cbn.
  - tauto.
  - rewrite IH. tauto.
Qed.

Lemma run_annotated_connected : forall d (run : VASRun d),
    ConnectedTrace (RunSource run) (RunAnnotatedWord run).
Proof.
  intros d [source targets]; cbn. revert source.
  induction targets; intros; cbn; auto.
Qed.

Lemma run_annotated_target : forall d (run : VASRun d),
    TraceTarget (RunSource run) (RunAnnotatedWord run) = RunTarget run.
Proof.
  intros d [source targets]; cbn. revert source.
  induction targets; intros; cbn; auto.
Qed.

Lemma gap_decomposition_higman : forall d small steps big big_steps,
    @JancarGapDecomposition d small steps big big_steps ->
    HigmanRunEmbed steps big_steps.
Proof.
  intros d small steps big big_steps H. induction H.
  - apply list_embed_nil_any.
  - apply list_embed_left. constructor.
    + split; [reflexivity|apply nvec_le_add_right].
    + exact IHJancarGapDecomposition.
Qed.

Lemma gap_decomposition_final_offset : forall d small steps big big_steps,
    @JancarGapDecomposition d small steps big big_steps ->
    exists offset,
      TraceTarget big big_steps =
      nvec_add (TraceTarget small steps) offset.
Proof.
  intros d small steps big big_steps H. induction H.
  - now exists final_offset.
  - destruct IHJancarGapDecomposition as [last Hlast].
    exists last. rewrite trace_target_app; cbn. exact Hlast.
Qed.

Lemma connected_trace_match : forall d source prefix action target suffix,
    @ConnectedTrace d source (prefix ++ (action, target) :: suffix) ->
    action = StepAction (TraceTarget source prefix) target /\
    ConnectedTrace target suffix.
Proof.
  intros d source prefix action target suffix H.
  apply connected_trace_app in H. destruct H as [_ H]. cbn in H. exact H.
Qed.

Lemma step_action_source_deterministic : forall d left right target,
    @StepAction d left target = StepAction right target -> left = right.
Proof.
  intros d left right target H.
  apply nvec_to_zvec_injective.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros i j Hij; subst j.
  pose proof (f_equal (fun value : ZVec d => Vector.nth value i) H) as Hnth.
  unfold StepAction, zvec_sub_run, nvec_to_zvec in Hnth |- *.
  repeat rewrite (nth_map2 Z.sub _ _ i i i eq_refl eq_refl) in Hnth.
  repeat rewrite (nth_map Z.of_nat _ i i eq_refl) in Hnth |- *.
  lia.
Qed.

Lemma nvec_le_offset_witness : forall d (left right : NVec d),
    nvec_le left right -> exists offset, right = nvec_add left offset.
Proof.
  intros d left right Hle.
  exists (Vector.map2 Nat.sub right left).
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Hindex; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  rewrite (nth_map2 Nat.sub _ _ index index index eq_refl eq_refl).
  specialize (Hle index). lia.
Qed.

Lemma higman_gap_decomposition : forall d small_steps big_steps small big,
    @ConnectedTrace d small small_steps -> ConnectedTrace big big_steps ->
    nvec_le small big ->
    nvec_le (TraceTarget small small_steps) (TraceTarget big big_steps) ->
    HigmanRunEmbed small_steps big_steps ->
    JancarGapDecomposition small small_steps big big_steps.
Proof.
  intros d small_steps. induction small_steps as [|[action target] tail IH];
    intros big_steps small big Hsmall Hbig Hsource Htarget Hembed.
  - destruct (nvec_le_offset_witness d small (TraceTarget big big_steps) Htarget)
      as [offset Hoff]. econstructor. exact Hoff.
  - destruct (list_embed_cons_inv Hembed)
      as [prefix [[big_action big_target] [suffix [Hsplit [Hhead Htail]]]]].
    subst big_steps. cbn in Hsmall. destruct Hsmall as [Hsmall_action Hsmall_tail].
    destruct Hhead as [Haction Hmatched]. cbn in Haction, Hmatched.
    destruct (nvec_le_offset_witness d target big_target Hmatched)
      as [offset Hoffset].
    assert (Hbig_match := Hbig).
    apply connected_trace_match in Hbig_match.
    destruct Hbig_match as [Hbig_action Hbig_tail].
    assert (Hpredecessor : TraceTarget big prefix = nvec_add small offset).
    { apply step_action_source_deterministic with (target := big_target).
      rewrite <- Hbig_action, <- Haction, Hsmall_action, Hoffset.
      symmetry. apply step_action_shift. }
    subst big_action. subst big_target.
    econstructor 2 with (gap := prefix) (offset := offset) (big_tail := suffix).
    + exact Hpredecessor.
    + apply IH.
      * exact Hsmall_tail.
      * exact Hbig_tail.
      * exact Hmatched.
      * rewrite trace_target_app in Htarget. cbn in Htarget. exact Htarget.
      * exact Htail.
Qed.

Theorem jancar_run_le_iff_higman : forall d (left right : VASRun d),
    JancarRunLe left right <->
    RunDirectionLe left right /\
    HigmanRunEmbed (RunAnnotatedWord left) (RunAnnotatedWord right).
Proof.
  intros d left right. split.
  - intros [initial [Hsource Hgap]]. split.
    + split.
      * rewrite Hsource. apply nvec_le_add_right.
      * destruct (gap_decomposition_final_offset _ _ _ _ _ Hgap)
          as [final Hfinal].
        rewrite run_annotated_target in Hfinal.
        rewrite run_annotated_target in Hfinal. rewrite Hfinal.
        apply nvec_le_add_right.
    + now apply gap_decomposition_higman in Hgap.
  - intros [[Hsource Htarget] Hembed].
    destruct (nvec_le_offset_witness d _ _ Hsource) as [initial Hinitial].
    exists initial. split; [exact Hinitial|].
    apply higman_gap_decomposition.
    + apply run_annotated_connected.
    + apply run_annotated_connected.
    + exact Hsource.
    + now rewrite !run_annotated_target.
    + exact Hembed.
Qed.

Lemma list_embed_refl_local : forall X (R : X -> X -> Prop),
    (forall x, R x x) -> forall values, list_embed R values values.
Proof.
  intros X R Hrefl values. induction values; constructor; auto.
Qed.

Lemma list_embed_trans_local : forall X (R : X -> X -> Prop),
    (forall x y z, R x y -> R y z -> R x z) ->
    forall left middle right,
      list_embed R left middle -> list_embed R middle right ->
      list_embed R left right.
Proof.
  intros X R Htrans left middle right Hlm Hmr.
  revert left Hlm. induction Hmr as
      [|middle_head middle_tail right_head right_tail Hhead Htail IH
       |middle_tail right_head right_tail Htail IH];
    intros left Hlm.
  - inversion Hlm. constructor.
  - inversion Hlm as [|left_head left_tail ? ? Hleft_head Hleft_tail
      |? skipped_head skipped_tail Hskip]; subst.
    + constructor.
      * eapply Htrans; eauto.
      * now apply IH.
    + constructor 3. now apply IH.
  - constructor 3. now apply IH.
Qed.

Lemma action_configuration_le_refl : forall d
    (value : ActionConfiguration d), ActionConfigurationLe value value.
Proof. intros d [action configuration]. split; [reflexivity|apply nvec_le_refl]. Qed.

Lemma action_configuration_le_trans : forall d
    (x y z : ActionConfiguration d),
    ActionConfigurationLe x y -> ActionConfigurationLe y z ->
    ActionConfigurationLe x z.
Proof.
  intros d [xa xc] [ya yc] [za zc].
  unfold ActionConfigurationLe; cbn.
  intros [Hxy Hxyc] [Hyz Hyzc].
  split; [congruence|eapply nvec_le_trans; eauto].
Qed.

Lemma jancar_run_le_refl : forall d (run : VASRun d), JancarRunLe run run.
Proof.
  intros d run. apply jancar_run_le_iff_higman. split.
  - split; apply nvec_le_refl.
  - apply list_embed_refl_local. apply action_configuration_le_refl.
Qed.

Lemma jancar_run_le_trans : forall d (x y z : VASRun d),
    JancarRunLe x y -> JancarRunLe y z -> JancarRunLe x z.
Proof.
  intros d x y z Hxy Hyz.
  apply jancar_run_le_iff_higman in Hxy.
  apply jancar_run_le_iff_higman in Hyz.
  apply jancar_run_le_iff_higman. destruct Hxy as [[Hxs Hxt] Hxw].
  destruct Hyz as [[Hys Hyt] Hyw]. split.
  - split; eapply nvec_le_trans; eauto.
  - eapply list_embed_trans_local; eauto using action_configuration_le_trans.
Qed.

Lemma nvec_le_exists_offset : forall d (left right : NVec d),
    nvec_le left right -> exists offset, right = nvec_add left offset.
Proof.
  intros d left right Hle.
  exists (Vector.map2 Nat.sub right left).
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Hindex; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  rewrite (nth_map2 Nat.sub _ _ index index index eq_refl eq_refl).
  specialize (Hle index). lia.
Qed.

Lemma jancar_direction_offsets : forall d (left right : VASRun d),
    JancarRunLe left right ->
    exists source_offset target_offset,
      RunSource right = nvec_add (RunSource left) source_offset /\
      RunTarget right = nvec_add (RunTarget left) target_offset.
Proof.
  intros d left right Hle. apply jancar_run_le_iff_higman in Hle.
  destruct Hle as [[Hsource Htarget] _].
  destruct (nvec_le_exists_offset _ _ _ Hsource) as [so Hso].
  destruct (nvec_le_exists_offset _ _ _ Htarget) as [to Hto].
  now exists so, to.
Qed.

(** Finite action positions are used only in the WQO proof.  The public
    alphabet compares actual action values, so duplicate positions denoting
    the same action are never distinguished by [JancarRunLe]. *)
Fixpoint vas_idx_to_fin {n} (index : idx n) : Fin.t n :=
  match index with
  | idx_fst => Fin.F1
  | idx_nxt tail => Fin.FS (vas_idx_to_fin tail)
  end.

Definition vas_nth_idx {A} (values : list A)
    (index : idx (length values)) : A :=
  Vector.nth (Vector.of_list values) (vas_idx_to_fin index).

Lemma vas_nth_idx_occurrence : forall A (values : list A) value,
    List.In value values -> exists index, vas_nth_idx values index = value.
Proof.
  intros A values. induction values as [|head tail IH]; intros value Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + exists idx_fst. reflexivity.
    + destruct (IH value Hin) as [index Hindex].
      exists (idx_nxt index). exact Hindex.
Qed.

Definition EncodedActionConfiguration {d} (system : PlainVAS d) :=
  (idx (length system) * NVec d)%type.

Definition EncodedActionConfigurationLe {d} (system : PlainVAS d) :
    EncodedActionConfiguration system -> EncodedActionConfiguration system -> Prop :=
  fun left right => fst left = fst right /\ nvec_le (snd left) (snd right).

Definition EncodedRun {d} (system : PlainVAS d) :=
  (NVec d * (NVec d * list (EncodedActionConfiguration system)))%type.

Definition EncodedRunLe {d} (system : PlainVAS d) :
    EncodedRun system -> EncodedRun system -> Prop :=
  fun left right =>
    nvec_le (fst left) (fst right) /\
    nvec_le (fst (snd left)) (fst (snd right)) /\
    list_embed (EncodedActionConfigurationLe system)
      (snd (snd left)) (snd (snd right)).

Definition DecodeVASWord {d} (system : PlainVAS d)
    (encoded : list (EncodedActionConfiguration system)) :
    list (ActionConfiguration d) :=
  List.map (fun item => (vas_nth_idx system (fst item), snd item)) encoded.

Definition DecoratesVASWord {d} (system : PlainVAS d)
    (encoded : list (EncodedActionConfiguration system))
    (annotated : list (ActionConfiguration d)) : Prop :=
  DecodeVASWord system encoded = annotated.

Definition DecoratesVASRun {d} (system : PlainVAS d)
    (encoded : EncodedRun system) (run : VASRun d) : Prop :=
  fst encoded = RunSource run /\
  fst (snd encoded) = RunTarget run /\
  DecoratesVASWord system (snd (snd encoded)) (RunAnnotatedWord run).

Lemma valid_steps_decorated : forall d (system : PlainVAS d) source targets,
    ValidVASTargets system source targets ->
    exists encoded,
      DecoratesVASWord system encoded (steps_of_targets source targets).
Proof.
  intros d system source targets. revert source.
  induction targets as [|target tail IH]; intros source Hvalid.
  - exists []. reflexivity.
  - cbn in Hvalid. destruct Hvalid as [Hin Htail].
    destruct (vas_nth_idx_occurrence _ system (StepAction source target) Hin)
      as [index Hindex].
    destruct (IH target Htail) as [encoded Hencoded].
    exists ((index, target) :: encoded).
    unfold DecoratesVASWord, DecodeVASWord in *. cbn.
    now rewrite Hindex, Hencoded.
Qed.

Lemma valid_run_decorated : forall d (system : PlainVAS d) run,
    ValidVASRun system run ->
    exists encoded, DecoratesVASRun system encoded run.
Proof.
  intros d system run Hvalid.
  destruct (valid_steps_decorated d system (RunSource run)
    (RunTargets run) Hvalid) as [word Hword].
  exists (RunSource run, (RunTarget run, word)). repeat split; auto.
Qed.

Lemma decorated_word_embedding : forall d (system : PlainVAS d)
    left_code right_code left_word right_word,
    DecoratesVASWord system left_code left_word ->
    DecoratesVASWord system right_code right_word ->
    list_embed (EncodedActionConfigurationLe system) left_code right_code ->
    HigmanRunEmbed left_word right_word.
Proof.
  intros d system left_code right_code left_word right_word
    Hleft Hright Hembed. rewrite <- Hleft, <- Hright. clear Hleft Hright.
  unfold HigmanRunEmbed, DecodeVASWord in *.
  induction Hembed as
      [|[li lc] lt [ri rc] rt Hhead Htail IH
       |lt [ri rc] rt Htail IH]; cbn.
  - constructor.
  - unfold EncodedActionConfigurationLe in Hhead; cbn in Hhead.
    destruct Hhead as [Hindex Hconfig]. subst ri.
    constructor; [now split|exact IH].
  - constructor 3. exact IH.
Qed.

Lemma encoded_run_embedding : forall d (system : PlainVAS d)
    left_code right_code left right,
    DecoratesVASRun system left_code left ->
    DecoratesVASRun system right_code right ->
    EncodedRunLe system left_code right_code ->
    JancarRunLe left right.
Proof.
  intros d system [ls [lt lw]] [rs [rt rw]] left right
    [Hls [Hlt Hlw]] [Hrs [Hrt Hrw]] [Hs [Ht Hw]]; cbn in *.
  subst ls lt rs rt. apply jancar_run_le_iff_higman. split.
  - split; assumption.
  - eapply decorated_word_embedding; eauto.
Qed.

Lemma encoded_action_configuration_almost_full : forall d system,
    af (@EncodedActionConfigurationLe d system).
Proof.
  intros d system. unfold EncodedActionConfigurationLe.
  eapply af_mono; [|exact
    (af_product (af_idx (length system)) (nvec_le_almost_full d))].
  intros [li lc] [ri rc]; cbn. tauto.
Qed.

Lemma encoded_run_almost_full : forall d system,
    af (@EncodedRunLe d system).
Proof.
  intros d system. unfold EncodedRunLe.
  pose proof (af_list_embed
    (encoded_action_configuration_almost_full d system)) as Hword.
  pose proof (af_product (nvec_le_almost_full d) Hword) as Htail.
  pose proof (af_product (nvec_le_almost_full d) Htail) as Hall.
  eapply af_mono; [|exact Hall].
  intros [ls [lt lw]] [rs [rt rw]]; cbn. tauto.
Qed.

Theorem jancar_run_wqo : forall d (system : PlainVAS d),
    afs (ValidVASRun system) (@JancarRunLe d).
Proof.
  intros d system. apply af_sub_rel_afs.
  eapply af_rel_morph with
    (f := fun encoded target =>
      DecoratesVASRun system encoded (proj1_sig target))
    (R := EncodedRunLe system)
    (T := fun left right =>
      JancarRunLe (proj1_sig left) (proj1_sig right)).
  - intros [run Hvalid]. cbn.
    destruct (valid_run_decorated d system run Hvalid) as [encoded Hencoded].
    now exists encoded.
  - intros left_code right_code [left Hleft] [right Hright]
      Hleft_code Hright_code Hencoded. cbn in *.
    eapply encoded_run_embedding; eauto.
  - apply encoded_run_almost_full.
Qed.
