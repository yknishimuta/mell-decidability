From Coq Require Import List Vector Lia.
From KruskalAfProp Require Import af.af af.af_tools.
From KruskalHigmanProp Require Import embeddings.list_embed af.af_list_embed.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Order Require Import AlmostFullBridge.
From Mell.VAS Require Import JancarOrder.
From Mell.WSVAS Require Import System Runs.

Import ListNotations.

Section RunOrder.
Context {d : nat} (system : WSVAS d).

Definition WSLetter := (NVec d * ws_transition system * NVec d)%type.

Definition ws_letter_le (left right : WSLetter) : Prop :=
  let '(left_source, left_transition, left_target) := left in
  let '(right_source, right_transition, right_target) := right in
  nvec_le left_source right_source /\
  ws_transition_le system left_transition right_transition /\
  nvec_le left_target right_target.

Fixpoint encode_ws_steps (source : NVec d)
    (steps : list (ws_transition system * NVec d)) : list WSLetter :=
  match steps with
  | [] => []
  | (transition, target) :: tail =>
      (source, transition, target) :: encode_ws_steps target tail
  end.

Definition encode_ws_run (run : WSRun system) : list WSLetter :=
  encode_ws_steps (ws_source run) (WSRunTargets run).

Definition WSDirectionLe (left right : WSRun system) : Prop :=
  nvec_le (ws_source left) (ws_source right) /\
  nvec_le (ws_target left) (ws_target right).

Definition WSHigmanEmbed (left right : WSRun system) : Prop :=
  list_embed ws_letter_le (encode_ws_run left) (encode_ws_run right).

(** Operational decomposition from Appendix C: every gap has both endpoints
    above the corresponding configuration of the smaller run. *)
Inductive WSRunGapDecomposition :
    NVec d -> list (ws_transition system * NVec d) ->
    NVec d -> list (ws_transition system * NVec d) -> Prop :=
| ws_gap_final : forall small_current big_current gap,
    nvec_le small_current big_current ->
    nvec_le small_current (ws_targets_target (system := system) big_current gap) ->
    WSRunGapDecomposition small_current [] big_current gap
| ws_gap_match : forall small_current transition small_target small_tail
    big_current gap big_transition big_target big_tail,
    nvec_le small_current big_current ->
    nvec_le small_current (ws_targets_target (system := system) big_current gap) ->
    ws_transition_le system transition big_transition ->
    nvec_le small_target big_target ->
    WSRunGapDecomposition small_target small_tail big_target big_tail ->
    WSRunGapDecomposition small_current
      ((transition, small_target) :: small_tail) big_current
      (gap ++ (big_transition, big_target) :: big_tail).

Definition WSRunOrder (left right : WSRun system) : Prop :=
  WSRunGapDecomposition (ws_source left) (WSRunTargets left)
    (ws_source right) (WSRunTargets right).

Lemma encode_ws_steps_app : forall source prefix suffix,
  encode_ws_steps source (prefix ++ suffix) =
  encode_ws_steps source prefix ++
  encode_ws_steps (ws_targets_target (system := system) source prefix) suffix.
Proof.
  intros source prefix; revert source.
  induction prefix as [|[transition target] tail IH]; intros source suffix; cbn; auto.
  now rewrite IH.
Qed.

Lemma encode_ws_steps_split_inv : forall source steps prefix letter suffix,
  encode_ws_steps source steps = prefix ++ letter :: suffix ->
  exists gap transition target tail,
    steps = gap ++ (transition, target) :: tail /\
    encode_ws_steps source gap = prefix /\
    letter = (ws_targets_target (system := system) source gap,
              transition, target) /\
    suffix = encode_ws_steps target tail.
Proof.
  intros source steps prefix. revert source steps.
  induction prefix as [|prefix_head prefix_tail IH];
    intros source steps letter suffix Hsplit.
  - destruct steps as [|[transition target] tail]; cbn in Hsplit; try discriminate.
    inversion Hsplit; subst.
    exists [], transition, target, tail. repeat split; reflexivity.
  - destruct steps as [|[first_transition first_target] first_tail];
      cbn in Hsplit; try discriminate.
    inversion Hsplit; subst prefix_head.
    destruct (IH first_target first_tail letter suffix H1)
      as [gap [transition [target [tail [Hsteps [Hprefix [Hletter Hsuffix]]]]]]].
    exists ((first_transition, first_target) :: gap), transition, target, tail.
    subst first_tail. split; [reflexivity|]. split.
    + cbn. now rewrite Hprefix.
    + split; assumption.
Qed.

Lemma ws_gap_higman : forall small steps big big_steps,
  WSRunGapDecomposition small steps big big_steps ->
  list_embed ws_letter_le
    (encode_ws_steps small steps) (encode_ws_steps big big_steps).
Proof.
  intros small steps big big_steps Hgap.
  induction Hgap as
      [small_current big_current gap Hgap_source Hgap_target
      |small_current transition small_target small_tail
       big_current gap big_transition big_target big_tail
       Hgap_source Hgap_target Htransition Hmatched Htail IH].
  - apply list_embed_nil_any.
  - rewrite encode_ws_steps_app. cbn.
    apply list_embed_left.
    constructor.
    + exact (conj Hgap_target (conj Htransition Hmatched)).
    + exact IH.
Qed.

Lemma ws_gap_direction : forall small steps big big_steps,
  WSRunGapDecomposition small steps big big_steps ->
  nvec_le small big /\
  nvec_le (ws_targets_target (system := system) small steps)
    (ws_targets_target (system := system) big big_steps).
Proof.
  intros small steps big big_steps Hgap.
  induction Hgap as
      [small_current big_current gap Hgap_source Hgap_target
      |small_current transition small_target small_tail
       big_current gap big_transition big_target big_tail
       Hgap_source Hgap_target Htransition Hmatched Htail IH].
  - split; assumption.
  - split; [assumption|].
    rewrite ws_targets_target_app. cbn. exact (proj2 IH).
Qed.

Lemma ws_higman_gap : forall small_steps big_steps small big,
  nvec_le small big ->
  nvec_le (ws_targets_target (system := system) small small_steps)
    (ws_targets_target (system := system) big big_steps) ->
  list_embed ws_letter_le
    (encode_ws_steps small small_steps) (encode_ws_steps big big_steps) ->
  WSRunGapDecomposition small small_steps big big_steps.
Proof.
  intros small_steps. induction small_steps as [|[transition target] tail IH];
    intros big_steps small big Hsource Htarget Hembed.
  - constructor; assumption.
  - destruct (list_embed_cons_inv Hembed)
      as [prefix [[[big_source big_transition] big_target]
          [suffix [Hsplit [Hletter Htail]]]]].
    destruct (encode_ws_steps_split_inv big big_steps prefix
        (big_source, big_transition, big_target) suffix Hsplit)
      as [gap [actual_transition [actual_target [actual_tail
          [Hsteps [Hprefix [Hletter_eq Hsuffix]]]]]]].
    inversion Hletter_eq; subst big_source actual_transition actual_target.
    subst big_steps suffix.
    cbn in Hletter. destruct Hletter as [Hgap_target [Htransition Hmatched]].
      apply ws_gap_match with (gap := gap) (big_transition := big_transition)
        (big_target := big_target) (big_tail := actual_tail).
      * exact Hsource.
      * exact Hgap_target.
      * exact Htransition.
      * exact Hmatched.
      * apply IH.
        -- exact Hmatched.
        -- rewrite ws_targets_target_app in Htarget. cbn in Htarget. exact Htarget.
        -- exact Htail.
Qed.

Theorem lemma_c_1_wsrun_order_iff_higman : forall left right,
  WSRunOrder left right <-> WSDirectionLe left right /\ WSHigmanEmbed left right.
Proof.
  intros left right. split.
  - intro H. split.
    + apply ws_gap_direction in H. exact H.
    + apply ws_gap_higman in H. exact H.
  - intros [[Hsource Htarget] Hembed].
    apply ws_higman_gap; assumption.
Qed.

Lemma ws_letter_le_refl : forall value, ws_letter_le value value.
Proof.
  intros [[source transition] target]; cbn. repeat split.
  - apply nvec_le_refl.
  - apply ws_transition_le_refl.
  - apply nvec_le_refl.
Qed.

Lemma ws_letter_le_trans : forall x y z,
  ws_letter_le x y -> ws_letter_le y z -> ws_letter_le x z.
Proof.
  intros [[xs xt] xy] [[ys yt] yy] [[zs zt] zy]; cbn.
  intros [Hxs [Hxt Hxy]] [Hys [Hyt Hyy]]. repeat split.
  - eapply nvec_le_trans; eauto.
  - eapply ws_transition_le_trans; eauto.
  - eapply nvec_le_trans; eauto.
Qed.

Theorem ws_run_order_refl : forall run, WSRunOrder run run.
Proof.
  intro run. apply lemma_c_1_wsrun_order_iff_higman. split.
  - split; apply nvec_le_refl.
  - apply list_embed_refl_local. apply ws_letter_le_refl.
Qed.

Theorem ws_run_order_trans : forall x y z,
  WSRunOrder x y -> WSRunOrder y z -> WSRunOrder x z.
Proof.
  intros x y z Hxy Hyz.
  apply lemma_c_1_wsrun_order_iff_higman in Hxy.
  apply lemma_c_1_wsrun_order_iff_higman in Hyz.
  apply lemma_c_1_wsrun_order_iff_higman.
  destruct Hxy as [[Hxs Hxt] Hxw], Hyz as [[Hys Hyt] Hyw]. split.
  - split; eapply nvec_le_trans; eauto.
  - eapply list_embed_trans_local; eauto using ws_letter_le_trans.
Qed.

Theorem ws_run_order_source_monotone : forall left right,
  WSRunOrder left right -> nvec_le (ws_source left) (ws_source right).
Proof.
  intros left right H. apply lemma_c_1_wsrun_order_iff_higman in H.
  exact (proj1 (proj1 H)).
Qed.

Theorem ws_run_order_target_monotone : forall left right,
  WSRunOrder left right -> nvec_le (ws_target left) (ws_target right).
Proof.
  intros left right H. apply lemma_c_1_wsrun_order_iff_higman in H.
  exact (proj2 (proj1 H)).
Qed.

Lemma encode_ws_run_shift : forall offset run,
  encode_ws_run (ws_run_shift offset run) =
  List.map (fun '(source, transition, target) =>
    (nvec_add source offset, transition, nvec_add target offset))
    (encode_ws_run run).
Proof.
  intros offset [source steps]. cbn. revert source.
  induction steps as [|[transition target] tail IH]; intros source; cbn; auto.
  now rewrite IH.
Qed.

Lemma ws_word_embed_shift : forall offset word,
  list_embed ws_letter_le word
    (List.map (fun '(source, transition, target) =>
      (nvec_add source offset, transition, nvec_add target offset)) word).
Proof.
  intros offset word. induction word as [|[[source transition] target] tail IH]; cbn.
  - constructor.
  - constructor.
    + repeat split; try apply nvec_le_add_right; apply ws_transition_le_refl.
    + exact IH.
Qed.

Theorem ws_run_order_shift : forall offset run,
  WSRunOrder run (ws_run_shift offset run).
Proof.
  intros offset run. apply lemma_c_1_wsrun_order_iff_higman. split.
  - split; rewrite ?ws_run_shift_source, ?ws_run_shift_target;
      apply nvec_le_add_right.
  - unfold WSHigmanEmbed. rewrite encode_ws_run_shift. apply ws_word_embed_shift.
Qed.

Lemma list_embed_refl_prefix : forall (X : Type) (R : X -> X -> Prop),
  (forall x, R x x) -> forall prefix suffix,
  list_embed R prefix (prefix ++ suffix).
Proof.
  intros X R Hrefl prefix. induction prefix as [|head tail IH]; intro suffix; cbn.
  - apply list_embed_nil_any.
  - constructor; auto.
Qed.

Lemma list_embed_refl_suffix : forall (X : Type) (R : X -> X -> Prop),
  (forall x, R x x) -> forall prefix suffix,
  list_embed R suffix (prefix ++ suffix).
Proof.
  intros X R Hrefl prefix. induction prefix as [|head tail IH]; intro suffix; cbn.
  - apply list_embed_refl_local. exact Hrefl.
  - constructor 3. apply IH.
Qed.

Lemma encode_ws_run_concat : forall left right,
  ws_target left = ws_source right ->
  encode_ws_run (ws_run_concat left right) =
    encode_ws_run left ++ encode_ws_run right.
Proof.
  intros [ls lt] [rs rt] Hboundary; cbn in *.
  rewrite encode_ws_steps_app, Hboundary. reflexivity.
Qed.

Theorem ws_run_order_concat_left : forall left right,
  ws_target left = ws_source right ->
  nvec_le (ws_target left) (ws_target right) ->
  WSRunOrder left (ws_run_concat left right).
Proof.
  intros left right Hboundary Htarget.
  apply lemma_c_1_wsrun_order_iff_higman. split.
  - split; [rewrite ws_run_concat_source; apply nvec_le_refl|].
    rewrite ws_run_concat_target by exact Hboundary. exact Htarget.
  - unfold WSHigmanEmbed. rewrite encode_ws_run_concat by exact Hboundary.
    apply list_embed_refl_prefix. apply ws_letter_le_refl.
Qed.

Theorem ws_run_order_concat_right : forall left right,
  ws_target left = ws_source right ->
  nvec_le (ws_source right) (ws_source left) ->
  WSRunOrder right (ws_run_concat left right).
Proof.
  intros left right Hboundary Hsource.
  apply lemma_c_1_wsrun_order_iff_higman. split.
  - split.
    + rewrite ws_run_concat_source. exact Hsource.
    + rewrite ws_run_concat_target by exact Hboundary. apply nvec_le_refl.
  - unfold WSHigmanEmbed. rewrite encode_ws_run_concat by exact Hboundary.
    apply list_embed_refl_suffix. apply ws_letter_le_refl.
Qed.

Definition EncodedWSRun :=
  (NVec d * (NVec d * list WSLetter))%type.

Definition encoded_ws_run (run : WSRun system) : EncodedWSRun :=
  (ws_source run, (ws_target run, encode_ws_run run)).

Definition EncodedWSRunLe (left right : EncodedWSRun) : Prop :=
  nvec_le (fst left) (fst right) /\
  nvec_le (fst (snd left)) (fst (snd right)) /\
  list_embed ws_letter_le (snd (snd left)) (snd (snd right)).

Lemma ws_letter_le_almost_full : af ws_letter_le.
Proof.
  unfold ws_letter_le.
  pose proof (af_product (nvec_le_almost_full d)
    (ws_transition_wqo system)) as Hleft.
  pose proof (af_product Hleft (nvec_le_almost_full d)) as Hall.
  eapply af_mono; [|exact Hall].
  intros [[xs xt] xy] [[ys yt] yy]; cbn. tauto.
Qed.

Lemma encoded_ws_run_almost_full : af EncodedWSRunLe.
Proof.
  unfold EncodedWSRunLe.
  pose proof (af_list_embed ws_letter_le_almost_full) as Hword.
  pose proof (af_product (nvec_le_almost_full d) Hword) as Htail.
  pose proof (af_product (nvec_le_almost_full d) Htail) as Hall.
  eapply af_mono; [|exact Hall].
  intros [ls [lt lw]] [rs [rt rw]]; cbn. tauto.
Qed.

Theorem corollary_c_2_wsrun_wqo :
  afs (ValidWSRun (system := system)) WSRunOrder.
Proof.
  apply af_sub_rel_afs.
  eapply af_rel_morph with
    (f := fun encoded target => encoded = encoded_ws_run (proj1_sig target))
    (R := EncodedWSRunLe)
    (T := fun left right =>
      WSRunOrder (proj1_sig left) (proj1_sig right)).
  - intros [run Hvalid]. cbn. now exists (encoded_ws_run run).
  - intros left_code right_code [left Hleft] [right Hright]
      Hleft_code Hright_code Hencoded. cbn in *.
    subst left_code right_code.
    apply lemma_c_1_wsrun_order_iff_higman.
    unfold EncodedWSRunLe, encoded_ws_run in Hencoded. cbn in Hencoded.
    destruct Hencoded as [Hs [Ht Hw]]. split; [now split|exact Hw].
  - exact encoded_ws_run_almost_full.
Qed.

End RunOrder.

Arguments encode_ws_run {d system} _.
Arguments WSRunOrder {d} system _ _.
Arguments WSDirectionLe {d} system _ _.
Arguments WSHigmanEmbed {d} system _ _.
