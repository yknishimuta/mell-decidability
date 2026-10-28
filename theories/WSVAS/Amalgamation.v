From Coq Require Import List Vector ZArith Lia.
From KruskalAfProp Require Import af.af.
From KruskalHigmanProp Require Import embeddings.list_embed.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.VAS Require Import Runs JancarOrder.
From Mell.WSVAS Require Import System Runs RunOrder.

Import ListNotations.

Section Amalgamation.
Context {d : nat} (system : WSVAS d).

Lemma nvec_add_le_compat : forall (left right offset : NVec d),
  nvec_le left right -> nvec_le (nvec_add left offset) (nvec_add right offset).
Proof.
  intros left right offset H index. specialize (H index).
  unfold nvec_add.
  repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma nvec_add_shuffle : forall (a b c : NVec d),
  nvec_add (nvec_add a b) c = nvec_add (nvec_add a c) b.
Proof.
  intros a b c. rewrite !nvec_add_assoc_local.
  f_equal. apply nvec_add_comm.
Qed.

(** The zero-transition case of Appendix C.4, and the local gap operation
    used at every recursive layer of the general construction. *)
Lemma amalgamate_ws_gaps : forall (base : NVec d)
    (alpha beta : WSRun system),
  ValidWSRun alpha -> ValidWSRun beta ->
  nvec_le base (ws_source alpha) -> nvec_le base (ws_target alpha) ->
  nvec_le base (ws_source beta) -> nvec_le base (ws_target beta) ->
  exists gamma,
    ValidWSRun gamma /\
    WSRunOrder system alpha gamma /\ WSRunOrder system beta gamma /\
    nvec_add base (ws_source gamma) =
      nvec_add (ws_source alpha) (ws_source beta) /\
    nvec_add base (ws_target gamma) =
      nvec_add (ws_target alpha) (ws_target beta).
Proof.
  intros base alpha beta Halpha Hbeta Has Hat Hbs Hbt.
  destruct (nvec_le_offset_witness d base (ws_source beta) Hbs)
    as [beta_source_offset Hbeta_source].
  destruct (nvec_le_offset_witness d base (ws_target alpha) Hat)
    as [alpha_target_offset Halpha_target].
  set (shifted_alpha := ws_run_shift beta_source_offset alpha).
  set (shifted_beta := ws_run_shift alpha_target_offset beta).
  assert (Hboundary : ws_target shifted_alpha = ws_source shifted_beta).
  { unfold shifted_alpha, shifted_beta.
    rewrite ws_run_shift_target, ws_run_shift_source,
      Halpha_target, Hbeta_source.
    apply nvec_add_shuffle. }
  exists (ws_run_concat shifted_alpha shifted_beta).
  assert (Hvalid_alpha : ValidWSRun shifted_alpha).
  { apply valid_ws_run_shift. exact Halpha. }
  assert (Hvalid_beta : ValidWSRun shifted_beta).
  { apply valid_ws_run_shift. exact Hbeta. }
  subst shifted_alpha shifted_beta.
  repeat split.
  - eapply valid_ws_run_concat; eauto.
  - apply lemma_c_1_wsrun_order_iff_higman. split.
    + split.
      * rewrite ws_run_concat_source, ws_run_shift_source.
        apply nvec_le_add_right.
      * rewrite ws_run_concat_target by exact Hboundary.
        rewrite ws_run_shift_target.
        rewrite Halpha_target.
        apply nvec_add_le_compat. exact Hbt.
    + unfold WSHigmanEmbed.
      rewrite encode_ws_run_concat by exact Hboundary.
      rewrite !encode_ws_run_shift.
      eapply list_embed_trans_local.
      * apply ws_letter_le_trans.
      * apply ws_word_embed_shift.
      * apply list_embed_refl_prefix. apply ws_letter_le_refl.
  - apply lemma_c_1_wsrun_order_iff_higman. split.
    + split.
      * rewrite ws_run_concat_source, ws_run_shift_source.
        rewrite Hbeta_source.
        apply nvec_add_le_compat. exact Has.
      * rewrite ws_run_concat_target by exact Hboundary.
        rewrite ws_run_shift_target. apply nvec_le_add_right.
    + unfold WSHigmanEmbed.
      rewrite encode_ws_run_concat by exact Hboundary.
      rewrite !encode_ws_run_shift.
      eapply list_embed_trans_local.
      * apply ws_letter_le_trans.
      * apply ws_word_embed_shift.
      * apply list_embed_refl_suffix. apply ws_letter_le_refl.
  - rewrite ws_run_concat_source, ws_run_shift_source, Hbeta_source.
    rewrite <- nvec_add_assoc_local.
    rewrite (nvec_add_comm d base (ws_source alpha)).
    rewrite nvec_add_assoc_local. reflexivity.
  - rewrite ws_run_concat_target by exact Hboundary.
    rewrite ws_run_shift_target, Halpha_target.
    rewrite (nvec_add_comm d (ws_target beta) alpha_target_offset).
    rewrite <- nvec_add_assoc_local. reflexivity.
Qed.

Definition ws_run_stitch (prefix : WSRun system)
    (transition : ws_transition system) (suffix : WSRun system) : WSRun system :=
  {| WSRunSource := ws_source prefix;
     WSRunTargets := WSRunTargets prefix ++
       (transition, ws_source suffix) :: WSRunTargets suffix |}.

Lemma ws_run_stitch_source : forall prefix transition suffix,
  ws_source (ws_run_stitch prefix transition suffix) = ws_source prefix.
Proof. reflexivity. Qed.

Lemma ws_run_stitch_target : forall prefix transition suffix,
  ws_target (ws_run_stitch prefix transition suffix) = ws_target suffix.
Proof.
  intros prefix transition suffix. unfold ws_run_stitch, ws_target; cbn.
  rewrite ws_targets_target_app. cbn. reflexivity.
Qed.

Lemma valid_ws_run_stitch : forall prefix transition suffix,
  ValidWSRun prefix -> ValidWSRun suffix ->
  ws_transition_action system transition =
    StepAction (ws_target prefix) (ws_source suffix) ->
  ValidWSRun (ws_run_stitch prefix transition suffix).
Proof.
  intros [source steps] transition [suffix_source suffix_steps]
    Hprefix Hsuffix Haction. cbn in *.
  apply valid_ws_targets_app. split; [exact Hprefix|].
  cbn. split; assumption.
Qed.

Lemma encode_ws_run_stitch : forall prefix transition suffix,
  encode_ws_run (ws_run_stitch prefix transition suffix) =
  encode_ws_run prefix ++
    (ws_target prefix, transition, ws_source suffix) :: encode_ws_run suffix.
Proof.
  intros [source steps] transition [suffix_source suffix_steps]. cbn.
  rewrite encode_ws_steps_app. cbn. reflexivity.
Qed.

Lemma list_embed_app_local : forall (X : Type) (R : X -> X -> Prop)
    left1 left2 right1 right2,
  list_embed R left1 right1 -> list_embed R left2 right2 ->
  list_embed R (left1 ++ left2) (right1 ++ right2).
Proof.
  intros X R left1 left2 right1 right2 H1 H2.
  induction H1; cbn.
  - exact H2.
  - constructor; assumption.
  - constructor 3. assumption.
Qed.

(** Corollary C.3 in the one-matched-transition form. *)
Lemma ws_run_order_stitch : forall left_prefix left_transition left_suffix
    right_prefix right_transition right_suffix,
  WSRunOrder system left_prefix right_prefix ->
  ws_transition_le system left_transition right_transition ->
  WSRunOrder system left_suffix right_suffix ->
  WSRunOrder system
    (ws_run_stitch left_prefix left_transition left_suffix)
    (ws_run_stitch right_prefix right_transition right_suffix).
Proof.
  intros lp lt ls rp rt rs Hprefix Htransition Hsuffix.
  apply lemma_c_1_wsrun_order_iff_higman. split.
  - split.
    + rewrite !ws_run_stitch_source.
      exact (ws_run_order_source_monotone system _ _ Hprefix).
    + rewrite !ws_run_stitch_target.
      exact (ws_run_order_target_monotone system _ _ Hsuffix).
  - unfold WSHigmanEmbed. rewrite !encode_ws_run_stitch.
    apply list_embed_app_local.
    + apply lemma_c_1_wsrun_order_iff_higman in Hprefix. exact (proj2 Hprefix).
    + constructor.
      * repeat split.
        -- exact (ws_run_order_target_monotone system _ _ Hprefix).
        -- exact Htransition.
        -- exact (ws_run_order_source_monotone system _ _ Hsuffix).
      * apply lemma_c_1_wsrun_order_iff_higman in Hsuffix. exact (proj2 Hsuffix).
Qed.

Lemma exact_transition_stitch : forall
    (base next alpha_pre alpha_post beta_pre beta_post
      merged_pre merged_post : NVec d)
    (root left right merged : ws_transition system),
  ws_transition_action system root = StepAction base next ->
  ws_transition_action system left = StepAction alpha_pre alpha_post ->
  ws_transition_action system right = StepAction beta_pre beta_post ->
  zvec_add (ws_transition_action system root)
      (ws_transition_action system merged) =
    zvec_add (ws_transition_action system left)
      (ws_transition_action system right) ->
  nvec_add base merged_pre = nvec_add alpha_pre beta_pre ->
  nvec_add next merged_post = nvec_add alpha_post beta_post ->
  ws_transition_action system merged = StepAction merged_pre merged_post.
Proof.
  intros base next alpha_pre alpha_post beta_pre beta_post
    merged_pre merged_post root left right merged
    Hroot Hleft Hright Hdiamond Hpre Hpost.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  pose proof (f_equal (fun value : ZVec d => Vector.nth value index) Hroot) as Hr.
  pose proof (f_equal (fun value : ZVec d => Vector.nth value index) Hleft) as Hl.
  pose proof (f_equal (fun value : ZVec d => Vector.nth value index) Hright) as Hv.
  pose proof (f_equal (fun value : ZVec d => Vector.nth value index) Hdiamond) as Hd.
  pose proof (f_equal (fun value : NVec d => Vector.nth value index) Hpre) as Hp.
  pose proof (f_equal (fun value : NVec d => Vector.nth value index) Hpost) as Hq.
  unfold StepAction, zvec_sub_run, zvec_add, nvec_to_zvec, nvec_add in *.
  repeat rewrite (Vector.nth_map2 Z.sub _ _ index index index eq_refl eq_refl) in *.
  repeat rewrite (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl) in *.
  repeat rewrite (Vector.nth_map Z.of_nat _ index index eq_refl) in *.
  repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in *.
  lia.
Qed.

Lemma ws_gap_decomposition_amalgamation : forall
    base root_steps alpha_source alpha_steps beta_source beta_steps,
  ValidWSTargets (system := system) base root_steps ->
  ValidWSTargets (system := system) alpha_source alpha_steps ->
  ValidWSTargets (system := system) beta_source beta_steps ->
  WSRunGapDecomposition system base root_steps alpha_source alpha_steps ->
  WSRunGapDecomposition system base root_steps beta_source beta_steps ->
  exists gamma,
    ValidWSRun gamma /\
    WSRunOrder system
      {| WSRunSource := alpha_source; WSRunTargets := alpha_steps |} gamma /\
    WSRunOrder system
      {| WSRunSource := beta_source; WSRunTargets := beta_steps |} gamma /\
    nvec_add base (ws_source gamma) = nvec_add alpha_source beta_source /\
    nvec_add (ws_targets_target (system := system) base root_steps)
      (ws_target gamma) =
    nvec_add (ws_targets_target (system := system) alpha_source alpha_steps)
      (ws_targets_target (system := system) beta_source beta_steps).
Proof.
  intros base root_steps alpha_source alpha_steps beta_source beta_steps
    Hroot Halpha Hbeta Halpha_order.
  revert beta_source beta_steps Hbeta.
  induction Halpha_order as
      [base alpha_source alpha_gap Halpha_source Halpha_target
      |base root_transition root_target root_tail
       alpha_source alpha_gap alpha_transition alpha_target alpha_tail
       Halpha_source Halpha_pre Hroot_alpha Halpha_matched
       Halpha_tail IH];
    intros beta_source beta_steps Hbeta Hbeta_order.
  - inversion Hbeta_order; subst.
    eapply amalgamate_ws_gaps; eauto.
  - inversion Hbeta_order as
      [|? ? ? ? ? beta_gap beta_transition beta_target beta_tail
        Hbeta_source Hbeta_pre Hroot_beta Hbeta_matched Hbeta_tail]; subst.
    apply valid_ws_targets_app in Halpha.
    destruct Halpha as [Halpha_gap Halpha_rest].
    cbn in Halpha_rest. destruct Halpha_rest as [Halpha_action Halpha_tail_valid].
    apply valid_ws_targets_app in Hbeta.
    destruct Hbeta as [Hbeta_gap Hbeta_rest].
    cbn in Hbeta_rest. destruct Hbeta_rest as [Hbeta_action Hbeta_tail_valid].
    cbn in Hroot. destruct Hroot as [Hroot_action Hroot_tail_valid].
    destruct (amalgamate_ws_gaps
      base
      {| WSRunSource := alpha_source; WSRunTargets := alpha_gap |}
      {| WSRunSource := beta_source; WSRunTargets := beta_gap |}
      Halpha_gap Hbeta_gap Halpha_source Halpha_pre
      Hbeta_source Hbeta_pre) as
      [gamma_gap [Hgamma_gap [Halpha_gap_order [Hbeta_gap_order
        [Hgamma_gap_source Hgamma_gap_target]]]]].
    destruct (IH Hroot_tail_valid Halpha_tail_valid
      beta_target beta_tail Hbeta_tail_valid Hbeta_tail)
      as [gamma_tail [Hgamma_tail [Halpha_tail_order [Hbeta_tail_order
        [Hgamma_tail_source Hgamma_tail_target]]]]].
    destruct (ws_transition_action_diamond system root_transition
      alpha_transition beta_transition Hroot_alpha Hroot_beta)
      as [merged [Halpha_merged [Hbeta_merged Hdiamond]]].
    assert (Hmerged_action : ws_transition_action system merged =
      StepAction (ws_target gamma_gap) (ws_source gamma_tail)).
    { eapply exact_transition_stitch with
        (base := base) (next := root_target)
        (alpha_pre := ws_targets_target (system := system) alpha_source alpha_gap)
        (alpha_post := alpha_target)
        (beta_pre := ws_targets_target (system := system) beta_source beta_gap)
        (beta_post := beta_target)
        (root := root_transition) (left := alpha_transition)
        (right := beta_transition); cbn in *; eauto. }
    exists (ws_run_stitch gamma_gap merged gamma_tail).
    repeat split.
    + eapply valid_ws_run_stitch; eauto.
    + change (WSRunOrder system
        (ws_run_stitch
          {| WSRunSource := alpha_source; WSRunTargets := alpha_gap |}
          alpha_transition
          {| WSRunSource := alpha_target; WSRunTargets := alpha_tail |})
        (ws_run_stitch gamma_gap merged gamma_tail)).
      eapply ws_run_order_stitch; eauto.
    + change (WSRunOrder system
        (ws_run_stitch
          {| WSRunSource := beta_source; WSRunTargets := beta_gap |}
          beta_transition
          {| WSRunSource := beta_target; WSRunTargets := beta_tail |})
        (ws_run_stitch gamma_gap merged gamma_tail)).
      eapply ws_run_order_stitch; eauto.
    + rewrite ws_run_stitch_source. exact Hgamma_gap_source.
    + rewrite ws_run_stitch_target.
      rewrite !ws_targets_target_app. cbn. exact Hgamma_tail_target.
Qed.

Theorem lemma_c_4_wsrun_exact_amalgamation : forall
    (root alpha beta : WSRun system),
  ValidWSRun root -> ValidWSRun alpha -> ValidWSRun beta ->
  WSRunOrder system root alpha -> WSRunOrder system root beta ->
  exists merged,
    ValidWSRun merged /\
    WSRunOrder system alpha merged /\
    WSRunOrder system beta merged /\
    nvec_add (ws_source root) (ws_source merged) =
      nvec_add (ws_source alpha) (ws_source beta) /\
    nvec_add (ws_target root) (ws_target merged) =
      nvec_add (ws_target alpha) (ws_target beta).
Proof.
  intros [root_source root_steps] [alpha_source alpha_steps]
    [beta_source beta_steps] Hroot Halpha Hbeta Hra Hrb.
  eapply ws_gap_decomposition_amalgamation; eauto.
Qed.

Theorem lemma_5_2_wsvas_runs_wqo_amalgamation :
  afs (ValidWSRun (system := system)) (WSRunOrder system) /\
  (forall root alpha beta,
    ValidWSRun root -> ValidWSRun alpha -> ValidWSRun beta ->
    WSRunOrder system root alpha -> WSRunOrder system root beta ->
    exists merged,
      ValidWSRun merged /\ WSRunOrder system alpha merged /\
      WSRunOrder system beta merged /\
      nvec_add (ws_source root) (ws_source merged) =
        nvec_add (ws_source alpha) (ws_source beta) /\
      nvec_add (ws_target root) (ws_target merged) =
        nvec_add (ws_target alpha) (ws_target beta)).
Proof.
  split.
  - apply corollary_c_2_wsrun_wqo.
  - exact lemma_c_4_wsrun_exact_amalgamation.
Qed.

Lemma nvec_scaling_step : forall coefficient
    (root previous run next : NVec d),
  nvec_add (nvec_scale coefficient root) previous =
    nvec_scale (S coefficient) run ->
  nvec_add root next = nvec_add previous run ->
  nvec_add (nvec_scale (S coefficient) root) next =
    nvec_scale (S (S coefficient)) run.
Proof.
  intros coefficient root previous run next IH Hdiamond.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  pose proof (f_equal (fun value : NVec d => Vector.nth value index) IH) as Hi.
  pose proof (f_equal (fun value : NVec d => Vector.nth value index) Hdiamond) as Hd.
  unfold nvec_add, nvec_scale in *.
  repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in *.
  repeat rewrite (Vector.nth_map (Nat.mul _) _ index index eq_refl) in *.
  lia.
Qed.

Theorem corollary_5_3_wsvas_run_scaling : forall root run (factor : nat),
  ValidWSRun root -> ValidWSRun run ->
  WSRunOrder system root run ->
  (1 <= factor)%nat ->
  exists scaled,
    ValidWSRun scaled /\ WSRunOrder system run scaled /\
    nvec_add (nvec_scale (factor - 1) (ws_source root))
      (ws_source scaled) = nvec_scale factor (ws_source run) /\
    nvec_add (nvec_scale (factor - 1) (ws_target root))
      (ws_target scaled) = nvec_scale factor (ws_target run).
Proof.
  intros root run factor Hroot Hrun Horder Hfactor.
  destruct factor as [|factor]; [lia|]. clear Hfactor.
  induction factor as [|factor IH].
  - exists run. repeat split; auto using ws_run_order_refl.
    + cbn. rewrite nvec_scale_zero, nvec_scale_one,
        nvec_add_zero_left_local. reflexivity.
    + cbn. rewrite nvec_scale_zero, nvec_scale_one,
        nvec_add_zero_left_local. reflexivity.
  - destruct IH as [previous [Hprevious [Hrun_previous [Hsource Htarget]]]].
    assert (Hroot_previous : WSRunOrder system root previous).
    { eapply ws_run_order_trans; eauto. }
    destruct (lemma_c_4_wsrun_exact_amalgamation root previous run
      Hroot Hprevious Hrun Hroot_previous Horder)
      as [next [Hnext [Hprevious_next [Hrun_next [Hnext_source Hnext_target]]]]].
    exists next. repeat split; auto.
    + replace ((S (S factor) - 1)%nat) with (S factor) by lia.
      replace ((S factor - 1)%nat) with factor in Hsource by lia.
      eapply nvec_scaling_step; eauto.
    + replace ((S (S factor) - 1)%nat) with (S factor) by lia.
      replace ((S factor - 1)%nat) with factor in Htarget by lia.
      eapply nvec_scaling_step; eauto.
Qed.

End Amalgamation.
