From Coq Require Import List Vector Arith Wf_nat Lia Sorting.Permutation Classical_Prop.
From Mell.Core Require Import Vector.
From Mell.BVASS Require Import Stateful Code ContextInsertion StatefulAmalgamation Extend.
From Mell.Order Require Import FiniteBasis.

Import ListNotations.

(** FoSSaCS 2026, Section 4: unary nodes do not increase branching depth. *)
Fixpoint branching_depth {d q} (run : SRun d q) : nat :=
  match run with
  | srun_leaf _ => 0
  | srun_node _ children _ =>
      match children with
      | sruns_nil => 0
      | sruns_cons child sruns_nil => branching_depth child
      | sruns_cons child tail =>
          S (Nat.max (branching_depth child) (runs_max_branching_depth tail))
      end
  end
with runs_max_branching_depth {d q} (runs : SRuns d q) : nat :=
  match runs with
  | sruns_nil => 0
  | sruns_cons run tail =>
      Nat.max (branching_depth run) (runs_max_branching_depth tail)
  end.

Lemma branching_depth_leaf : forall d q (config : SConfig d q),
    branching_depth (srun_leaf config) = 0.
Proof. reflexivity. Qed.

Lemma branching_depth_unary : forall d q (rule : SRule d q) child result,
    branching_depth (srun_node rule (sruns_cons child sruns_nil) result) =
      branching_depth child.
Proof. reflexivity. Qed.

Lemma branching_depth_branching_head : forall d q (rule : SRule d q)
    first second tail result,
    branching_depth first <
      branching_depth
        (srun_node rule (sruns_cons first (sruns_cons second tail)) result).
Proof. cbn; intros; lia. Qed.

Lemma runs_max_branching_depth_head : forall d q (run : SRun d q) runs,
    branching_depth run <=
      runs_max_branching_depth (sruns_cons run runs).
Proof. cbn; intros; apply Nat.le_max_l. Qed.

Lemma sruns_remove_branching_depth : forall d q (run : SRun d q) source rest,
    SRunsRemove run source rest ->
    runs_max_branching_depth source =
      Nat.max (branching_depth run) (runs_max_branching_depth rest).
Proof.
  intros d q run source rest Hremove. induction Hremove; cbn.
  - reflexivity.
  - rewrite IHHremove, Nat.max_assoc.
    rewrite (Nat.max_comm (branching_depth head) (branching_depth run)).
    now rewrite <- Nat.max_assoc.
Qed.

Lemma branching_depth_node_formula : forall d q (rule : SRule d q) children result,
    branching_depth (srun_node rule children result) =
      if Nat.leb 2 (length (sruns_configs children))
      then S (runs_max_branching_depth children)
      else runs_max_branching_depth children.
Proof.
  intros d q rule children result. destruct children as [|first tail]; cbn; auto.
  destruct tail; cbn; auto using Nat.max_0_r.
Qed.

Lemma srun_isomorphic_branching_depth_mut : forall d q,
  (forall left right : SRun d q,
      SRunIsomorphic left right ->
      branching_depth left = branching_depth right) /\
  (forall left right : SRuns d q,
      SRunsIsomorphic left right ->
      runs_max_branching_depth left = runs_max_branching_depth right).
Proof.
  intros d q. apply SRunIsomorphic_mutind.
  - reflexivity.
  - intros rule left right result Hiso IH.
    rewrite !branching_depth_node_formula, IH.
    pose proof (sruns_isomorphic_configs_permutation d q left right Hiso)
      as Hconfigs.
    now rewrite (Permutation_length Hconfigs).
  - reflexivity.
  - intros left lefts right rights remainder Hremove Hheadiso Hhead
      Htailiso Htail. cbn.
    rewrite Hhead, Htail.
    pose proof (sruns_remove_branching_depth d q right rights remainder Hremove)
      as Hdepth.
    now rewrite Hdepth.
Qed.

Theorem srun_isomorphic_branching_depth : forall d q
    (left right : SRun d q),
    SRunIsomorphic left right ->
    branching_depth left = branching_depth right.
Proof. intros; eapply (proj1 (srun_isomorphic_branching_depth_mut d q)); eauto. Qed.

Definition SameTargetAndSize {d q} (alpha beta : SRun d q) : Prop :=
  root_config alpha = root_config beta /\
  run_node_count alpha = run_node_count beta.

Lemma same_target_and_size_refl : forall d q (run : SRun d q),
    SameTargetAndSize run run.
Proof. intros; split; reflexivity. Qed.

Lemma same_target_and_size_sym : forall d q (left right : SRun d q),
    SameTargetAndSize left right -> SameTargetAndSize right left.
Proof. intros d q left right [Hroot Hsize]; split; symmetry; assumption. Qed.

Lemma same_target_and_size_trans : forall d q (first second third : SRun d q),
    SameTargetAndSize first second -> SameTargetAndSize second third ->
    SameTargetAndSize first third.
Proof. intros d q first second third [Hroot1 Hsize1] [Hroot2 Hsize2].
  split; congruence. Qed.

Definition RunBasis {d q} (B : SBVAS d q) (basis : list (SRun d q)) : Prop :=
  (forall sigma, List.In sigma basis -> ValidSRun B sigma) /\
  (forall alpha, ValidSRun B alpha ->
    exists sigma, List.In sigma basis /\ ContextOrder B sigma alpha).

Lemma run_basis_root_configs_reachable : forall d q (B : SBVAS d q) basis,
    RunBasis B basis ->
    ReachableConfigurations B (basis_root_configs basis).
Proof.
  intros d q B basis [Hvalid _]. now apply basis_root_configs_reachable.
Qed.

Fixpoint srun_path_compose {d q} {whole middle focus : SRun d q}
    (outer : SRunPath whole middle) (inner : SRunPath middle focus) :
    SRunPath whole focus :=
  match outer in SRunPath actual_whole actual_middle
    return SRunPath actual_middle focus -> SRunPath actual_whole focus with
  | srun_path_here run => fun path => path
  | srun_path_child rule before child after result actual_middle tail =>
      fun path => srun_path_child rule before child after result focus
        (srun_path_compose tail path)
  end inner.

Fixpoint srun_path_into_replacement {d q}
    {whole old replacement focus : SRun d q}
    (outer : SRunPath whole old) (inner : SRunPath replacement focus)
    (delta : NVec d) :
    SRunPath (replace_subrun_at outer replacement delta) focus :=
  match outer in SRunPath actual_whole actual_old
    return SRunPath
      (replace_subrun_at outer replacement delta) focus with
  | srun_path_here _ => inner
  | srun_path_child rule before child after result actual_old tail =>
      srun_path_child rule before
        (replace_subrun_at tail replacement delta) after
        (fst result, nvec_add (snd result) delta) focus
        (srun_path_into_replacement tail inner delta)
  end.

Definition BasisRunInRepresentative {d q} (B : SBVAS d q)
    (sigma alpha : SRun d q) : Prop :=
  exists beta focus (path : SRunPath beta focus),
    ValidSRun B beta /\
    SameTargetAndSize alpha beta /\
    ContextOrder B sigma focus.

Definition RIndex {d q} (B : SBVAS d q) (basis : list (SRun d q))
    (alpha : SRun d q) (index : nat) : Prop :=
  exists sigma,
    nth_error basis index = Some sigma /\
    BasisRunInRepresentative B sigma alpha.

Definition RSelection {d q} (B : SBVAS d q) (basis : list (SRun d q))
    (alpha : SRun d q) (selected : list nat) : Prop :=
  NoDup selected /\
  (forall index,
    List.In index selected <-> index < length basis /\ RIndex B basis alpha index).

Definition RCardinality {d q} (B : SBVAS d q) (basis : list (SRun d q))
    (alpha : SRun d q) (cardinality : nat) : Prop :=
  exists selected, RSelection B basis alpha selected /\
    length selected = cardinality.

Lemma finite_prop_selection : forall (universe : list nat) (P : nat -> Prop),
    NoDup universe ->
    exists selected,
      NoDup selected /\
      (forall index, List.In index selected <->
        List.In index universe /\ P index).
Proof.
  intros universe P Hnodup. induction Hnodup as [|head tail Hnotin Hnodup IH].
  - exists []. split; [constructor|]. cbn. tauto.
  - destruct IH as [selected [Hselected_nodup Hselected]].
    destruct (classic (P head)) as [Hhead|Hhead].
    + exists (head :: selected). split.
      * constructor; [intro Hin; apply Hselected in Hin; tauto|exact Hselected_nodup].
      * intro index. cbn. rewrite Hselected. split.
        -- intros [Heq|[Hin HP]].
           ++ subst. split; [left; reflexivity|exact Hhead].
           ++ split; [right; exact Hin|exact HP].
        -- intros [[Heq|Hin] HP].
           ++ left. exact Heq.
           ++ right. split; assumption.
    + exists selected. split; [exact Hselected_nodup|].
      intro index. rewrite Hselected. split.
      * intros [Hin HP]. split; [right; exact Hin|exact HP].
      * intros [[Heq|Hin] HP].
        -- subst. contradiction.
        -- split; assumption.
Qed.

Lemma in_seq_zero_iff : forall length index,
    List.In index (seq 0 length) <-> index < length.
Proof. intros length index. rewrite in_seq. lia. Qed.

Lemma r_cardinality_exists : forall d q (B : SBVAS d q) basis alpha,
    exists cardinality, RCardinality B basis alpha cardinality.
Proof.
  intros d q B basis alpha.
  destruct (finite_prop_selection (seq 0 (length basis))
    (RIndex B basis alpha)) as [selected [Hnodup Hselected]].
  - apply seq_NoDup.
  - exists (length selected), selected. split.
    + split; [exact Hnodup|]. intro index. rewrite Hselected, in_seq_zero_iff.
      tauto.
    + reflexivity.
Qed.

Lemma r_index_same_target_and_size : forall d q (B : SBVAS d q) basis
    alpha beta index,
    SameTargetAndSize alpha beta ->
    (RIndex B basis alpha index <-> RIndex B basis beta index).
Proof.
  intros d q B basis alpha beta index Hequiv. split.
  - intros [sigma [Hnth [representative [focus [path
      [Hvalid [Hsame Hbelow]]]]]]].
    exists sigma. split; [exact Hnth|]. exists representative, focus, path.
    split; [exact Hvalid|]. split; [|exact Hbelow].
    eapply same_target_and_size_trans.
    + apply same_target_and_size_sym. exact Hequiv.
    + exact Hsame.
  - intros [sigma [Hnth [representative [focus [path
      [Hvalid [Hsame Hbelow]]]]]]].
    exists sigma. split; [exact Hnth|]. exists representative, focus, path.
    split; [exact Hvalid|]. split; [|exact Hbelow].
    eapply same_target_and_size_trans; eauto.
Qed.

Lemma r_cardinality_unique : forall d q (B : SBVAS d q) basis alpha left right,
    RCardinality B basis alpha left ->
    RCardinality B basis alpha right -> left = right.
Proof.
  intros d q B basis alpha left right
    [xs [[Hxs_nd Hxs] Hxs_len]] [ys [[Hys_nd Hys] Hys_len]].
  assert (Hperm : Permutation xs ys).
  { apply NoDup_Permutation; try assumption. intro index.
    rewrite Hxs, Hys. reflexivity. }
  rewrite <- Hxs_len, <- Hys_len. now apply Permutation_length.
Qed.

Lemma r_cardinality_invariant : forall d q (B : SBVAS d q) basis
    alpha beta cardinality,
    SameTargetAndSize alpha beta ->
    (RCardinality B basis alpha cardinality <->
     RCardinality B basis beta cardinality).
Proof.
  intros d q B basis alpha beta cardinality Hequiv. split.
  - intros [selected [[Hnodup Hselected] Hlength]].
    exists selected. split; [|exact Hlength]. split; [exact Hnodup|].
    intro index. rewrite Hselected.
    rewrite (r_index_same_target_and_size d q B basis alpha beta index Hequiv).
    reflexivity.
  - intros [selected [[Hnodup Hselected] Hlength]].
    exists selected. split; [|exact Hlength]. split; [exact Hnodup|].
    intro index. rewrite Hselected.
    rewrite (r_index_same_target_and_size d q B basis alpha beta index Hequiv).
    reflexivity.
Qed.

Lemma in_list_has_nth_error : forall (A : Type) (value : A) values,
    List.In value values -> exists index, nth_error values index = Some value.
Proof.
  intros A value values Hin. induction values as [|head tail IH]; cbn in *.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst. exists 0. reflexivity.
    + destruct (IH Hin) as [index Hindex]. exists (S index). exact Hindex.
Qed.

Lemma r_index_nonempty : forall d q (B : SBVAS d q) basis alpha,
    RunBasis B basis -> ValidSRun B alpha ->
    exists index, index < length basis /\ RIndex B basis alpha index.
Proof.
  intros d q B basis alpha [_ Hcover] Hvalid.
  destruct (Hcover alpha Hvalid) as [sigma [Hin Hbelow]].
  destruct (in_list_has_nth_error _ _ _ Hin) as [index Hnth].
  exists index. split.
  - apply nth_error_Some. rewrite Hnth. discriminate.
  - exists sigma. split; [exact Hnth|].
    exists alpha. exists alpha. exists (srun_path_here alpha).
    split; [exact Hvalid|]. split.
    + apply same_target_and_size_refl.
    + exact Hbelow.
Qed.

Lemma r_cardinality_positive_bounded : forall d q (B : SBVAS d q) basis
    alpha cardinality,
    RunBasis B basis -> ValidSRun B alpha ->
    RCardinality B basis alpha cardinality ->
    0 < cardinality /\ cardinality <= length basis.
Proof.
  intros d q B basis alpha cardinality Hbasis Hvalid
    [selected [[Hnodup Hselected] Hlength]].
  destruct (r_index_nonempty d q B basis alpha Hbasis Hvalid)
    as [index [Hbound Hr]].
  assert (Hin : List.In index selected) by (apply Hselected; auto).
  split.
  - rewrite <- Hlength. destruct selected; [inversion Hin|cbn; lia].
  - rewrite <- Hlength.
    rewrite <- (length_seq (length basis) 0).
    apply NoDup_incl_length with (l := selected) (l' := seq 0 (length basis)).
    + exact Hnodup.
    + intros item Hitem. apply in_seq_zero_iff.
      apply Hselected in Hitem. exact (proj1 Hitem).
Qed.

Lemma nvec_add_zero_bounded : forall d (value : NVec d),
    nvec_add value (nvec_zero d) = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add, nvec_zero.
  rewrite (nth_map2 Nat.add value (Vector.const 0 d)
    index index index eq_refl eq_refl), Vector.const_nth. lia.
Qed.

Lemma r_index_subrun_inclusion : forall d q (B : SBVAS d q) basis
    whole subrun (outer : SRunPath whole subrun) index,
    ValidSRun B whole ->
    RIndex B basis subrun index -> RIndex B basis whole index.
Proof.
  intros d q B basis whole subrun outer index Hwhole
    [sigma [Hnth [representative [focus [inner
      [Hrepresentative [[Hroot Hnodes] Hbelow]]]]]]].
  assert (Hstate : fst (root_config representative) =
      fst (root_config subrun)) by now rewrite Hroot.
  assert (Hcounter : snd (root_config representative) =
      nvec_add (snd (root_config subrun)) (nvec_zero d)).
  { rewrite nvec_add_zero_bounded. now rewrite Hroot. }
  destruct (subrun_replacement_exact d q B whole subrun representative outer
    (nvec_zero d) Hwhole Hrepresentative Hstate Hcounter) as
    [replaced [Hdefinition [Hvalid [Hrootstate [Hrootcounter Hcount]]]]].
  exists sigma. split; [exact Hnth|].
  exists replaced, focus.
  subst replaced.
  exists (srun_path_into_replacement outer inner (nvec_zero d)).
  split; [exact Hvalid|]. split; [|exact Hbelow].
  split.
  - destruct (root_config whole) as [whole_state whole_counter] eqn:Hwhole_root.
    destruct (root_config
      (replace_subrun_at outer representative (nvec_zero d)))
      as [new_state new_counter] eqn:Hnew_root.
    cbn in Hrootstate, Hrootcounter |- *. subst new_state.
    rewrite nvec_add_zero_bounded in Hrootcounter. subst new_counter. reflexivity.
  - rewrite <- Hnodes in Hcount. lia.
Qed.

Lemma r_selection_subrun_incl : forall d q (B : SBVAS d q) basis
    whole subrun (path : SRunPath whole subrun) whole_selected sub_selected,
    ValidSRun B whole ->
    RSelection B basis whole whole_selected ->
    RSelection B basis subrun sub_selected ->
    incl sub_selected whole_selected.
Proof.
  intros d q B basis whole subrun path whole_selected sub_selected Hvalid
    [_ Hwhole] [_ Hsub] index Hin.
  apply Hwhole. apply Hsub in Hin. destruct Hin as [Hbound Hr]. split; auto.
  eapply r_index_subrun_inclusion; eauto.
Qed.

Lemma r_cardinality_subrun_le : forall d q (B : SBVAS d q) basis
    whole subrun (path : SRunPath whole subrun) whole_card sub_card,
    ValidSRun B whole ->
    RCardinality B basis whole whole_card ->
    RCardinality B basis subrun sub_card ->
    sub_card <= whole_card.
Proof.
  intros d q B basis whole subrun path whole_card sub_card Hvalid
    [whole_selected [[Hwhole_nd Hwhole] Hwhole_len]]
    [sub_selected [[Hsub_nd Hsub] Hsub_len]].
  rewrite <- Hwhole_len, <- Hsub_len.
  apply NoDup_incl_length; [exact Hsub_nd|].
  eapply (r_selection_subrun_incl d q B basis whole subrun path
    whole_selected sub_selected).
  - exact Hvalid.
  - split; assumption.
  - split; assumption.
Qed.

Definition config_inb {d q} (config : SConfig d q)
    (configs : list (SConfig d q)) : bool :=
  if in_dec sconfig_eq_dec config configs then true else false.

Definition bad_child_count {d q} (available : list (SConfig d q))
    (run : SRun d q) : nat :=
  match run with
  | srun_leaf _ => 0
  | srun_node _ children _ =>
      length (List.filter
        (fun config => negb (config_inb config available))
        (sruns_configs children))
  end.

Lemma config_inb_true_iff : forall d q (config : SConfig d q) configs,
    config_inb config configs = true <-> List.In config configs.
Proof.
  intros d q config configs. unfold config_inb.
  destruct (in_dec sconfig_eq_dec config configs); split; intro H; auto;
    discriminate.
Qed.

Lemma config_inb_false_iff : forall d q (config : SConfig d q) configs,
    config_inb config configs = false <-> ~ List.In config configs.
Proof.
  intros d q config configs. unfold config_inb.
  destruct (in_dec sconfig_eq_dec config configs); split; intro H; auto;
    try discriminate; contradiction.
Qed.

Definition SameClassBadCount {d q} (B : SBVAS d q)
    (available : list (SConfig d q)) (alpha : SRun d q) (count : nat) : Prop :=
  exists beta,
    ValidSRun B beta /\
    SameTargetAndSize alpha beta /\
    bad_child_count available beta = count.

Lemma bad_child_minimal_representative : forall d q (B : SBVAS d q)
    available alpha,
    ValidSRun B alpha ->
    exists alpha_min,
      ValidSRun B alpha_min /\
      SameTargetAndSize alpha alpha_min /\
      forall beta,
        ValidSRun B beta ->
        SameTargetAndSize alpha beta ->
        bad_child_count available alpha_min <= bad_child_count available beta.
Proof.
  intros d q B available alpha Hvalid.
  assert (Hex : exists count, SameClassBadCount B available alpha count).
  { exists (bad_child_count available alpha), alpha. repeat split; auto. }
  destruct (dec_inh_nat_subset_has_unique_least_element
    (fun count => SameClassBadCount B available alpha count)
    (fun count => classic (SameClassBadCount B available alpha count)) Hex)
    as [minimum [[Hminimum Hleast] _]].
  destruct Hminimum as [alpha_min [Hmin_valid [Hmin_same Hmin_count]]].
  exists alpha_min. split; [exact Hmin_valid|]. split; [exact Hmin_same|].
  intros beta Hbeta_valid Hbeta_same.
  rewrite Hmin_count. apply Hleast.
  exists beta. split; [exact Hbeta_valid|]. split; [exact Hbeta_same|reflexivity].
Qed.

Definition replace_two_children {d q} (rule : SRule d q)
    (before : SRuns d q) (first : SRun d q) (middle : SRuns d q)
    (second : SRun d q) (after : SRuns d q) (result : SConfig d q)
    (new_first new_second : SRun d q) : SRun d q :=
  srun_node rule
    (sruns_append before
      (sruns_cons new_first
        (sruns_append middle (sruns_cons new_second after)))) result.

Lemma sruns_append_assoc_bounded : forall d q
    (first second third : SRuns d q),
    sruns_append (sruns_append first second) third =
      sruns_append first (sruns_append second third).
Proof. intros d q first; induction first; intros; cbn; congruence. Qed.

Lemma nvec_sum_two_frame_exact : forall d before middle after
    (first second new_first new_second : NVec d),
    nvec_add first second = nvec_add new_first new_second ->
    nvec_sum (before ++ first :: middle ++ second :: after) =
      nvec_sum (before ++ new_first :: middle ++ new_second :: after).
Proof.
  intros d before middle after first second new_first new_second Heq.
  repeat (rewrite nvec_sum_app_extend || rewrite nvec_sum_cons_context).
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Hindex; subst index'.
  apply (f_equal (fun value => Vector.nth value index)) in Heq.
  unfold nvec_add in *.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in *.
  lia.
Qed.

Lemma add_displacement_two_frame_exact : forall d (offset : ZVec d)
    before middle after first second new_first new_second result,
    nvec_add first second = nvec_add new_first new_second ->
    add_displacement offset (before ++ first :: middle ++ second :: after) =
      Some result ->
    add_displacement offset
      (before ++ new_first :: middle ++ new_second :: after) = Some result.
Proof.
  intros d offset before middle after first second new_first new_second result
    Hpair Happly.
  pose proof (nvec_sum_two_frame_exact d before middle after first second
    new_first new_second Hpair) as Hsum.
  unfold add_displacement in *. now rewrite <- Hsum.
Qed.

Lemma valid_sruns_two_frame_replace : forall d q (B : SBVAS d q)
    before first middle second after new_first new_second,
    ValidSRuns B
      (sruns_append before
        (sruns_cons first (sruns_append middle (sruns_cons second after)))) ->
    ValidSRun B new_first -> ValidSRun B new_second ->
    ValidSRuns B
      (sruns_append before
        (sruns_cons new_first
          (sruns_append middle (sruns_cons new_second after)))).
Proof.
  intros d q B before. induction before as [|head tail IH];
    intros first middle second after new_first new_second
      Hvalid Hfirst Hsecond; cbn in *.
  - inversion Hvalid; subst. constructor; [exact Hfirst|].
    eapply valid_sruns_frame_replace_stateful; eauto.
  - inversion Hvalid; subst. constructor; [assumption|].
    eapply IH; eauto.
Qed.

Theorem simultaneous_sibling_replacement : forall d q (B : SBVAS d q)
    (rule : SRule d q) before first middle second after result
    new_first new_second,
    ValidSRun B
      (srun_node rule
        (sruns_append before
          (sruns_cons first (sruns_append middle (sruns_cons second after))))
        result) ->
    ValidSRun B new_first -> ValidSRun B new_second ->
    fst (root_config new_first) = fst (root_config first) ->
    fst (root_config new_second) = fst (root_config second) ->
    nvec_add (snd (root_config first)) (snd (root_config second)) =
      nvec_add (snd (root_config new_first)) (snd (root_config new_second)) ->
    run_node_count first + run_node_count second =
      run_node_count new_first + run_node_count new_second ->
    exists replaced,
      replaced = replace_two_children rule before first middle second after
        result new_first new_second /\
      ValidSRun B replaced /\
      root_config replaced =
        root_config
          (srun_node rule
            (sruns_append before
              (sruns_cons first
                (sruns_append middle (sruns_cons second after)))) result) /\
      run_node_count replaced =
        run_node_count
          (srun_node rule
            (sruns_append before
              (sruns_cons first
                (sruns_append middle (sruns_cons second after)))) result).
Proof.
  intros d q B rule before first middle second after result new_first new_second
    Hvalid Hnew_first Hnew_second Hfirst_state Hsecond_state
    Hcounter Hnodes.
  inversion Hvalid as [|? ? ? Hrule Hchildren Hstates Happly Houtput]; subst.
  exists (replace_two_children rule before first middle second after result
    new_first new_second). split; [reflexivity|]. split.
  - unfold replace_two_children. econstructor.
    + exact Hrule.
    + eapply valid_sruns_two_frame_replace; eauto.
    + repeat first [rewrite sruns_configs_append in Hstates |
        rewrite List.map_app in Hstates | progress cbn in Hstates].
      repeat first [rewrite sruns_configs_append |
        rewrite List.map_app | progress cbn].
      rewrite Hfirst_state, Hsecond_state. exact Hstates.
    + repeat first [rewrite sruns_configs_append in Happly |
        rewrite List.map_app in Happly | progress cbn in Happly].
      repeat first [rewrite sruns_configs_append |
        rewrite List.map_app | progress cbn].
      eapply add_displacement_two_frame_exact; eauto.
    + exact Houtput.
  - split; [reflexivity|].
    unfold replace_two_children.
    repeat first [rewrite runs_node_count_append | progress cbn]. lia.
Qed.

Theorem sibling_context_transfer_exact : forall d q (B : SBVAS d q)
    (rule : SRule d q) before first middle second after result
    sigma representative focus (inner : SRunPath representative focus),
    ValidSRun B
      (srun_node rule
        (sruns_append before
          (sruns_cons first (sruns_append middle (sruns_cons second after))))
        result) ->
    ValidSRun B sigma ->
    ValidSRun B representative ->
    SameTargetAndSize first representative ->
    ContextOrder B sigma second ->
    ContextOrder B sigma focus ->
    exists transferred whole',
      ValidSRun B transferred /\
      ValidSRun B whole' /\
      fst (root_config transferred) = fst (root_config first) /\
      root_config whole' =
        root_config
          (srun_node rule
            (sruns_append before
              (sruns_cons first
                (sruns_append middle (sruns_cons second after)))) result) /\
      run_node_count whole' =
        run_node_count
          (srun_node rule
            (sruns_append before
              (sruns_cons first
                (sruns_append middle (sruns_cons second after)))) result) /\
      whole' = replace_two_children rule before first middle second after result
        transferred sigma.
Proof.
  intros d q B rule before first middle second after result sigma representative
    focus inner Hwhole Hsigma Hrepresentative [Hrep_root Hrep_nodes]
    Hsigma_second Hsigma_focus.
  assert (Hsecond : ValidSRun B second).
  { inversion Hwhole; subst.
    eapply valid_sruns_frame_member_stateful with
      (before := sruns_append before (sruns_cons first middle))
      (after := after).
    rewrite sruns_append_assoc_bounded. cbn. exact H3. }
  destruct (stateful_context_transfer_lemma_8 d q B sigma second
    representative focus inner Hsigma Hsecond Hrepresentative
    Hsigma_second Hsigma_focus) as
    [transferred [Htransferred [_ [Htransferred_state
      [Hcounter Hnodes]]]]].
  assert (Hnew_first_state : fst (root_config transferred) =
      fst (root_config first)).
  { rewrite Htransferred_state, <- Hrep_root. reflexivity. }
  assert (Hnew_second_state : fst (root_config sigma) =
      fst (root_config second)).
  { eapply context_order_root_state; exact Hsigma_second. }
  assert (Hpair_counter :
      nvec_add (snd (root_config first)) (snd (root_config second)) =
      nvec_add (snd (root_config transferred)) (snd (root_config sigma))).
  { rewrite <- Hrep_root in Hcounter.
    apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros index index' Hindex; subst index'.
    apply (f_equal (fun value => Vector.nth value index)) in Hcounter.
    unfold nvec_add in *.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in *.
    lia. }
  assert (Hpair_nodes : run_node_count first + run_node_count second =
      run_node_count transferred + run_node_count sigma).
  { rewrite <- Hrep_nodes in Hnodes. lia. }
  destruct (simultaneous_sibling_replacement d q B rule before first middle
    second after result transferred sigma Hwhole Htransferred Hsigma
    Hnew_first_state Hnew_second_state Hpair_counter Hpair_nodes) as
    [whole' [Hwhole'_def [Hwhole'_valid [Hwhole'_root Hwhole'_nodes]]]].
  exists transferred, whole'. repeat split; assumption.
Qed.

Definition bad_config_count {d q} (available : list (SConfig d q))
    (configs : list (SConfig d q)) : nat :=
  length (List.filter
    (fun config => negb (config_inb config available)) configs).

Lemma bad_config_count_two_frame_decreases : forall d q
    (available : list (SConfig d q)) before middle after
    old_first old_second new_first new_second,
    ~ List.In old_first available ->
    ~ List.In old_second available ->
    List.In new_second available ->
    bad_config_count available
      (before ++ new_first :: middle ++ new_second :: after) <
    bad_config_count available
      (before ++ old_first :: middle ++ old_second :: after).
Proof.
  intros d q available before middle after old_first old_second new_first
    new_second Hfirst Hsecond Hnew_second.
  unfold bad_config_count.
  repeat first [rewrite filter_app | progress cbn].
  apply config_inb_false_iff in Hfirst.
  apply config_inb_false_iff in Hsecond.
  apply config_inb_true_iff in Hnew_second.
  rewrite Hfirst, Hsecond, Hnew_second. cbn.
  destruct (config_inb new_first available); cbn;
    repeat first [rewrite length_app | progress cbn]; lia.
Qed.

Lemma sibling_context_transfer_reduces_bad_children : forall d q
    (B : SBVAS d q) available
    (rule : SRule d q) before first middle second after result
    sigma representative focus (inner : SRunPath representative focus),
    ValidSRun B
      (srun_node rule
        (sruns_append before
          (sruns_cons first (sruns_append middle (sruns_cons second after))))
        result) ->
    ValidSRun B sigma -> ValidSRun B representative ->
    SameTargetAndSize first representative ->
    ContextOrder B sigma second -> ContextOrder B sigma focus ->
    ~ List.In (root_config first) available ->
    ~ List.In (root_config second) available ->
    List.In (root_config sigma) available ->
    exists whole',
      ValidSRun B whole' /\
      SameTargetAndSize
        (srun_node rule
          (sruns_append before
            (sruns_cons first (sruns_append middle (sruns_cons second after))))
          result) whole' /\
      bad_child_count available whole' <
        bad_child_count available
          (srun_node rule
            (sruns_append before
              (sruns_cons first
                (sruns_append middle (sruns_cons second after)))) result).
Proof.
  intros d q B available rule before first middle second after result sigma
    representative focus inner Hwhole Hsigma Hrep Hsame Hsecond Hfocus
    Hfirst_bad Hsecond_bad Hsigma_good.
  destruct (sibling_context_transfer_exact d q B rule before first middle
    second after result sigma representative focus inner Hwhole Hsigma Hrep
    Hsame Hsecond Hfocus) as
    [transferred [whole' [Htransferred [Hwhole'
      [Hstate [Hroot [Hnodes Hdefinition]]]]]]].
  exists whole'. split; [exact Hwhole'|]. split.
  - split; [symmetry; exact Hroot|symmetry; exact Hnodes].
  - subst whole'. unfold bad_child_count, replace_two_children. cbn.
    repeat first [rewrite sruns_configs_append | progress cbn].
    apply bad_config_count_two_frame_decreases; assumption.
Qed.

Definition srun_path_cast_whole {d q} {left right focus : SRun d q}
    (Heq : left = right) (path : SRunPath left focus) : SRunPath right focus :=
  match Heq with eq_refl => path end.

Lemma second_child_path : forall d q (rule : SRule d q)
    before first middle second after result,
    SRunPath
      (srun_node rule
        (sruns_append before
          (sruns_cons first (sruns_append middle (sruns_cons second after))))
        result) second.
Proof.
  intros d q rule before first middle second after result.
  apply (srun_path_cast_whole
    (f_equal (fun children => srun_node rule children result)
      (sruns_append_assoc_bounded d q before (sruns_cons first middle)
        (sruns_cons second after)))).
  apply srun_path_child. apply srun_path_here.
Qed.

Lemma r_index_parent_from_second : forall d q (B : SBVAS d q) basis
    (rule : SRule d q) before first middle second after result index sigma,
    nth_error basis index = Some sigma ->
    ValidSRun B
      (srun_node rule
        (sruns_append before
          (sruns_cons first (sruns_append middle (sruns_cons second after))))
        result) ->
    ContextOrder B sigma second ->
    RIndex B basis
      (srun_node rule
        (sruns_append before
          (sruns_cons first (sruns_append middle (sruns_cons second after))))
        result) index.
Proof.
  intros d q B basis rule before first middle second after result index sigma
    Hnth Hvalid Hbelow.
  exists sigma. split; [exact Hnth|].
  exists (srun_node rule
    (sruns_append before
      (sruns_cons first (sruns_append middle (sruns_cons second after)))) result).
  exists second. exists (second_child_path d q rule before first middle second after result).
  split; [exact Hvalid|]. split; [apply same_target_and_size_refl|exact Hbelow].
Qed.

Theorem r_index_excluded_from_bad_sibling : forall d q (B : SBVAS d q)
    basis available (rule : SRule d q) before first middle second after result
    index sigma,
    nth_error basis index = Some sigma ->
    RunBasis B basis ->
    ValidSRun B
      (srun_node rule
        (sruns_append before
          (sruns_cons first (sruns_append middle (sruns_cons second after))))
        result) ->
    ContextOrder B sigma second ->
    ~ List.In (root_config first) available ->
    ~ List.In (root_config second) available ->
    List.In (root_config sigma) available ->
    (forall beta,
      ValidSRun B beta ->
      SameTargetAndSize
        (srun_node rule
          (sruns_append before
            (sruns_cons first (sruns_append middle (sruns_cons second after))))
          result) beta ->
      bad_child_count available
        (srun_node rule
          (sruns_append before
            (sruns_cons first (sruns_append middle (sruns_cons second after))))
          result) <= bad_child_count available beta) ->
    ~ RIndex B basis first index.
Proof.
  intros d q B basis available rule before first middle second after result
    index sigma Hnth [Hbasis_valid _] Hwhole Hbelow Hfirst_bad Hsecond_bad
    Hsigma_good Hminimal Hr.
  destruct Hr as [sigma' [Hnth' [representative [focus [inner
    [Hrep_valid [Hsame Hfocus]]]]]]].
  rewrite Hnth in Hnth'. inversion Hnth'; subst sigma'.
  assert (Hsigma_valid : ValidSRun B sigma) by (apply Hbasis_valid; eapply nth_error_In; eauto).
  destruct (sibling_context_transfer_reduces_bad_children d q B available
    rule before first middle second after result sigma representative focus inner
    Hwhole Hsigma_valid Hrep_valid Hsame Hbelow Hfocus Hfirst_bad Hsecond_bad
    Hsigma_good) as [whole' [Hwhole'_valid [Hwhole'_same Hdecrease]]].
  pose proof (Hminimal whole' Hwhole'_valid Hwhole'_same). lia.
Qed.

(** A proof-only annotation keeps each omission decision attached to its
    complete configuration while input occurrences are permuted. *)
Definition OmissionAnnotation (d q : nat) :=
  (Fin.t q * option (NVec d))%type.

Definition annotation_state {d q} (entry : OmissionAnnotation d q) : Fin.t q :=
  fst entry.

Fixpoint annotation_retained {d q} (entries : list (OmissionAnnotation d q)) :=
  match entries with
  | [] => []
  | (state, None) :: tail => state :: annotation_retained tail
  | (_, Some _) :: tail => annotation_retained tail
  end.

Fixpoint annotation_omitted {d q} (entries : list (OmissionAnnotation d q)) :
    list (SConfig d q) :=
  match entries with
  | [] => []
  | (_, None) :: tail => annotation_omitted tail
  | (state, Some counters) :: tail =>
      (state, counters) :: annotation_omitted tail
  end.

Definition AnnotationAvailable {d q} (available : list (SConfig d q))
    (entry : OmissionAnnotation d q) : Prop :=
  match entry with
  | (_, None) => True
  | (state, Some counters) => List.In (state, counters) available
  end.

Lemma omission_selection_annotations : forall d q available inputs retained omitted,
    @OmissionSelection d q available inputs retained omitted ->
    exists entries : list (OmissionAnnotation d q),
      List.map annotation_state entries = inputs /\
      List.Forall (AnnotationAvailable available) entries /\
      annotation_retained entries = retained /\
      annotation_omitted entries = omitted.
Proof.
  intros d q available inputs retained omitted Hselection.
  induction Hselection as [|state inputs retained omitted Htail IH|
    state counters inputs retained omitted Hin Htail IH].
  - exists []. repeat split; constructor.
  - destruct IH as [entries [Hstates [Havailable [Hretained Homitted]]]].
    exists ((state, None) :: entries). split.
    + cbn. now rewrite Hstates.
    + split.
      * constructor; [exact I|exact Havailable].
      * split; [cbn; now rewrite Hretained|cbn; exact Homitted].
  - destruct IH as [entries [Hstates [Havailable [Hretained Homitted]]]].
    exists ((state, Some counters) :: entries). split.
    + cbn. now rewrite Hstates.
    + split.
      * constructor; [exact Hin|exact Havailable].
      * split; [cbn; exact Hretained|cbn; now rewrite Homitted].
Qed.

Lemma annotations_omission_selection : forall d q available
    (entries : list (OmissionAnnotation d q)) inputs,
    List.map annotation_state entries = inputs ->
    List.Forall (AnnotationAvailable available) entries ->
    OmissionSelection available inputs
      (annotation_retained entries) (annotation_omitted entries).
Proof.
  intros d q available entries. induction entries as [|[state choice] tail IH];
    intros inputs Hstates Havailable; cbn in *; subst inputs.
  - constructor.
  - inversion Havailable; subst. destruct choice as [counters|]; cbn in *.
    + constructor; [exact H1|]. apply IH; auto.
    + constructor. apply IH; auto.
Qed.

Lemma annotation_retained_permutation : forall d q
    (left right : list (OmissionAnnotation d q)),
    Permutation left right ->
    Permutation (annotation_retained left) (annotation_retained right).
Proof.
  intros d q left right Hperm. induction Hperm; cbn; auto.
  - destruct x as [state choice]. destruct choice; cbn; auto.
  - destruct x as [sx ox], y as [sy oy].
    destruct ox, oy; cbn; auto using perm_swap.
  - eapply Permutation_trans; eauto.
Qed.

Lemma annotation_omitted_permutation : forall d q
    (left right : list (OmissionAnnotation d q)),
    Permutation left right ->
    Permutation (annotation_omitted left) (annotation_omitted right).
Proof.
  intros d q left right Hperm. induction Hperm; cbn; auto.
  - destruct x as [state choice]. destruct choice; cbn; auto.
  - destruct x as [sx ox], y as [sy oy].
    destruct ox, oy; cbn; auto using perm_swap.
  - eapply Permutation_trans; eauto.
Qed.

Lemma annotation_available_permutation : forall d q available
    (left right : list (OmissionAnnotation d q)),
    Permutation left right ->
    List.Forall (AnnotationAvailable available) left ->
    List.Forall (AnnotationAvailable available) right.
Proof.
  intros. eapply Permutation_Forall; eauto.
Qed.

Theorem omission_selection_permutation_transport : forall d q available
    inputs inputs' retained omitted,
    Permutation inputs inputs' ->
    @OmissionSelection d q available inputs retained omitted ->
    exists retained' omitted',
      OmissionSelection available inputs' retained' omitted' /\
      Permutation retained retained' /\
      Permutation omitted omitted'.
Proof.
  intros d q available inputs inputs' retained omitted Hinputs Hselection.
  destruct (omission_selection_annotations d q available inputs retained omitted
    Hselection) as [entries [Hstates [Havailable [Hretained Homitted]]]].
  assert (Hmapped : Permutation inputs'
      (List.map annotation_state entries)).
  { rewrite Hstates. now apply Permutation_sym. }
  destruct (@Permutation_map_inv (OmissionAnnotation d q) (Fin.t q)
    annotation_state inputs' entries Hmapped) as
    [entries' [Hstates' Hentries]].
  exists (annotation_retained entries'), (annotation_omitted entries').
  split.
  - eapply annotations_omission_selection.
    + symmetry. exact Hstates'.
    + eapply annotation_available_permutation; eauto.
  - split.
    + rewrite <- Hretained. now apply annotation_retained_permutation.
    + rewrite <- Homitted. now apply annotation_omitted_permutation.
Qed.

Inductive ChildPartition {d q} (available : list (SConfig d q))
    (P : SRun d q -> SRun d q -> Prop) :
    SRuns d q -> SRuns d q -> list (SConfig d q) -> Prop :=
| child_partition_nil : ChildPartition available P sruns_nil sruns_nil []
| child_partition_keep : forall old tail new new_tail omitted,
    ~ List.In (root_config old) available ->
    P old new ->
    root_config new = root_config old ->
    ChildPartition available P tail new_tail omitted ->
    ChildPartition available P (sruns_cons old tail)
      (sruns_cons new new_tail) omitted
| child_partition_omit : forall old tail new_tail omitted,
    List.In (root_config old) available ->
    ChildPartition available P tail new_tail omitted ->
    ChildPartition available P (sruns_cons old tail)
      new_tail (root_config old :: omitted).

Lemma child_partition_selection : forall d q available P old new omitted,
    @ChildPartition d q available P old new omitted ->
    OmissionSelection available
      (List.map fst (sruns_configs old))
      (List.map fst (sruns_configs new)) omitted.
Proof.
  intros d q available P old new omitted Hpartition.
  induction Hpartition; cbn.
  - constructor.
  - rewrite H1. cbn. constructor. exact IHHpartition.
  - destruct (root_config old) as [state counters] eqn:Hroot. cbn in *.
    constructor; [exact H|exact IHHpartition].
Qed.

Lemma child_partition_configs_permutation : forall d q available P old new omitted,
    @ChildPartition d q available P old new omitted ->
    Permutation (sruns_configs old) (sruns_configs new ++ omitted).
Proof.
  intros d q available P old new omitted Hpartition.
  induction Hpartition; cbn.
  - constructor.
  - rewrite H1. constructor. exact IHHpartition.
  - eapply Permutation_trans.
    + constructor. exact IHHpartition.
    + apply Permutation_middle.
Qed.

Lemma child_partition_bad_length : forall d q available P old new omitted,
    @ChildPartition d q available P old new omitted ->
    length (sruns_configs new) =
      bad_config_count available (sruns_configs old).
Proof.
  intros d q available P old new omitted Hpartition.
  induction Hpartition; cbn.
  - reflexivity.
  - apply config_inb_false_iff in H.
    unfold bad_config_count in *. cbn in *. rewrite H. cbn. lia.
  - apply config_inb_true_iff in H.
    unfold bad_config_count in *. cbn in *. rewrite H. cbn. exact IHHpartition.
Qed.

Lemma child_partition_new_valid : forall d q available P old new omitted
    (B' : SBVAS d q),
    @ChildPartition d q available P old new omitted ->
    (forall old_run new_run, P old_run new_run -> ValidSRun B' new_run) ->
    ValidSRuns B' new.
Proof.
  intros d q available P old new omitted B' Hpartition HP.
  induction Hpartition.
  - constructor.
  - constructor; [eapply HP; eauto|exact IHHpartition].
  - exact IHHpartition.
Qed.

Lemma child_partition_exists : forall d q available (P : SRun d q -> SRun d q -> Prop)
    old (B : SBVAS d q),
    ValidSRuns B old ->
    (forall run, ValidSRun B run -> ~ List.In (root_config run) available ->
      exists new, P run new /\ root_config new = root_config run) ->
    exists new omitted, ChildPartition available P old new omitted.
Proof.
  intros d q available P old B Hvalid Hconstruct.
  induction Hvalid as [|run tail Hrun Htail IH].
  - exists sruns_nil, []. constructor.
  - destruct IH as [new_tail [omitted Hpartition]].
    destruct (in_dec sconfig_eq_dec (root_config run) available) as [Hin|Hout].
    + exists new_tail, (root_config run :: omitted). constructor; assumption.
    + destruct (Hconstruct run Hrun Hout) as [new [HP Hroot]].
      exists (sruns_cons new new_tail), omitted. econstructor; eauto.
Qed.

Lemma nvec_sum_permutation_bounded : forall d (left right : list (NVec d)),
    Permutation left right -> nvec_sum left = nvec_sum right.
Proof.
  intros d left right Hperm. repeat rewrite nvec_sum_rsum_stateful.
  now apply nvec_rsum_permutation_stateful.
Qed.

Lemma child_partition_counter_sum : forall d q available P old new omitted,
    @ChildPartition d q available P old new omitted ->
    nvec_sum (List.map snd (sruns_configs old)) =
      nvec_sum
        (List.map snd (sruns_configs new) ++ List.map snd omitted).
Proof.
  intros d q available P old new omitted Hpartition.
  apply nvec_sum_permutation_bounded.
  rewrite <- List.map_app.
  apply Permutation_map. now apply child_partition_configs_permutation with
    (available := available) (P := P).
Qed.

Theorem child_partition_extend_shortening : forall d q (B : SBVAS d q)
    available (rule : SRule d q) old_children result P new_children omitted,
    ValidSRun B (srun_node rule old_children (output_state rule, result)) ->
    @ChildPartition d q available P old_children new_children omitted ->
    (forall old new, P old new ->
      ValidSRun (extend_bvass B available) new) ->
    exists retained' omitted' shortened,
      OmissionSelection available (input_states rule) retained' omitted' /\
      Permutation (List.map fst (sruns_configs new_children)) retained' /\
      Permutation omitted omitted' /\
      ValidSRun (extend_bvass B available) shortened /\
      root_config shortened = (output_state rule, result) /\
      RetainedChildrenOccurrence retained' new_children shortened /\
      length retained' = bad_config_count available (sruns_configs old_children).
Proof.
  intros d q B available rule old_children result P new_children omitted
    Hnode Hpartition HPvalid.
  inversion Hnode as [|? ? ? Hrule Hchildren Hstates Happly Houtput]; subst.
  pose proof (child_partition_selection d q available P old_children
    new_children omitted Hpartition) as Hselection.
  destruct (omission_selection_permutation_transport d q available
    (List.map fst (sruns_configs old_children)) (input_states rule)
    (List.map fst (sruns_configs new_children)) omitted Hstates Hselection) as
    [retained' [omitted' [Hselection' [Hretained Homitted]]]].
  assert (Hnew_valid : ValidSRuns (extend_bvass B available) new_children).
  { eapply child_partition_new_valid; eauto. }
  assert (Hcounter_perm : Permutation
      (List.map snd (sruns_configs old_children))
      (List.map snd (sruns_configs new_children) ++ List.map snd omitted')).
  { eapply Permutation_trans with
      (l' := List.map snd (sruns_configs new_children ++ omitted)).
    - apply Permutation_map.
      eapply child_partition_configs_permutation; eauto.
    - rewrite List.map_app. apply Permutation_app_head.
      now apply Permutation_map. }
  assert (Happly' : add_displacement (rule_delta rule)
      (List.map snd (sruns_configs new_children) ++ List.map snd omitted') =
      Some result).
  { cbn in Happly. rewrite <- Happly.
    now apply add_displacement_permutation. }
  destruct (extend_local_root_shortening d q B available rule retained' omitted'
    new_children result Hrule Hselection' Hnew_valid Hretained Happly') as
    [shortened [Hshort_valid [Hshort_root [Hoccurrence [Hlength _]]]]].
  exists retained', omitted', shortened. repeat split; try assumption.
  pose proof (Permutation_length Hretained) as Hretained_length.
  rewrite length_map in Hretained_length.
  pose proof (child_partition_bad_length d q available P old_children
    new_children omitted Hpartition) as Hbad_length.
  rewrite <- Hbad_length. symmetry. exact Hretained_length.
Qed.

Theorem r_cardinality_strict_from_excluded_index : forall d q
    (B : SBVAS d q) basis parent child parent_card child_card excluded,
    RCardinality B basis parent parent_card ->
    RCardinality B basis child child_card ->
    (forall index, RIndex B basis child index ->
      RIndex B basis parent index) ->
    excluded < length basis ->
    RIndex B basis parent excluded ->
    ~ RIndex B basis child excluded ->
    child_card < parent_card.
Proof.
  intros d q B basis parent child parent_card child_card excluded
    [parent_indices [[Hparent_nodup Hparent_spec] Hparent_len]]
    [child_indices [[Hchild_nodup Hchild_spec] Hchild_len]]
    Hinclusion Hexcluded_bound Hexcluded_parent Hexcluded_child.
  assert (Hexcluded_in_parent : List.In excluded parent_indices).
  { apply Hparent_spec. auto. }
  assert (Hexcluded_not_child : ~ List.In excluded child_indices).
  { intro Hin. apply Hchild_spec in Hin. tauto. }
  assert (Hincluded : incl (excluded :: child_indices) parent_indices).
  { intros index [Heq|Hin].
    - subst. exact Hexcluded_in_parent.
    - apply Hparent_spec. apply Hchild_spec in Hin.
      destruct Hin as [Hbound Hr]. split; [exact Hbound|now apply Hinclusion]. }
  assert (Hnodup : NoDup (excluded :: child_indices)).
  { constructor; assumption. }
  pose proof (NoDup_incl_length Hnodup Hincluded) as Hlength.
  cbn in Hlength. rewrite Hchild_len, Hparent_len in Hlength. lia.
Qed.

Lemma sruns_in_remove_bounded : forall d q (run : SRun d q) runs,
    SRunsIn run runs -> exists remainder, SRunsRemove run runs remainder.
Proof.
  intros d q run runs Hin. induction Hin.
  - exists runs. constructor.
  - destruct IHHin as [remainder Hremove].
    exists (sruns_cons other remainder). now constructor 2.
Qed.

Lemma bad_config_count_permutation : forall d q available
    (left right : list (SConfig d q)),
    Permutation left right ->
    bad_config_count available left = bad_config_count available right.
Proof.
  intros d q available left right Hperm. unfold bad_config_count.
  induction Hperm; cbn.
  - reflexivity.
  - destruct (negb (config_inb x available)); cbn; now rewrite IHHperm.
  - destruct (negb (config_inb x available)),
      (negb (config_inb y available)); cbn; lia.
  - now rewrite IHHperm1, IHHperm2.
Qed.

Lemma bad_config_count_cons_bad : forall d q available
    (run : SRun d q) configs,
    ~ List.In (root_config run) available ->
    bad_config_count available (root_config run :: configs) =
      S (bad_config_count available configs).
Proof.
  intros d q available run configs Hbad. unfold bad_config_count. cbn.
  apply config_inb_false_iff in Hbad. now rewrite Hbad.
Qed.

Lemma bad_run_exists_frame : forall d q available (runs : SRuns d q),
    0 < bad_config_count available (sruns_configs runs) ->
    exists before bad after,
      runs = sruns_append before (sruns_cons bad after) /\
      ~ List.In (root_config bad) available.
Proof.
  intros d q available runs. induction runs as [|head tail IH]; cbn.
  - unfold bad_config_count. cbn. lia.
  - intro Hpositive.
    destruct (in_dec sconfig_eq_dec (root_config head) available) as [Hin|Hout].
    + assert (Hbool : config_inb (root_config head) available = true)
        by now apply config_inb_true_iff.
      unfold bad_config_count in Hpositive. cbn in Hpositive. rewrite Hbool in Hpositive.
      destruct (IH Hpositive) as [before [bad [after [Heq Hbad]]]].
      exists (sruns_cons head before), bad, after. cbn. now rewrite Heq.
    + exists sruns_nil, head, tail. split; [reflexivity|exact Hout].
Qed.

Lemma sruns_reorder_selected_first : forall d q (selected : SRun d q)
    children remainder,
    SRunsRemove selected children remainder ->
    SRunsIsomorphic (sruns_cons selected remainder) children.
Proof.
  intros d q selected children remainder Hremove.
  eapply sruns_iso_cons with (right := selected) (remainder := remainder).
  - exact Hremove.
  - apply (proj1 (srun_isomorphic_refl_mut d q)).
  - apply (proj2 (srun_isomorphic_refl_mut d q)).
Qed.

Lemma reordered_bad_child_node : forall d q (B : SBVAS d q) available
    (rule : SRule d q) children result selected remainder,
    ValidSRun B (srun_node rule children result) ->
    SRunsRemove selected children remainder ->
    ~ List.In (root_config selected) available ->
    2 <= bad_config_count available (sruns_configs children) ->
    exists middle second after,
      remainder = sruns_append middle (sruns_cons second after) /\
      ~ List.In (root_config second) available /\
      ValidSRun B (srun_node rule (sruns_cons selected remainder) result) /\
      SameTargetAndSize
        (srun_node rule children result)
        (srun_node rule (sruns_cons selected remainder) result) /\
      bad_child_count available (srun_node rule children result) =
        bad_child_count available
          (srun_node rule (sruns_cons selected remainder) result).
Proof.
  intros d q B available rule children result selected remainder Hvalid Hremove
    Hselected_bad Htwo.
  pose proof (sruns_remove_configs_permutation d q selected children remainder
    Hremove) as Hconfigs.
  assert (Hcount : bad_config_count available (root_config selected ::
      sruns_configs remainder) = bad_config_count available (sruns_configs children)).
  { now apply bad_config_count_permutation. }
  rewrite (bad_config_count_cons_bad d q available selected
    (sruns_configs remainder) Hselected_bad) in Hcount.
  assert (Hremaining : 0 < bad_config_count available (sruns_configs remainder))
    by lia.
  destruct (bad_run_exists_frame d q available remainder Hremaining)
    as [middle [second [after [Hframe Hsecond_bad]]]].
  exists middle, second, after. split; [exact Hframe|]. split; [exact Hsecond_bad|].
  assert (Hiso_children : SRunsIsomorphic
      (sruns_cons selected remainder) children).
  { now apply sruns_reorder_selected_first. }
  assert (Hiso_node : SRunIsomorphic
      (srun_node rule (sruns_cons selected remainder) result)
      (srun_node rule children result)) by (constructor; exact Hiso_children).
  split.
  - eapply srun_isomorphic_valid.
    + apply srun_isomorphic_sym_stateful. exact Hiso_node.
    + exact Hvalid.
  - split.
    + split.
      * reflexivity.
      * symmetry. now apply srun_isomorphic_node_count.
    + change (bad_config_count available (sruns_configs children) =
        bad_config_count available (root_config selected :: sruns_configs remainder)).
	      rewrite (bad_config_count_cons_bad d q available selected
	        (sruns_configs remainder) Hselected_bad).
	      symmetry. exact Hcount.
Qed.

Theorem r_index_excluded_from_any_bad_child : forall d q (B : SBVAS d q)
    basis available (rule : SRule d q) children result child,
    RunBasis B basis ->
    (forall sigma, List.In sigma basis ->
      List.In (root_config sigma) available) ->
    ValidSRun B (srun_node rule children result) ->
    SRunsIn child children ->
    ~ List.In (root_config child) available ->
    2 <= bad_child_count available (srun_node rule children result) ->
    (forall beta,
      ValidSRun B beta ->
      SameTargetAndSize (srun_node rule children result) beta ->
      bad_child_count available (srun_node rule children result) <=
        bad_child_count available beta) ->
    exists index sigma,
      nth_error basis index = Some sigma /\
      List.In (root_config sigma) available /\
      RIndex B basis (srun_node rule children result) index /\
      ~ RIndex B basis child index.
Proof.
  intros d q B basis available rule children result child Hbasis Hbasis_available
    Hvalid Hin Hchild_bad Htwo Hminimal.
  destruct (sruns_in_remove_bounded d q child children Hin)
    as [remainder Hremove].
  destruct (reordered_bad_child_node d q B available rule children result child
    remainder Hvalid Hremove Hchild_bad Htwo)
    as [middle [second [after [Hframe [Hsecond_bad
      [Hreordered [Hequiv Hbad_eq]]]]]]].
  subst remainder.
  destruct Hbasis as [Hbasis_valid Hcover].
  assert (Hsecond_valid : ValidSRun B second).
  { inversion Hreordered as [|? ? ? ? Hchildren ? ? ?]; subst.
    eapply valid_sruns_frame_member_stateful with
      (before := sruns_cons child middle) (after := after).
    cbn. exact Hchildren. }
  destruct (Hcover second Hsecond_valid) as [sigma [Hsigma_in Hbelow]].
  destruct (in_list_has_nth_error _ sigma basis Hsigma_in) as [index Hnth].
  exists index, sigma. split; [exact Hnth|]. split; [now apply Hbasis_available|].
  split.
  - apply (proj2 (r_index_same_target_and_size d q B basis
      (srun_node rule children result)
      (srun_node rule
        (sruns_cons child (sruns_append middle (sruns_cons second after))) result)
      index Hequiv)).
    exact (r_index_parent_from_second d q B basis rule sruns_nil child middle
      second after result index sigma Hnth Hreordered Hbelow).
  - eapply (r_index_excluded_from_bad_sibling d q B basis available rule
    sruns_nil child middle second after result index sigma Hnth).
    + split; assumption.
    + cbn. exact Hreordered.
    + exact Hbelow.
    + exact Hchild_bad.
    + exact Hsecond_bad.
    + now apply Hbasis_available.
    + intros beta Hbeta_valid Hbeta_same.
      cbn in Hbeta_same.
      change (bad_child_count available
        (srun_node rule
          (sruns_cons child (sruns_append middle (sruns_cons second after))) result)
        <= bad_child_count available beta).
      rewrite <- Hbad_eq.
      apply Hminimal; [exact Hbeta_valid|].
      eapply same_target_and_size_trans; [exact Hequiv|exact Hbeta_same].
Qed.

Lemma sruns_remove_frame_bounded : forall d q (child : SRun d q) children rest,
    SRunsRemove child children rest ->
    exists before after,
      children = sruns_append before (sruns_cons child after).
Proof.
  intros d q child children rest Hremove. induction Hremove.
  - exists sruns_nil, runs. reflexivity.
  - destruct IHHremove as [before [after Heq]].
    exists (sruns_cons head before), after. cbn. now rewrite Heq.
Qed.

Lemma sruns_in_direct_path : forall d q (rule : SRule d q) children result child,
    SRunsIn child children ->
    exists path : SRunPath (srun_node rule children result) child, True.
Proof.
  intros d q rule children result child Hin.
  destruct (sruns_in_remove_bounded d q child children Hin) as [rest Hremove].
  destruct (sruns_remove_frame_bounded d q child children rest Hremove)
    as [before [after Heq]]. subst children.
  exists (srun_path_child rule before child after result child
    (srun_path_here child)). exact I.
Qed.

Theorem bad_child_r_cardinality_strict : forall d q (B : SBVAS d q)
    basis available (rule : SRule d q) children result child
    parent_card child_card,
    RunBasis B basis ->
    (forall sigma, List.In sigma basis ->
      List.In (root_config sigma) available) ->
    ValidSRun B (srun_node rule children result) ->
    SRunsIn child children ->
    ~ List.In (root_config child) available ->
    2 <= bad_child_count available (srun_node rule children result) ->
    (forall beta,
      ValidSRun B beta ->
      SameTargetAndSize (srun_node rule children result) beta ->
      bad_child_count available (srun_node rule children result) <=
        bad_child_count available beta) ->
    RCardinality B basis (srun_node rule children result) parent_card ->
    RCardinality B basis child child_card ->
    child_card < parent_card.
Proof.
  intros d q B basis available rule children result child parent_card child_card
    Hbasis Hbasis_available Hvalid Hin Hbad Htwo Hminimal Hparent Hchild.
  destruct (r_index_excluded_from_any_bad_child d q B basis available rule
    children result child Hbasis Hbasis_available Hvalid Hin Hbad Htwo Hminimal)
    as [index [sigma [Hnth [Hsigma_good [Hparent_index Hchild_index]]]]].
  eapply r_cardinality_strict_from_excluded_index; eauto.
  - intros item Hitem.
    destruct (sruns_in_direct_path d q rule children result child Hin)
      as [path _].
    eapply r_index_subrun_inclusion; eauto.
  - apply nth_error_Some. rewrite Hnth. discriminate.
Qed.

Inductive ForallSRuns {d q} (P : SRun d q -> Prop) : SRuns d q -> Prop :=
| forall_sruns_nil : ForallSRuns P sruns_nil
| forall_sruns_cons : forall run tail,
    P run -> ForallSRuns P tail -> ForallSRuns P (sruns_cons run tail).

Lemma child_partition_forall_new : forall d q available P old new omitted
    (Q : SRun d q -> Prop),
    @ChildPartition d q available P old new omitted ->
    (forall old_run new_run, P old_run new_run -> Q new_run) ->
    ForallSRuns Q new.
Proof.
  intros d q available P old new omitted Q Hpartition HP.
  induction Hpartition.
  - constructor.
  - constructor; [now apply HP with old|exact IHHpartition].
  - exact IHHpartition.
Qed.

Lemma forall_sruns_max_lt : forall d q (runs : SRuns d q) bound,
    0 < bound ->
    ForallSRuns (fun run => branching_depth run < bound) runs ->
    runs_max_branching_depth runs < bound.
Proof.
  intros d q runs bound Hpositive Hall. induction Hall; cbn; lia.
Qed.

Lemma forall_sruns_succ_max_lt : forall d q (runs : SRuns d q) bound,
    1 < bound ->
    ForallSRuns (fun run => S (branching_depth run) < bound) runs ->
    S (runs_max_branching_depth runs) < bound.
Proof.
  intros d q runs bound Hpositive Hall. induction Hall; cbn; lia.
Qed.

Lemma sruns_in_node_count_le : forall d q (run : SRun d q) runs,
    SRunsIn run runs -> run_node_count run <= runs_node_count runs.
Proof. intros d q run runs Hin. induction Hin; cbn; lia. Qed.

Lemma direct_child_node_count_lt : forall d q (rule : SRule d q)
    children result child,
    SRunsIn child children ->
    run_node_count child < run_node_count (srun_node rule children result).
Proof.
  intros. cbn. pose proof (sruns_in_node_count_le d q child children H). lia.
Qed.

Definition BoundedChildReplacement {d q} (B : SBVAS d q)
    (basis : list (SRun d q)) (parent_card : nat)
    (old new : SRun d q) : Prop :=
  exists child_card,
    RCardinality B basis old child_card /\
    ValidSRun (extend_bvass B (basis_root_configs basis)) new /\
    root_config new = root_config old /\
    branching_depth new < child_card /\
    child_card <= parent_card.

Lemma bounded_child_replacement_depth : forall d q (B : SBVAS d q) basis
    parent_card old new,
    BoundedChildReplacement B basis parent_card old new ->
    branching_depth new < parent_card.
Proof. intros d q B basis parent_card old new [card [_ [_ [_ [Hdepth Hle]]]]]; lia. Qed.

Lemma bounded_child_replacement_succ_depth : forall d q (B : SBVAS d q) basis
    parent_card old new,
    BoundedChildReplacement B basis parent_card old new ->
    RunBasis B basis ->
    (exists rule children result,
      ValidSRun B (srun_node rule children result) /\
      SRunsIn old children /\
      ~ List.In (root_config old) (basis_root_configs basis) /\
      2 <= bad_child_count (basis_root_configs basis)
        (srun_node rule children result) /\
      (forall beta,
        ValidSRun B beta ->
        SameTargetAndSize (srun_node rule children result) beta ->
        bad_child_count (basis_root_configs basis)
          (srun_node rule children result) <=
        bad_child_count (basis_root_configs basis) beta) /\
      RCardinality B basis (srun_node rule children result) parent_card) ->
    S (branching_depth new) < parent_card.
Proof.
  intros d q B basis parent_card old new
    [child_card [Hchild_card [_ [_ [Hdepth Hle]]]]]
    Hbasis
    [rule [children [result [Hvalid [Hin [Hbad [Htwo [Hminimal Hparent]]]]]]]].
  assert (Hbasis_roots : forall sigma, List.In sigma basis ->
      List.In (root_config sigma) (basis_root_configs basis)).
  { intros sigma Hsigma. apply in_map. exact Hsigma. }
  pose proof (bad_child_r_cardinality_strict d q B basis
    (basis_root_configs basis) rule children result old parent_card child_card
    Hbasis Hbasis_roots Hvalid Hin Hbad Htwo Hminimal Hparent Hchild_card).
  lia.
Qed.

Lemma child_partition_exists_with_occurrence : forall d q available
    (P : SRun d q -> SRun d q -> Prop) old (B : SBVAS d q),
    ValidSRuns B old ->
    (forall run,
      ValidSRun B run -> SRunsIn run old ->
      ~ List.In (root_config run) available ->
      exists new, P run new /\ root_config new = root_config run) ->
    exists new omitted, ChildPartition available P old new omitted.
Proof.
  intros d q available P old B Hvalid Hconstruct.
  induction Hvalid as [|run tail Hrun Htail IH].
  - exists sruns_nil, []. constructor.
  - assert (Htail_construct : forall child,
      ValidSRun B child -> SRunsIn child tail ->
      ~ List.In (root_config child) available ->
      exists new, P child new /\ root_config new = root_config child).
    { intros child Hchild Hin Hbad. apply Hconstruct; auto. now constructor 2. }
    destruct (IH Htail_construct) as [new_tail [omitted Hpartition]].
    destruct (in_dec sconfig_eq_dec (root_config run) available) as [Hin|Hout].
    + exists new_tail, (root_config run :: omitted). constructor; assumption.
    + destruct (Hconstruct run Hrun (sruns_in_here run tail) Hout)
        as [new [HP Hroot]].
      exists (sruns_cons new new_tail), omitted. econstructor; eauto.
Qed.

Theorem bounded_branching_by_r_cardinality : forall d q (B : SBVAS d q) basis,
    RunBasis B basis ->
    forall alpha cardinality,
      ValidSRun B alpha ->
      RCardinality B basis alpha cardinality ->
      exists eta,
        ValidSRun (extend_bvass B (basis_root_configs basis)) eta /\
        root_config eta = root_config alpha /\
        branching_depth eta < cardinality.
Proof.
  intros d q B basis Hbasis.
  assert (Hbasis_roots : forall sigma, List.In sigma basis ->
      List.In (root_config sigma) (basis_root_configs basis)).
  { intros sigma Hsigma. apply in_map. exact Hsigma. }
  intro alpha.
  remember (run_node_count alpha) as measure eqn:Hmeasure.
  revert alpha Hmeasure.
  induction measure using lt_wf_ind; intros alpha Hmeasure cardinality Hvalid Hcard.
  destruct (bad_child_minimal_representative d q B
    (basis_root_configs basis) alpha Hvalid)
    as [minimal [Hminimal_valid [Hsame Hminimal]]].
  assert (Hminimal_measure : run_node_count minimal = measure).
  { destruct Hsame as [_ Hnodes]. lia. }
  assert (Hminimal_card : RCardinality B basis minimal cardinality).
  { apply (proj1 (r_cardinality_invariant d q B basis alpha minimal
      cardinality Hsame)). exact Hcard. }
  destruct (r_cardinality_positive_bounded d q B basis minimal cardinality
    Hbasis Hminimal_valid Hminimal_card) as [Hcard_positive Hcard_bound].
  destruct minimal as [config|rule children result].
  - exists (srun_leaf config). split.
    + now apply original_valid_run_in_extension.
    + split.
      * destruct Hsame as [Hroot _]. cbn in Hroot |- *. symmetry. exact Hroot.
      * cbn. exact Hcard_positive.
  - inversion Hminimal_valid as
      [|? ? ? Hrule Hchildren Hstates Happly Houtput]; subst.
    destruct result as [result_state result_counters]. cbn in Houtput. subst result_state.
    set (P := fun old new =>
      BoundedChildReplacement B basis cardinality old new /\
      SRunsIn old children /\
      ~ List.In (root_config old) (basis_root_configs basis)).
    assert (Hconstruct : forall child,
      ValidSRun B child -> SRunsIn child children ->
      ~ List.In (root_config child) (basis_root_configs basis) ->
      exists new, P child new /\ root_config new = root_config child).
    { intros child Hchild Hin Hbad.
      destruct (r_cardinality_exists d q B basis child) as [child_card Hchild_card].
      assert (Hchild_measure : run_node_count child < run_node_count alpha).
      { rewrite (proj2 Hsame). now apply direct_child_node_count_lt
          with (rule := rule) (children := children)
            (result := (output_state rule, result_counters)). }
      destruct (H (run_node_count child) Hchild_measure child eq_refl child_card
        Hchild Hchild_card) as [new [Hnew_valid [Hnew_root Hnew_depth]]].
      assert (Hchild_le : child_card <= cardinality).
      { destruct (sruns_in_direct_path d q rule children
          (output_state rule, result_counters) child Hin)
          as [path _].
        eapply r_cardinality_subrun_le; eauto. }
      exists new. split.
      - split.
        + exists child_card. repeat split; assumption.
        + split; assumption.
      - exact Hnew_root. }
    destruct (child_partition_exists_with_occurrence d q
      (basis_root_configs basis) P children B Hchildren Hconstruct)
      as [new_children [omitted Hpartition]].
    destruct (child_partition_extend_shortening d q B
      (basis_root_configs basis) rule children result_counters P new_children omitted
      Hminimal_valid Hpartition) as
      [retained [omitted' [shortened [Hselection [Hretained [Homitted
        [Hshort_valid [Hshort_root [Hoccurrence Hretained_length]]]]]]]]].
    { intros old new HP. unfold P, BoundedChildReplacement in HP.
      destruct HP as [[child_card [_ [Hnew_valid _]]] _]. exact Hnew_valid. }
    exists shortened. split; [exact Hshort_valid|]. split.
    + cbn in Hshort_root, Hsame |- *. rewrite Hshort_root.
      symmetry. exact (proj1 Hsame).
    + assert (Hall : ForallSRuns
          (fun run => branching_depth run < cardinality) new_children).
      { eapply child_partition_forall_new; [exact Hpartition|].
        intros old new HP. destruct HP as [Hbounded _].
        now apply bounded_child_replacement_depth in Hbounded. }
      destruct retained as [|retained_head retained_tail].
      * destruct Hoccurrence as [leaf_config Hleaf]. subst shortened. cbn.
        exact Hcard_positive.
      * destruct Hoccurrence as [short_rule [short_config Hshort]].
        subst shortened.
        pose proof (Permutation_length Hretained) as Hnew_length.
        rewrite length_map in Hnew_length.
        destruct retained_tail as [|retained_second retained_tail].
        -- rewrite branching_depth_node_formula.
	           change (length (sruns_configs new_children) = 1) in Hnew_length.
	           assert (Hleb : Nat.leb 2 (length (sruns_configs new_children)) = false).
	           { rewrite Hnew_length. reflexivity. }
	           rewrite Hleb.
           now apply forall_sruns_max_lt.
        -- assert (Htwo : 2 <= bad_child_count (basis_root_configs basis)
              (srun_node rule children (output_state rule, result_counters))).
           { change (2 <= bad_config_count (basis_root_configs basis)
                (sruns_configs children)).
             rewrite <- Hretained_length. cbn. lia. }
           assert (Hall_succ : ForallSRuns
              (fun run => S (branching_depth run) < cardinality) new_children).
           { eapply child_partition_forall_new; [exact Hpartition|].
             intros old new HP.
             destruct HP as [Hbounded [Hin Hbad]].
             eapply bounded_child_replacement_succ_depth;
               [exact Hbounded|exact Hbasis|].
             exists rule, children, (output_state rule, result_counters).
	             repeat split; try assumption.
	             intros beta Hbeta_valid Hbeta_same.
	             apply Hminimal; [exact Hbeta_valid|].
	             eapply same_target_and_size_trans; [exact Hsame|exact Hbeta_same].
           }
           assert (Hcard_two : 1 < cardinality).
           { inversion Hall_succ; subst; cbn in Hnew_length; lia. }
           rewrite branching_depth_node_formula.
	           change (length (sruns_configs new_children) =
	             S (S (length retained_tail))) in Hnew_length.
	           assert (Hleb : Nat.leb 2 (length (sruns_configs new_children)) = true).
	           { apply Nat.leb_le. rewrite Hnew_length. lia. }
	           rewrite Hleb.
           now apply forall_sruns_succ_max_lt.
Qed.

Theorem finite_basis_bounded_branching_depth : forall d q (B : SBVAS d q) basis,
    RunBasis B basis ->
    forall alpha,
      ValidSRun B alpha ->
      exists eta,
        ValidSRun (extend_bvass B (basis_root_configs basis)) eta /\
        root_config eta = root_config alpha /\
        branching_depth eta <= Nat.pred (length basis).
Proof.
  intros d q B basis Hbasis alpha Hvalid.
  destruct (r_cardinality_exists d q B basis alpha) as [cardinality Hcard].
  destruct (bounded_branching_by_r_cardinality d q B basis Hbasis alpha
    cardinality Hvalid Hcard) as [eta [Heta [Hroot Hdepth]]].
  destruct (r_cardinality_positive_bounded d q B basis alpha cardinality
    Hbasis Hvalid Hcard) as [Hpositive Hbounded].
  exists eta. split; [exact Heta|]. split; [exact Hroot|].
  destruct (length basis); cbn in *; lia.
Qed.

Lemma proof_basis_run_basis : forall d q (B : SBVAS d q)
    (proof_basis : list {run : SRun d q | ValidSRun B run}),
    (forall run : {run : SRun d q | ValidSRun B run},
      exists base, List.In base proof_basis /\
        ContextOrder B (proj1_sig base) (proj1_sig run)) ->
    RunBasis B (List.map (@proj1_sig _ (fun run => ValidSRun B run)) proof_basis).
Proof.
  intros d q B proof_basis Hcover. split.
  - intros run Hin. apply in_map_iff in Hin.
    destruct Hin as [proof_run [Heq Hin]]. subst run. exact (proj2_sig proof_run).
  - intros run Hvalid.
    destruct (Hcover (exist (fun candidate => ValidSRun B candidate) run Hvalid))
      as [base [Hin Hbelow]].
    exists (proj1_sig base). split.
    + apply in_map. exact Hin.
    + exact Hbelow.
Qed.

Theorem lemma_9_uniform_bounded_branching : forall d q (B : SBVAS d q),
    exists F bound,
      ReachableConfigurations B F /\
      forall alpha,
        ValidSRun B alpha ->
        exists eta,
          ValidSRun (extend_bvass B F) eta /\
          root_config eta = root_config alpha /\
          branching_depth eta <= bound.
Proof.
  intros d q B.
  destruct (context_order_finite_cover d q B) as [proof_basis Hcover].
  set (basis := List.map (@proj1_sig _ (fun run => ValidSRun B run)) proof_basis).
  assert (Hbasis : RunBasis B basis).
  { unfold basis. now apply proof_basis_run_basis. }
  exists (basis_root_configs basis), (Nat.pred (length basis)). split.
  - now apply run_basis_root_configs_reachable.
  - intros alpha Hvalid. now apply finite_basis_bounded_branching_depth.
Qed.

Theorem lemma_9_reach_bounded_branching_iff : forall d q (B : SBVAS d q),
    exists F bound,
      ReachableConfigurations B F /\
      forall state counters,
        SReach B state counters <->
        exists eta,
          ValidSRun (extend_bvass B F) eta /\
          root_config eta = (state, counters) /\
          branching_depth eta <= bound.
Proof.
  intros d q B.
  destruct (lemma_9_uniform_bounded_branching d q B)
    as [F [bound [Hreachable Hbounded]]].
  exists F, bound. split; [exact Hreachable|]. intros state counters. split.
  - intro Hreach. apply stateful_run_reach_iff in Hreach.
    destruct Hreach as [alpha [Hvalid Hroot]].
    destruct (Hbounded alpha Hvalid) as [eta [Heta [Hetaroot Hdepth]]].
    exists eta. split; [exact Heta|]. split; [congruence|exact Hdepth].
  - intros [eta [Heta [Hroot Hdepth]]].
    assert (Hextend : SReach (extend_bvass B F) state counters).
    { apply stateful_run_reach_iff. exists eta. split; assumption. }
    apply (proj1 (extend_bvass_reach_iff d q B F Hreachable state counters)).
    exact Hextend.
Qed.
