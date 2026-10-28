From Coq Require Import List Vector Lia Sorting.Permutation Classical_Prop.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Contexts RunOrder.
From Mell.VAS Require Import Intraproductions.
From Mell.WSVAS Require Import BVASSimulation.

Import ListNotations.

Definition SourceMultiShuffle {d} (X I : NVec d -> Prop)
    (word : list (NVec d)) : Prop :=
  exists xs is,
    xs <> [] /\ List.Forall X xs /\ List.Forall I is /\
    Permutation word (xs ++ is).

Definition ReachFromNonemptyShuffle {d} (S : IBVAS d)
    (X I : NVec d -> Prop) (target : NVec d) : Prop :=
  exists run,
    ValidFreeIRun S run /\ irun_target run = target /\
    SourceMultiShuffle X I (free_irun_sources run).

Definition NSetMinkowskiN {d} (left right : NVec d -> Prop)
    (value : NVec d) : Prop :=
  exists l r, left l /\ right r /\ value = nvec_add l r.

Definition NSetStable {d} (X P : NVec d -> Prop) : Prop :=
  forall x p, X x -> P p -> X (nvec_add x p).

Definition HasSource {d} (X : NVec d -> Prop) (word : list (NVec d)) : Prop :=
  exists value, List.In value word /\ X value.

Lemma has_source_app : forall d (X : NVec d -> Prop) left right,
  HasSource X (left ++ right) <-> HasSource X left \/ HasSource X right.
Proof.
  intros d X left right. unfold HasSource. setoid_rewrite in_app_iff.
  firstorder.
Qed.

Lemma forall_union_no_source : forall d (X I : NVec d -> Prop) word,
  List.Forall (fun value => X value \/ I value) word ->
  ~ HasSource X word -> List.Forall I word.
Proof.
  intros d X I word Hall Hnone. induction Hall as [|head tail Hhead Htail IH].
  - constructor.
  - constructor.
    + destruct Hhead as [HX|HI]; [exfalso|exact HI].
      apply Hnone. exists head. cbn. auto.
    + apply IH. intros [value [Hin HX]]. apply Hnone.
      exists value. cbn. auto.
Qed.

Lemma source_multi_shuffle_characterization : forall d
    (X I : NVec d -> Prop) word,
  SourceMultiShuffle X I word ->
  List.Forall (fun value => X value \/ I value) word /\ HasSource X word.
Proof.
  intros d X I word [xs [is [Hne [HX [HI Hperm]]]]]. split.
  - eapply Permutation_Forall; [apply Permutation_sym; exact Hperm|].
    apply List.Forall_app. split.
    + eapply List.Forall_impl; [|exact HX]. firstorder.
    + eapply List.Forall_impl; [|exact HI]. firstorder.
  - destruct xs as [|x xs]; [contradiction|].
    exists x. split; [|now inversion HX].
    eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
    apply in_or_app. left. cbn; auto.
Qed.

(* A direct constructive partition, used below, avoids relying on the converse
   characterization in the presence of several X occurrences. *)
Lemma source_multi_shuffle_forall : forall d (X I : NVec d -> Prop) word,
  SourceMultiShuffle X I word ->
  List.Forall (fun value => X value \/ I value) word /\ HasSource X word.
Proof. intros; now apply source_multi_shuffle_characterization. Qed.

Section OneSource.
Context {d : nat} (S : IBVAS d).
Variables X I P : NVec d -> Prop.

Hypothesis Hclosed : ClosedUnderFreeRuns S I.
Hypothesis Hperiodic : PeriodicNSet P.
Hypothesis Hstable : NSetStable X P.
Hypothesis Hreach : forall target,
  ReachFromShuffle S X I target -> NSetMinkowskiN I P target.

Lemma marked_free_shift : forall run offset,
  MarkedFreeIRun S X I run -> P offset ->
  exists shifted,
    MarkedFreeIRun S X I shifted /\
    irun_target shifted = nvec_add (irun_target run) offset.
Proof.
  intros run offset Hmarked. induction Hmarked; intro HP.
  - exists (irun_leaf (nvec_add value offset)). split; cbn; auto.
    constructor. now apply Hstable.
  - destruct (IHHmarked HP) as [shifted [Hshifted Htarget]].
    exists (irun_node action
      (iruns_append before (iruns_cons shifted after))
      (nvec_add target offset)). split; [|reflexivity].
    econstructor; eauto.
    repeat rewrite iruns_targets_append_free in H4 |- *. cbn in H4 |- *.
    eapply apply_action_frame_shift; eauto.
Qed.

Lemma apply_action_same_sum : forall (action : Action d)
    (old_children new_children : list (NVec d)) (target : NVec d),
  length old_children = length new_children ->
  nvec_sum old_children = nvec_sum new_children ->
  apply_action action old_children = Some target ->
  apply_action action new_children = Some target.
Proof.
  intros action old_children new_children target Hlen Hsum Happly.
  unfold apply_action in Happly |- *. rewrite <- Hlen.
  destruct (Nat.eqb (length old_children) (action_arity action));
    [|discriminate].
  unfold add_displacement in Happly |- *. now rewrite <- Hsum.
Qed.

Lemma transfer_sum : forall (head base offset : NVec d)
    (before after : list (NVec d)),
  nvec_rsum
    (nvec_add head offset :: before ++ base :: after) =
  nvec_rsum
    (head :: before ++ nvec_add base offset :: after).
Proof.
  intros. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  cbn [nvec_rsum].
  rewrite (nvec_rsum_app d before (base :: after)),
    (nvec_rsum_app d before (nvec_add base offset :: after)).
  cbn [nvec_rsum]. unfold nvec_add.
  repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Definition CompressRun (run : IRun d) : Prop :=
  exists compressed,
    MarkedFreeIRun S X I compressed /\
    irun_target compressed = irun_target run.

Definition CompressRuns (runs : IRuns d) : Prop :=
  exists compressed,
    MarkedFreeIRunsSplit S X I compressed /\
    length (iruns_targets compressed) = length (iruns_targets runs) /\
    nvec_sum (iruns_targets compressed) = nvec_sum (iruns_targets runs).

Combined Scheme ValidFreeIRun_IRuns_ind
  from ValidFreeIRun_ind', ValidFreeIRuns_ind'.

Lemma compress_free_run :
  (forall run, ValidFreeIRun S run ->
    List.Forall (fun value => X value \/ I value)
      (free_irun_sources run) ->
    HasSource X (free_irun_sources run) -> CompressRun run) /\
  (forall runs, ValidFreeIRuns S runs ->
    List.Forall (fun value => X value \/ I value)
      (free_iruns_sources runs) ->
    HasSource X (free_iruns_sources runs) -> CompressRuns runs).
Proof.
  apply ValidFreeIRun_IRuns_ind; intros.
  - cbn in *. destruct H0 as [special [[Heq|[]] HX]]; subst value.
    exists (irun_leaf special). split; [constructor; assumption|reflexivity].
  - cbn in H0, H1. unfold CompressRun.
    destruct (H H0 H1) as [new_children
      [[before [main [after [Hshape [Hbefore [Hafter
        [HbeforeI [HafterI Hmain]]]]]]]] [Hlen Hsum]]].
    exists (irun_node action new_children target). split; [|reflexivity].
    subst new_children. econstructor; eauto.
    eapply apply_action_same_sum; [symmetry; exact Hlen|symmetry; exact Hsum|].
    exact e.
  - cbn in H0. destruct H0 as [value [[] _]].
  - cbn in H1, H2. apply List.Forall_app in H1 as [Hrun_all Htail_all].
    destruct (classic (HasSource X (free_irun_sources run)))
      as [Hrun_has|Hrun_none].
    + destruct (H Hrun_all Hrun_has) as [new_run [Hnew_run Hnew_target]].
      destruct (classic (HasSource X (free_iruns_sources runs)))
        as [Htail_has|Htail_none].
      * destruct (H0 Htail_all Htail_has) as [new_tail
          [[before [main [after [Hshape [Hbefore [Hafter
            [HbeforeI [HafterI Hmain]]]]]]]] [Hlen Hsum]]].
        subst new_tail.
        assert (Hmain_reach : ReachFromShuffle S X I (irun_target main)).
        { now apply marked_free_reach_from_shuffle. }
        destruct (Hreach _ Hmain_reach) as [base [offset [HIbase [HP Hoff]]]].
        destruct (marked_free_shift new_run offset Hnew_run HP)
          as [shifted [Hshifted Hshifted_target]].
        set (tail' := iruns_append before
          (iruns_cons (irun_leaf base) after)).
        exists (iruns_cons shifted tail'). split.
        -- exists iruns_nil, shifted, tail'. split; [reflexivity|].
           split; [constructor|]. split.
           ++ unfold tail'. apply valid_free_iruns_append; auto.
              constructor; [constructor|exact Hafter].
           ++ split; [constructor|]. split.
              ** unfold AllFreeSources, tail'.
                 rewrite free_iruns_sources_append. cbn.
                 apply List.Forall_app. split.
                 --- exact HbeforeI.
                 --- constructor; [exact HIbase|exact HafterI].
              ** exact Hshifted.
        -- split.
           ++ cbn. unfold tail'. repeat rewrite iruns_targets_append_free. cbn.
              repeat rewrite iruns_targets_append_free in Hlen. cbn in Hlen.
              repeat rewrite length_app in Hlen |- *. cbn in Hlen |- *. lia.
           ++ unfold tail'.
              cbn [iruns_targets irun_target].
              rewrite iruns_targets_append_free.
              cbn [iruns_targets irun_target].
              repeat rewrite iruns_targets_append_free in Hsum. cbn in Hsum.
              repeat rewrite nvec_sum_rsum in Hsum |- *.
              rewrite Hoff in Hsum.
              rewrite Hshifted_target, Hnew_target.
              rewrite (transfer_sum (irun_target run) base offset
                (iruns_targets before) (iruns_targets after)).
              cbn [nvec_rsum]. now rewrite Hsum.
      * assert (HtailI : List.Forall I (free_iruns_sources runs)).
        { now apply forall_union_no_source with X. }
        exists (iruns_cons new_run runs). split.
        -- exists iruns_nil, new_run, runs. split; [reflexivity|].
           split; [constructor|]. split; [exact v0|].
           split; [constructor|]. split; [exact HtailI|exact Hnew_run].
        -- split.
           ++ cbn; reflexivity.
           ++ cbn [iruns_targets]. rewrite Hnew_target. reflexivity.
    + assert (Htail_has : HasSource X (free_iruns_sources runs)).
      { apply (proj1 (has_source_app d X _ _)) in H2.
        destruct H2; contradiction || assumption. }
      assert (HrunI : List.Forall I (free_irun_sources run)).
      { now apply forall_union_no_source with X. }
      assert (HItarget : I (irun_target run)).
      { apply Hclosed; assumption. }
      destruct (H0 Htail_all Htail_has) as [new_tail
        [[before [main [after [Hshape [Hbefore [Hafter
          [HbeforeI [HafterI Hmain]]]]]]]] [Hlen Hsum]]].
      subst new_tail. exists (iruns_cons run
        (iruns_append before (iruns_cons main after))). split.
      * exists (iruns_cons run before), main, after. split; [reflexivity|].
        split; [constructor; assumption|]. split; [exact Hafter|].
        split.
        -- unfold AllFreeSources in *. cbn. apply List.Forall_app. auto.
        -- split; [exact HafterI|exact Hmain].
      * split.
        -- change (Nat.succ (length (iruns_targets
             (iruns_append before (iruns_cons main after)))) =
             Nat.succ (length (iruns_targets runs))). now rewrite Hlen.
        -- change (nvec_sum (irun_target run :: iruns_targets
             (iruns_append before (iruns_cons main after))) =
             nvec_sum (irun_target run :: iruns_targets runs)).
           repeat rewrite nvec_sum_rsum in Hsum |- *.
           cbn [nvec_rsum]. now rewrite Hsum.
Qed.

Theorem multi_source_compress : forall run,
  ValidFreeIRun S run ->
  SourceMultiShuffle X I (free_irun_sources run) ->
  exists compressed,
    MarkedFreeIRun S X I compressed /\
    irun_target compressed = irun_target run.
Proof.
  intros run Hvalid Hmulti.
  destruct (source_multi_shuffle_forall d X I _ Hmulti) as [Hall Hhas].
  exact ((proj1 compress_free_run) run Hvalid Hall Hhas).
Qed.

End OneSource.

Theorem lemma_5_7_one_source_reduction : forall d (S : IBVAS d)
    (I P X : NVec d -> Prop),
  ClosedUnderFreeRuns S I ->
  PeriodicNSet P ->
  NSetStable X P ->
  (forall target, ReachFromShuffle S X I target ->
    NSetMinkowskiN I P target) ->
  forall target,
    ReachFromShuffle S X I target <->
    ReachFromNonemptyShuffle S X I target.
Proof.
  intros d S I P X Hclosed Hperiodic Hstable Hreach target. split.
  - intros [run [Hvalid [Htarget Hshuffle]]]. exists run.
    repeat split; auto.
    destruct Hshuffle as [prefix [special [suffix
      [Hword [HX [Hpre Hsuf]]]]]].
    exists [special], (prefix ++ suffix). split; [discriminate|].
    split; [constructor; auto|]. split.
    + now apply List.Forall_app.
    + rewrite Hword. exact (Permutation_sym (Permutation_middle prefix suffix special)).
  - intros [run [Hvalid [Htarget Hmulti]]].
    destruct (multi_source_compress S X I P Hclosed Hstable Hreach
      run Hvalid Hmulti) as [compressed [Hmarked Hcompressed]].
    exists compressed. split.
    + exact (marked_free_valid S X I compressed Hmarked).
    + split; [congruence|].
      exact (marked_free_source_shuffle S X I compressed Hmarked).
Qed.
