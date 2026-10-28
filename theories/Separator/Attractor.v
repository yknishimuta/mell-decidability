From Coq Require Import Classical_Prop Lia List Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Contexts.
From Mell.Separator Require Import SafeLinearization.
From Mell.WSVAS Require Import BVASSimulation.
From Mell.BVAS Require Import OneSourceReduction.

Import ListNotations.

Definition InitialNSet {d} (system : IBVAS d) : NVec d -> Prop :=
  fun value => List.In value (initial_vectors system).

(** We use Fact 3.6's equivalent [Reach(S)] formulation.  It keeps the
    distinguished occurrences supplied by [SourceMultiShuffle], and is the
    form consumed in Section 7. *)
Definition Attractor {d} (system : IBVAS d) (set : NVec d -> Prop) : Prop :=
  forall target,
    ReachFromNonemptyShuffle system set (Reach system) target -> set target.

Lemma source_multi_shuffle_map_right : forall d
    (left right right' : NVec d -> Prop) word,
  (forall value, right value -> right' value) ->
  SourceMultiShuffle left right word ->
  SourceMultiShuffle left right' word.
Proof.
  intros d left right right' word Hmap
    [xs [is [Hxs [Hleft [Hright Hperm]]]]].
  exists xs, is. repeat split; auto.
  eapply List.Forall_impl; [|exact Hright]. exact Hmap.
Qed.

Lemma initial_is_reachable : forall d (system : IBVAS d) value,
  InitialNSet system value -> Reach system value.
Proof.
  intros d system value Hin.
  apply In_nth_error in Hin as [index Hindex].
  eapply reach_initial. exact Hindex.
Qed.

Lemma attractor_initial_form : forall d (system : IBVAS d) set,
  Attractor system set ->
  forall target,
    ReachFromNonemptyShuffle system set (InitialNSet system) target ->
    set target.
Proof.
  intros d system set Hattr target Hreach. apply Hattr.
  destruct Hreach as [run [Hvalid [Htarget Hshuffle]]].
  exists run. repeat split; auto.
  eapply source_multi_shuffle_map_right; [|exact Hshuffle].
  apply initial_is_reachable.
Qed.

Lemma list_partition_union : forall d
    (left right : NVec d -> Prop) word,
  List.Forall (fun value => left value \/ right value) word ->
  exists xs is,
    List.Forall left xs /\ List.Forall right is /\
    Permutation word (xs ++ is) /\
    (HasSource left word -> xs <> []).
Proof.
  intros d left right word Hall.
  induction Hall as [|head tail Hhead Htail
    [xs [is [Hxs [His [Hperm Hnonempty]]]]]].
  - exists [], []. repeat split; auto.
    intros [value [[] _]].
  - destruct (classic (left head)) as [Hleft|Hnotleft].
    + exists (head :: xs), is. repeat split.
      * constructor; assumption.
      * exact His.
      * cbn. now apply perm_skip.
      * discriminate.
    + assert (Hright : right head) by tauto.
      exists xs, (head :: is). repeat split.
      * exact Hxs.
      * constructor; assumption.
      * eapply Permutation_trans; [apply perm_skip; exact Hperm|].
        apply Permutation_middle.
      * intros [value [[<-|Hin] Hvalue]]; [contradiction|].
        apply Hnonempty. now exists value.
Qed.

Lemma source_multi_shuffle_partition : forall d
    (left right : NVec d -> Prop) word,
  List.Forall (fun value => left value \/ right value) word ->
  HasSource left word ->
  SourceMultiShuffle left right word.
Proof.
  intros d left right word Hall Hsource.
  destruct (list_partition_union d left right word Hall) as
    [xs [is [Hxs [His [Hperm Hnonempty]]]]].
  exists xs, is. repeat split; auto.
Qed.

Fixpoint free_leaf_runs {d} (values : list (NVec d)) : IRuns d :=
  match values with
  | [] => iruns_nil
  | value :: tail => iruns_cons (irun_leaf value) (free_leaf_runs tail)
  end.

Lemma free_leaf_runs_targets : forall d (values : list (NVec d)),
  iruns_targets (free_leaf_runs values) = values.
Proof. intros d values; induction values; cbn; congruence. Qed.

Lemma free_leaf_runs_sources : forall d (values : list (NVec d)),
  free_iruns_sources (free_leaf_runs values) = values.
Proof. intros d values; induction values; cbn; congruence. Qed.

Lemma free_leaf_runs_valid : forall d (system : IBVAS d)
    (values : list (NVec d)),
  ValidFreeIRuns system (free_leaf_runs values).
Proof. intros d system values; induction values; constructor; auto; constructor. Qed.

Lemma forall_reach_children : forall d (system : IBVAS d) children,
  List.Forall (Reach system) children -> ReachChildren system children.
Proof.
  intros d system children Hchildren.
  induction Hchildren as [|child tail Hchild Htail IH].
  - apply reach_children_nil.
  - apply reach_children_cons; assumption.
Qed.

Lemma reach_action_in : forall d (system : IBVAS d) action children target,
  List.In action (system_actions system) ->
  List.Forall (Reach system) children ->
  apply_action action children = Some target ->
  Reach system target.
Proof.
  intros d system action children target Haction Hchildren Happly.
  apply In_nth_error in Haction as [index Hindex].
  pose proof (forall_reach_children d system children Hchildren) as Hreaches.
  econstructor; [exact Hindex|exact Hreaches|exact Happly].
Qed.

Lemma attractor_union_reach_inductive : forall d (system : IBVAS d) set,
  Attractor system set ->
  IBVASInductiveInvariant system (fun value => set value \/ Reach system value).
Proof.
  intros d system set Hattr. split.
  - intros value Hinitial. right. now apply initial_is_reachable.
  - intros action children target Haction Hall Happly.
    change (set target \/ Reach system target).
    destruct (classic (HasSource set children)) as [Hhas|Hnone].
    + left. apply Hattr. exists (irun_node action (free_leaf_runs children) target).
      split.
      * econstructor; eauto using free_leaf_runs_valid.
        now rewrite free_leaf_runs_targets.
      * split; [reflexivity|]. cbn. rewrite free_leaf_runs_sources.
        now apply source_multi_shuffle_partition.
    + right. eapply reach_action_in with
        (action := action) (children := children).
      * exact Haction.
      *
      apply List.Forall_forall. intros value Hin.
      rewrite List.Forall_forall in Hall.
      pose proof (Hall value Hin) as Hvalue.
      destruct Hvalue as [Hset|Hreach]; [exfalso|exact Hreach].
      apply Hnone. now exists value.
      * exact Happly.
Qed.

Lemma reach_in_inductive_invariant : forall d (system : IBVAS d) set,
  IBVASInductiveInvariant system set ->
  (forall value, Reach system value -> set value) /\
  (forall values, ReachChildren system values -> List.Forall set values).
Proof.
  intros d system set Hinvariant.
  apply (Reach_mutind d system
    (fun value _ => set value)
    (fun values _ => List.Forall set values)).
  - intros index value Hindex.
    exact (proj1 Hinvariant _ (nth_error_In _ _ Hindex)).
  - intros index action children value Haction _ Hall Happly.
    eapply (proj2 Hinvariant); eauto using nth_error_In.
  - constructor.
  - intros value values _ Hvalue _ Hvalues. constructor; assumption.
Qed.

Lemma inductive_invariant_attractor : forall d (system : IBVAS d) set,
  IBVASInductiveInvariant system set -> Attractor system set.
Proof.
  intros d system set Hinvariant target
    [run [Hvalid [<- Hshuffle]]].
  apply (proj1 (inductive_invariant_free_runs system set Hinvariant))
    with (run := run); [exact Hvalid|].
  destruct Hshuffle as [xs [is [Hxs [Hxs_set [His_reach Hperm]]]]].
  eapply Permutation_Forall; [apply Permutation_sym; exact Hperm|].
  apply List.Forall_app. split; [exact Hxs_set|].
  eapply List.Forall_impl; [|exact His_reach].
  intros value Hreach.
  exact (proj1 (reach_in_inductive_invariant d system set Hinvariant)
    value Hreach).
Qed.

Lemma attractor_with_initials_inductive : forall d (system : IBVAS d) set,
  Attractor system set ->
  (forall value, InitialNSet system value -> set value) ->
  IBVASInductiveInvariant system set.
Proof.
  intros d system set Hattr Hinitial.
  split; [exact Hinitial|].
  intros action children target Haction Hall Happly.
  apply Hattr. exists (irun_node action (free_leaf_runs children) target).
  split.
  - econstructor; eauto using free_leaf_runs_valid.
    now rewrite free_leaf_runs_targets.
  - split; [reflexivity|]. cbn. rewrite free_leaf_runs_sources.
    exists children, []. split.
    + intro Heq. subst children.
      unfold apply_action in Happly.
      destruct action as [arity Hpositive displacement]. cbn in *.
      destruct arity; [lia|discriminate].
    + split; [exact Hall|]. split; [constructor|now rewrite app_nil_r].
Qed.

(** Lemma 3.7 is proved in [WitnessUpdate], together with the marked-run
    flattening operation it needs. *)
