From Coq Require Import List Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Contexts OneSourceReduction.
From Mell.WSVAS Require Import BVASSimulation.

Import ListNotations.

Definition Language (d : nat) := list (NVec d) -> Prop.

Definition NonemptyLanguage {d} (language : Language d) : Prop :=
  forall word, language word -> word <> [].

Inductive WordShuffle {A : Type} : list A -> list A -> list A -> Prop :=
| word_shuffle_nil : WordShuffle [] [] []
| word_shuffle_left : forall value left right output,
    WordShuffle left right output ->
    WordShuffle (value :: left) right (value :: output)
| word_shuffle_right : forall value left right output,
    WordShuffle left right output ->
    WordShuffle left (value :: right) (value :: output).

Definition LanguageShuffle {d} (left right : Language d) : Language d :=
  fun output => exists left_word right_word,
    left left_word /\ right right_word /\
    WordShuffle left_word right_word output.

Inductive LanguageStar {d} (language : Language d) : Language d :=
| language_star_nil : LanguageStar language []
| language_star_cons : forall word tail,
    language word -> LanguageStar language tail ->
    LanguageStar language (word ++ tail).

Definition LanguagePlus {d} (language : Language d) : Language d :=
  fun output => exists word tail,
    language word /\ LanguageStar language tail /\ output = word ++ tail.

Definition NonemptyWords {d} (set : NVec d -> Prop) : Language d :=
  fun word => word <> [] /\ List.Forall set word.

Definition ReachLanguage {d} (system : IBVAS d) (language : Language d)
    (target : NVec d) : Prop :=
  exists run,
    ValidFreeIRun system run /\ irun_target run = target /\
    language (free_irun_sources run).

Section LeafSubstitution.
Context {d : nat} (system : IBVAS d).

Definition ReplacementFor (value : NVec d) (run : IRun d) : Prop :=
  ValidFreeIRun system run /\ irun_target run = value.

Inductive SubstituteLeavesRun : IRun d -> list (IRun d) -> IRun d -> Prop :=
| substitute_leaf : forall value replacement,
    ReplacementFor value replacement ->
    SubstituteLeavesRun (irun_leaf value) [replacement] replacement
| substitute_node : forall action children target replacements
      substituted_children,
    SubstituteLeavesRuns children replacements substituted_children ->
    SubstituteLeavesRun (irun_node action children target) replacements
      (irun_node action substituted_children target)
with SubstituteLeavesRuns : IRuns d -> list (IRun d) -> IRuns d -> Prop :=
| substitute_nil : SubstituteLeavesRuns iruns_nil [] iruns_nil
| substitute_cons : forall run runs run_replacements runs_replacements
      substituted_run substituted_runs,
    SubstituteLeavesRun run run_replacements substituted_run ->
    SubstituteLeavesRuns runs runs_replacements substituted_runs ->
    SubstituteLeavesRuns (iruns_cons run runs)
      (run_replacements ++ runs_replacements)
      (iruns_cons substituted_run substituted_runs).

Scheme SubstituteLeavesRun_ind' := Induction for SubstituteLeavesRun Sort Prop
with SubstituteLeavesRuns_ind' := Induction for SubstituteLeavesRuns Sort Prop.
Combined Scheme SubstituteLeaves_mutind
  from SubstituteLeavesRun_ind', SubstituteLeavesRuns_ind'.

Lemma substitute_leaves_target_sources :
  (forall run replacements substituted,
    SubstituteLeavesRun run replacements substituted ->
    irun_target substituted = irun_target run /\
    free_irun_sources substituted =
      List.concat (List.map free_irun_sources replacements)) /\
  (forall runs replacements substituted,
    SubstituteLeavesRuns runs replacements substituted ->
    iruns_targets substituted = iruns_targets runs /\
    free_iruns_sources substituted =
      List.concat (List.map free_irun_sources replacements)).
Proof.
  refine (SubstituteLeaves_mutind
    (fun run replacements substituted _ =>
      irun_target substituted = irun_target run /\
      free_irun_sources substituted =
        List.concat (List.map free_irun_sources replacements))
    (fun runs replacements substituted _ =>
      iruns_targets substituted = iruns_targets runs /\
      free_iruns_sources substituted =
        List.concat (List.map free_irun_sources replacements))
    _ _ _ _).
  - intros value replacement [Hvalid Htarget].
    cbn. split; [exact Htarget|symmetry; apply app_nil_r].
  - intros action children target replacements substituted_children
      Hsubstituted IH. destruct IH as [Htargets Hsources]. cbn. auto.
  - cbn. auto.
  - intros run runs run_replacements runs_replacements substituted_run
      substituted_runs Hrun IHrun Hruns IHruns.
    destruct IHrun as [Htarget Hsource].
    destruct IHruns as [Htargets Hsources].
    cbn. rewrite Htarget, Htargets, Hsource, Hsources, List.map_app,
      List.concat_app. auto.
Qed.

Combined Scheme ValidFreeRunRunsFlattening_mutind
  from ValidFreeIRun_ind', ValidFreeIRuns_ind'.

Lemma substitute_leaves_valid :
  (forall run, ValidFreeIRun system run -> forall replacements substituted,
    SubstituteLeavesRun run replacements substituted ->
    ValidFreeIRun system substituted) /\
  (forall runs, ValidFreeIRuns system runs -> forall replacements substituted,
    SubstituteLeavesRuns runs replacements substituted ->
    ValidFreeIRuns system substituted).
Proof.
  apply ValidFreeRunRunsFlattening_mutind.
  - intros value replacements substituted Hsubstitute.
    inversion Hsubstitute as [value' replacement Hreplacement|]; subst.
    exact (proj1 Hreplacement).
  - intros action children target Haction Hchildren IHchildren Happly
      replacements substituted Hsubstitute.
    inversion Hsubstitute as
      [|action' children' target' replacements' substituted_children Hsubs];
      subst. constructor; [exact Haction|eauto|].
    destruct (proj2 substitute_leaves_target_sources _ _ _ Hsubs)
      as [Htargets _]. now rewrite Htargets.
  - intros replacements substituted Hsubstitute.
    inversion Hsubstitute; subst. constructor.
  - intros run runs Hrun IHrun Hruns IHruns replacements substituted
      Hsubstitute.
    inversion Hsubstitute; subst. constructor; eauto.
Qed.

Lemma substitute_leaves_exists :
  (forall run, ValidFreeIRun system run -> forall replacements,
    List.Forall2 (ReplacementFor) (free_irun_sources run) replacements ->
    exists substituted, SubstituteLeavesRun run replacements substituted) /\
  (forall runs, ValidFreeIRuns system runs -> forall replacements,
    List.Forall2 (ReplacementFor) (free_iruns_sources runs) replacements ->
    exists substituted, SubstituteLeavesRuns runs replacements substituted).
Proof.
  apply ValidFreeRunRunsFlattening_mutind.
  - intros value replacements Hreplacements.
    inversion Hreplacements as
      [|source replacement sources replacements' Hreplacement Htail]; subst.
    inversion Htail; subst. exists replacement. constructor. exact Hreplacement.
  - intros action children target Haction Hchildren IHchildren Happly
      replacements Hreplacements.
    destruct (IHchildren replacements Hreplacements) as [children' Hchildren'].
    exists (irun_node action children' target). constructor. exact Hchildren'.
  - intros replacements Hreplacements. inversion Hreplacements; subst.
    exists iruns_nil. constructor.
  - intros run runs Hrun IHrun Hruns IHruns replacements Hreplacements.
    cbn in Hreplacements. apply List.Forall2_app_inv_l in Hreplacements.
    destruct Hreplacements as [run_replacements [runs_replacements
      [Heq [Hrun_replacements Hruns_replacements]]]]. subst replacements.
    destruct (IHrun _ Heq) as [run' Hrun'].
    destruct (IHruns _ Hrun_replacements) as [runs' Hruns'].
    exists (iruns_cons run' runs'). now constructor.
Qed.

Theorem substitute_all_leaves : forall run replacements,
  ValidFreeIRun system run ->
  List.Forall2 (ReplacementFor) (free_irun_sources run) replacements ->
  exists substituted,
    ValidFreeIRun system substituted /\
    SubstituteLeavesRun run replacements substituted /\
    irun_target substituted = irun_target run /\
    free_irun_sources substituted =
      List.concat (List.map free_irun_sources replacements).
Proof.
  intros run replacements Hvalid Hreplacements.
  destruct (proj1 substitute_leaves_exists run Hvalid replacements Hreplacements)
    as [substituted Hsubstituted].
  exists substituted. repeat split.
  - eapply (proj1 substitute_leaves_valid); eauto.
  - exact Hsubstituted.
  - exact (proj1 (proj1 substitute_leaves_target_sources _ _ _ Hsubstituted)).
  - exact (proj2 (proj1 substitute_leaves_target_sources _ _ _ Hsubstituted)).
Qed.

End LeafSubstitution.

Lemma word_shuffle_right_prefix : forall A (prefix left right output : list A),
  WordShuffle left right output ->
  WordShuffle left (prefix ++ right) (prefix ++ output).
Proof.
  intros A prefix; induction prefix as [|value prefix IH];
    intros left right output Hshuffle; cbn; [exact Hshuffle|].
  constructor. now apply IH.
Qed.

Lemma language_star_append : forall d (language : Language d) left right,
  LanguageStar language left -> LanguageStar language right ->
  LanguageStar language (left ++ right).
Proof.
  intros d language left right Hleft Hright. induction Hleft.
  - cbn. exact Hright.
  - rewrite <- app_assoc. constructor; assumption.
Qed.

Lemma language_plus_cons : forall d (language : Language d) word tail,
  language word -> LanguageStar language tail ->
  LanguagePlus language (word ++ tail).
Proof. intros; exists word, tail; auto. Qed.

Section Fact36.
Context {d : nat} (system : IBVAS d).
Variables K L : Language d.

Definition ReachL (value : NVec d) : Prop := ReachLanguage system L value.

Lemma reachable_word_replacements : forall left right output,
  WordShuffle left right output ->
  List.Forall ReachL right ->
  exists replacements expanded_right,
    List.Forall2 (ReplacementFor system) output replacements /\
    LanguageStar L expanded_right /\
    (right <> [] -> LanguagePlus L expanded_right) /\
    WordShuffle left expanded_right
      (List.concat (List.map free_irun_sources replacements)).
Proof.
  intros left right output Hshuffle. induction Hshuffle; intro Hreachable.
  - exists [], []. repeat split; try constructor. intros H; contradiction.
  - destruct (IHHshuffle Hreachable) as
      [replacements [expanded
        [Hreplacements [Hstar [Hplus Hinterleave]]]]].
    exists (irun_leaf value :: replacements), expanded. repeat split.
    + constructor; [split; [constructor|reflexivity]|exact Hreplacements].
    + exact Hstar.
    + exact Hplus.
    + cbn. now constructor.
  - inversion Hreachable as [|? ? Hhead Htail]; subst.
    destruct Hhead as [inner [Hinner_valid [Hinner_target HL]]].
    destruct (IHHshuffle Htail) as
      [replacements [expanded
        [Hreplacements [Hstar [Hplus Hinterleave]]]]].
    exists (inner :: replacements), (free_irun_sources inner ++ expanded).
    repeat split.
    + constructor; [split; assumption|exact Hreplacements].
    + constructor; assumption.
    + intros _. exists (free_irun_sources inner), expanded.
      repeat split; auto.
    + cbn. now apply word_shuffle_right_prefix.
Qed.

Theorem fact_3_6_reach_shuffle_flatten :
  NonemptyLanguage K -> NonemptyLanguage L -> forall target,
  ReachLanguage system
    (LanguageShuffle K (NonemptyWords ReachL)) target ->
  ReachLanguage system
    (LanguageShuffle K (LanguagePlus L)) target.
Proof.
  intros HK HL target
    [outer [Houter_valid [Htarget
      [left [right [HKleft [[Hright_nonempty Hright_reach] Hshuffle]]]]]]].
  destruct (reachable_word_replacements left right
    (free_irun_sources outer) Hshuffle Hright_reach) as
    [replacements [expanded
      [Hreplacements [Hstar [Hplus Hexpanded_shuffle]]]]].
  destruct (substitute_all_leaves system outer replacements Houter_valid
    Hreplacements) as
    [flattened [Hflattened_valid [Hsubstituted
      [Hflattened_target Hflattened_sources]]]].
  exists flattened. split; [exact Hflattened_valid|].
  split; [now rewrite Hflattened_target|].
  exists left, expanded. split; [exact HKleft|]. split.
  - now apply Hplus.
  - now rewrite Hflattened_sources.
Qed.

End Fact36.

Section ReachSideFlattening.
Context {d : nat} (system : IBVAS d).

Definition InitialValue (value : NVec d) : Prop :=
  List.In value (initial_vectors system).

Lemma reach_to_initialized_free_run :
  (forall value, Reach system value ->
    exists run,
      ValidFreeIRun system run /\ irun_target run = value /\
      List.Forall InitialValue (free_irun_sources run)) /\
  (forall values, ReachChildren system values ->
    exists runs,
      ValidFreeIRuns system runs /\ iruns_targets runs = values /\
      List.Forall InitialValue (free_iruns_sources runs)).
Proof.
  apply Reach_mutind.
  - intros index value Hindex. exists (irun_leaf value).
    split; [apply valid_free_leaf|]. split; [reflexivity|].
    constructor; [exact (nth_error_In _ _ Hindex)|constructor].
  - intros index action children value Hindex _
      [runs [Hvalid [Htargets Hsources]]] Happly.
    exists (irun_node action runs value). split.
    + constructor; [exact (nth_error_In _ _ Hindex)|exact Hvalid|].
      now rewrite Htargets.
    + split; [reflexivity|exact Hsources].
  - exists iruns_nil. split; [apply valid_free_nil|].
    split; [reflexivity|constructor].
  - intros value values _
      [run [Hrun [Htarget Hsources]]]
      _ [runs [Hruns [Htargets Hsources_tail]]].
    exists (iruns_cons run runs). split.
    + now constructor.
    + split.
      * cbn. now rewrite Htarget, Htargets.
      * cbn. apply List.Forall_app. now split.
Qed.

Lemma reachable_replacement_runs : forall values,
  List.Forall (Reach system) values ->
  exists replacements,
    List.Forall2 (ReplacementFor system) values replacements /\
    List.Forall InitialValue
      (List.concat (List.map free_irun_sources replacements)).
Proof.
  intros values Hvalues. induction Hvalues as
      [|value values Hvalue Hvalues [replacements [Hreplacements Hsources]]].
  - exists []. split; constructor.
  - destruct (proj1 reach_to_initialized_free_run value Hvalue) as
      [run [Hvalid [Htarget Hrun_sources]]].
    exists (run :: replacements). split.
    + constructor; [now split|exact Hreplacements].
    + cbn. apply List.Forall_app. now split.
Qed.

Lemma leaf_replacement_runs : forall (A : NVec d -> Prop) values,
  List.Forall A values ->
  List.Forall2 (ReplacementFor system) values
    (List.map (@irun_leaf d) values).
Proof.
  intros A values Hvalues. induction Hvalues; cbn; constructor; auto.
  split; [constructor|reflexivity].
Qed.

Lemma forall2_permutation_transport_left : forall
    (left right : list (NVec d)) replacements,
  Permutation left right ->
  List.Forall2 (ReplacementFor system) right replacements ->
  exists transported,
    Permutation transported replacements /\
    List.Forall2 (ReplacementFor system) left transported.
Proof.
  intros left right replacements Hperm.
  revert replacements. induction Hperm; intros replacements Hreplacements.
  - inversion Hreplacements. exists []. split; constructor.
  - inversion Hreplacements as
        [|source replacement sources replacements_tail Hhead Htail]; subst.
    destruct (IHHperm _ Htail) as [transported [Htransported Hall]].
    exists (replacement :: transported). split;
      [now constructor|now constructor].
  - inversion Hreplacements as
        [|source_y replacement_y sources_y replacements_y Hhead_y Htail_y];
      subst.
    inversion Htail_y as
        [|source_x replacement_x sources_x replacements_x Hhead_x Htail];
      subst.
    exists (replacement_x :: replacement_y :: replacements_x). split.
    + constructor.
    + constructor; [exact Hhead_x|]. constructor; assumption.
  - destruct (IHHperm2 _ Hreplacements) as [middle [Hmiddle Hmiddle_all]].
    destruct (IHHperm1 _ Hmiddle_all) as [transported [Ht Hall]].
    exists transported. split; [eapply Permutation_trans; eauto|exact Hall].
Qed.

Lemma concat_map_sources_permutation : forall left right : list (IRun d),
  Permutation left right ->
  Permutation
    (List.concat (List.map free_irun_sources left))
    (List.concat (List.map free_irun_sources right)).
Proof.
  intros left right Hperm. induction Hperm; cbn.
  - constructor.
  - now apply Permutation_app.
  - apply Permutation_app_swap_app.
  - eapply Permutation_trans; eauto.
Qed.

Theorem flatten_reachable_side_sources : forall (A : NVec d -> Prop) run,
  ValidFreeIRun system run ->
  SourceMultiShuffle A (Reach system) (free_irun_sources run) ->
  exists flattened,
    ValidFreeIRun system flattened /\
    irun_target flattened = irun_target run /\
    SourceMultiShuffle A InitialValue (free_irun_sources flattened).
Proof.
  intros A run Hvalid
    [specials [sides [Hspecials_nonempty
      [Hspecials [Hsides Hsource_permutation]]]]].
  pose proof (leaf_replacement_runs A specials Hspecials) as Hleft.
  destruct (reachable_replacement_runs sides Hsides) as
    [right_replacements [Hright Hright_sources]].
  set (left_replacements := List.map (@irun_leaf d) specials).
  assert (Hcombined : List.Forall2 (ReplacementFor system)
      (specials ++ sides) (left_replacements ++ right_replacements)).
  { apply List.Forall2_app; assumption. }
  destruct (forall2_permutation_transport_left _ _ _ Hsource_permutation
    Hcombined) as [replacements [Hreplacement_perm Hreplacements]].
  destruct (substitute_all_leaves system run replacements Hvalid Hreplacements)
    as [flattened [Hflattened [Hsubstitute [Htarget Hsources]]]].
  exists flattened. split; [exact Hflattened|]. split; [exact Htarget|].
  exists specials,
    (List.concat (List.map free_irun_sources right_replacements)).
  repeat split; try assumption.
  - rewrite Hsources.
    eapply Permutation_trans.
    + apply concat_map_sources_permutation. exact Hreplacement_perm.
    + unfold left_replacements. rewrite List.map_app, List.concat_app.
      apply Permutation_app; [|reflexivity].
      assert (Hleaf_sources : forall values : list (NVec d),
        List.concat
          (List.map free_irun_sources (List.map (@irun_leaf d) values)) =
        values).
      { intro values. induction values as [|value tail IH];
          cbn [free_irun_sources]; [reflexivity|].
        change (value ::
          List.concat
            (List.map free_irun_sources (List.map (@irun_leaf d) tail)) =
          value :: tail).
        f_equal. exact IH. }
      now rewrite Hleaf_sources.
Qed.

End ReachSideFlattening.
