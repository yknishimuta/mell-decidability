From Coq Require Import List Vector ZArith Lia Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder Amalgamation.
From Mell.BVASS Require Import Stateful ContextInsertion.

(** Paper node counts.  In contrast to [srun_size], the constructors used
    to encode a list of children are not execution-tree nodes. *)
Fixpoint run_node_count {d q} (run : SRun d q) : nat :=
  match run with
  | srun_leaf _ => 1
  | srun_node _ children _ => S (runs_node_count children)
  end
with runs_node_count {d q} (runs : SRuns d q) : nat :=
  match runs with
  | sruns_nil => 0
  | sruns_cons run tail => run_node_count run + runs_node_count tail
  end.

Fixpoint context_node_count {d q} (context : SContext d q) : nat :=
  match context with
  | scontext_hole => 0
  | scontext_node _ before inner after _ =>
      S (runs_node_count before + context_node_count inner +
         runs_node_count after)
  end.

Lemma runs_node_count_append : forall d q (left right : SRuns d q),
    runs_node_count (sruns_append left right) =
    runs_node_count left + runs_node_count right.
Proof.
  intros d q left; induction left; intros right; cbn; [lia|].
  rewrite IHleft. lia.
Qed.

Lemma sruns_isomorphic_insert_removed : forall d q
    (selected target : SRun d q) source remainder targets,
    SRunsRemove selected source remainder ->
    SRunIsomorphic selected target ->
    SRunsIsomorphic remainder targets ->
    SRunsIsomorphic source (sruns_cons target targets).
Proof.
  intros d q selected target source remainder targets Hremove.
  revert target targets. induction Hremove; intros target targets Hselected Hremainder.
  - eapply sruns_iso_cons with (right := target) (remainder := targets).
    + constructor.
    + exact Hselected.
    + exact Hremainder.
  - inversion Hremainder as
      [| left lefts right rights right_tail Hremove_right Hhead Htail]; subst.
    pose proof (IHHremove target right_tail Hselected Htail) as Hinsert_tail.
    eapply sruns_iso_cons with
      (right := right) (remainder := sruns_cons target right_tail).
    + constructor 2. exact Hremove_right.
    + exact Hhead.
    + exact Hinsert_tail.
Qed.

Lemma srun_isomorphic_sym_bounded : forall d q bound,
  (forall first : SRun d q, srun_size first < bound ->
    forall second, SRunIsomorphic first second ->
      SRunIsomorphic second first) /\
  (forall first : SRuns d q, sruns_size first < bound ->
    forall second, SRunsIsomorphic first second ->
      SRunsIsomorphic second first).
Proof.
  intros d q bound. induction bound as [|bound IH].
  - split; intros; lia.
  - destruct IH as [IHrun IHruns]. split.
    + intros first Hsize second Hiso. inversion Hiso; subst.
      * constructor.
      * constructor. eapply IHruns; [cbn in Hsize; lia|eassumption].
    + intros first Hsize second Hiso. inversion Hiso; subst.
      * constructor.
      * eapply sruns_isomorphic_insert_removed; eauto.
        -- eapply IHrun; [cbn in Hsize; lia|eassumption].
        -- eapply IHruns; [cbn in Hsize; lia|eassumption].
Qed.

Theorem srun_isomorphic_sym_stateful : forall d q
    (left right : SRun d q),
    SRunIsomorphic left right -> SRunIsomorphic right left.
Proof.
  intros d q left right Hiso.
  eapply (proj1 (srun_isomorphic_sym_bounded d q (S (srun_size left))));
    eauto; lia.
Qed.

Lemma context_plug_node_count : forall d q (context : SContext d q) run,
    run_node_count (scontext_plug context run) =
    context_node_count context + run_node_count run.
Proof.
  intros d q context; induction context; intro run; cbn; [lia|].
  repeat rewrite runs_node_count_append. cbn. rewrite IHcontext. lia.
Qed.

Lemma context_compose_node_count : forall d q
    (outer inner : SContext d q),
    context_node_count (scontext_compose outer inner) =
    context_node_count outer + context_node_count inner.
Proof.
  intros d q outer; induction outer; intro inner; cbn; [lia|].
  rewrite IHouter. lia.
Qed.

Lemma identity_context_node_count : forall d q,
    @context_node_count d q scontext_hole = 0.
Proof. reflexivity. Qed.

Lemma sruns_remove_node_count : forall d q (run : SRun d q) source remainder,
    SRunsRemove run source remainder ->
    runs_node_count source = run_node_count run + runs_node_count remainder.
Proof.
  intros d q run source remainder H; induction H; cbn; lia.
Qed.

Lemma srun_isomorphic_node_count_mut : forall d q,
  (forall left right : SRun d q,
      SRunIsomorphic left right -> run_node_count left = run_node_count right) /\
  (forall left right : SRuns d q,
      SRunsIsomorphic left right -> runs_node_count left = runs_node_count right).
Proof.
  intros d q. apply SRunIsomorphic_mutind.
  - reflexivity.
  - intros. cbn. congruence.
  - reflexivity.
  - intros left lefts right rights remainder Hremove Hiso Hhead
      Htails Htail.
    cbn. pose proof (sruns_remove_node_count d q right rights remainder Hremove)
      as Hcount. lia.
Qed.

Theorem srun_isomorphic_node_count : forall d q
    (left right : SRun d q),
    SRunIsomorphic left right -> run_node_count left = run_node_count right.
Proof. intros; eapply (proj1 (srun_isomorphic_node_count_mut d q)); eauto. Qed.

Theorem sruns_isomorphic_node_count : forall d q
    (left right : SRuns d q),
    SRunsIsomorphic left right -> runs_node_count left = runs_node_count right.
Proof. intros; eapply (proj2 (srun_isomorphic_node_count_mut d q)); eauto. Qed.

Fixpoint family_added_node_count {d q} {run : SRun d q}
    (family : SContextFamily run) : nat :=
  match family with
  | family_leaf context => context_node_count context
  | family_node context children _ =>
      context_node_count context + families_added_node_count children
  end
with families_added_node_count {d q} {runs : SRuns d q}
    (families : SContextFamilies runs) : nat :=
  match families with
  | families_nil => 0
  | families_cons family tail =>
      family_added_node_count family + families_added_node_count tail
  end.

Lemma insert_family_node_count_mut : forall d q,
  (forall (run : SRun d q) (family : SContextFamily run),
    run_node_count (insert_context_family family) =
      run_node_count run + family_added_node_count family) /\
  (forall (runs : SRuns d q) (families : SContextFamilies runs),
    runs_node_count (insert_context_families families) =
      runs_node_count runs + families_added_node_count families).
Proof.
  intros d q. apply SContextFamily_SContextFamilies_ind; cbn.
  - intros. rewrite context_plug_node_count. cbn. apply Nat.add_comm.
  - intros rule children result context families IH matched.
    rewrite context_plug_node_count. cbn. rewrite IH. lia.
  - reflexivity.
  - intros run runs family IHfamily families IHfamilies.
    cbn. rewrite IHfamily, IHfamilies. lia.
Qed.

Theorem insert_context_family_node_count : forall d q
    (run : SRun d q) (family : SContextFamily run),
    run_node_count (insert_context_family family) =
      run_node_count run + family_added_node_count family.
Proof. intros; apply (proj1 (insert_family_node_count_mut d q)). Qed.

Lemma srun_isomorphic_root_counter : forall d q
    (left right : SRun d q),
    SRunIsomorphic left right ->
    snd (root_config left) = snd (root_config right).
Proof.
  intros d q left right Hiso.
  now rewrite (srun_isomorphic_root d q left right Hiso).
Qed.

Lemma valid_sruns_insert_removed : forall d q (B : SBVAS d q)
    (run : SRun d q) source remainder,
    SRunsRemove run source remainder ->
    ValidSRun B run -> ValidSRuns B remainder -> ValidSRuns B source.
Proof.
  intros d q B run source remainder Hremove.
  induction Hremove; intros Hrun Hremaining.
  - constructor; assumption.
  - inversion Hremaining; subst. constructor; [assumption|].
    eapply IHHremove; eauto.
Qed.

Lemma sruns_remove_configs_permutation : forall d q (run : SRun d q)
    source remainder,
    SRunsRemove run source remainder ->
    Permutation (root_config run :: sruns_configs remainder)
      (sruns_configs source).
Proof.
  intros d q run source remainder H; induction H; cbn.
  - apply Permutation_refl.
  - eapply Permutation_trans.
    + apply perm_swap.
    + constructor. assumption.
Qed.

Lemma sruns_isomorphic_configs_permutation : forall d q
    (left right : SRuns d q),
    SRunsIsomorphic left right ->
    Permutation (sruns_configs left) (sruns_configs right).
Proof.
  intros d q left right H; induction H; cbn.
  - constructor.
  - eapply Permutation_trans.
    + rewrite (srun_isomorphic_root d q left right H0).
      constructor. exact IHSRunsIsomorphic.
    + exact (sruns_remove_configs_permutation d q right rights remainder H).
Qed.

Lemma srun_isomorphic_valid_mut : forall d q (B : SBVAS d q),
  (forall left right : SRun d q,
    SRunIsomorphic left right -> ValidSRun B left -> ValidSRun B right) /\
  (forall left right : SRuns d q,
    SRunsIsomorphic left right -> ValidSRuns B left -> ValidSRuns B right).
Proof.
  intros d q B. apply SRunIsomorphic_mutind.
  - intros config Hvalid. exact Hvalid.
  - intros rule left right result Hiso IH Hvalid.
    inversion Hvalid; subst.
    pose proof (sruns_isomorphic_configs_permutation d q left right Hiso)
      as Hconfigs.
    econstructor.
    + exact H2.
    + apply IH. exact H3.
    + eapply Permutation_trans with
        (l' := List.map fst (sruns_configs left)).
      * apply Permutation_map. now apply Permutation_sym.
      * exact H4.
    + rewrite <- H5. apply add_displacement_permutation.
      apply Permutation_map. now apply Permutation_sym.
    + exact H6.
  - intros Hvalid. exact Hvalid.
  - intros left lefts right rights remainder Hremove Hhead IHhead Htail IHtail
      Hvalid.
    inversion Hvalid; subst.
    eapply valid_sruns_insert_removed; eauto.
Qed.

Theorem srun_isomorphic_valid : forall d q (B : SBVAS d q) left right,
    SRunIsomorphic left right -> ValidSRun B left -> ValidSRun B right.
Proof. intros; eapply (proj1 (srun_isomorphic_valid_mut d q B)); eauto. Qed.

(** A path contains the occurrence, not merely the value of a subrun.  The
    [before]/[after] frame therefore distinguishes duplicate equal children. *)
Inductive SRunPath {d q} : forall whole focus : SRun d q, Type :=
| srun_path_here : forall run, SRunPath run run
| srun_path_child : forall rule before child after result focus,
    SRunPath child focus ->
    SRunPath
      (srun_node rule (sruns_append before (sruns_cons child after)) result)
      focus.

Fixpoint replace_subrun_at {d q} {whole focus : SRun d q}
    (path : SRunPath whole focus) (replacement : SRun d q)
    (delta : NVec d) : SRun d q :=
  match path with
  | srun_path_here _ => replacement
  | srun_path_child rule before child after result focus tail =>
      srun_node rule
        (sruns_append before
          (sruns_cons (replace_subrun_at tail replacement delta) after))
        (fst result, nvec_add (snd result) delta)
  end.

Lemma valid_sruns_frame_replace_stateful : forall d q (B : SBVAS d q)
    before after old replacement,
    ValidSRuns B (sruns_append before (sruns_cons old after)) ->
    ValidSRun B replacement ->
    ValidSRuns B (sruns_append before (sruns_cons replacement after)).
Proof.
  intros d q B before; induction before; intros after old replacement Hold Hnew;
    cbn in *.
  - inversion Hold; subst. constructor; assumption.
  - inversion Hold; subst. constructor; [assumption|].
    eapply IHbefore; eauto.
Qed.

Lemma valid_sruns_frame_member_stateful : forall d q (B : SBVAS d q)
    before after run,
    ValidSRuns B (sruns_append before (sruns_cons run after)) ->
    ValidSRun B run.
Proof.
  intros d q B before; induction before; intros after run Hvalid; cbn in Hvalid.
  - inversion Hvalid; assumption.
  - inversion Hvalid; subst. eapply IHbefore; eauto.
Qed.

Lemma sruns_configs_append : forall d q (left right : SRuns d q),
    sruns_configs (sruns_append left right) =
    sruns_configs left ++ sruns_configs right.
Proof.
  intros d q left; induction left; intro right; cbn; [reflexivity|].
  now rewrite IHleft.
Qed.

Lemma add_displacement_frame_shift : forall d (offset : ZVec d)
    before after left right target delta,
    right = nvec_add left delta ->
    add_displacement offset (before ++ left :: after) = Some target ->
    add_displacement offset (before ++ right :: after) =
      Some (nvec_add target delta).
Proof.
  intros d offset before after left right target delta Hright Happly.
  unfold add_displacement in Happly |- *.
  assert (Hold :
    zvec_add offset (nvec_to_zvec (nvec_sum (before ++ left :: after))) =
      nvec_to_zvec target).
  { apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros index index' Heq; subst index'. unfold nvec_to_zvec.
    rewrite (nth_map Z.of_nat target index index eq_refl).
    eapply zvec_to_nvec_sound; eauto. }
  rewrite (nvec_sum_frame_shift d before after left right delta Hright),
    nvec_to_zvec_add, zvec_add_assoc, Hold, <- nvec_to_zvec_add.
  apply zvec_to_nvec_of_nvec.
Qed.

Lemma replace_subrun_at_root : forall d q
    (whole focus replacement : SRun d q)
    (path : SRunPath whole focus) delta,
    fst (root_config replacement) = fst (root_config focus) ->
    snd (root_config replacement) =
      nvec_add (snd (root_config focus)) delta ->
    fst (root_config (replace_subrun_at path replacement delta)) =
      fst (root_config whole) /\
    snd (root_config (replace_subrun_at path replacement delta)) =
      nvec_add (snd (root_config whole)) delta.
Proof.
  intros d q whole focus replacement path.
  induction path; intros delta Hstate Hcounter; cbn.
  - auto.
  - split; reflexivity.
Qed.

Lemma replace_subrun_at_node_count : forall d q
    (whole focus replacement : SRun d q)
    (path : SRunPath whole focus) delta,
    run_node_count (replace_subrun_at path replacement delta) +
      run_node_count focus =
    run_node_count whole + run_node_count replacement.
Proof.
  intros d q whole focus replacement path.
  induction path; intro delta; cbn.
  - lia.
  - repeat rewrite runs_node_count_append. cbn.
    specialize (IHpath delta). lia.
Qed.

Theorem replace_subrun_at_valid : forall d q (B : SBVAS d q)
    (whole focus replacement : SRun d q)
    (path : SRunPath whole focus) delta,
    ValidSRun B whole -> ValidSRun B replacement ->
    fst (root_config replacement) = fst (root_config focus) ->
    snd (root_config replacement) =
      nvec_add (snd (root_config focus)) delta ->
    ValidSRun B (replace_subrun_at path replacement delta).
Proof.
  intros d q B whole focus replacement path.
  induction path; intros delta Hwhole Hreplacement Hstate Hcounter.
  - exact Hreplacement.
  - inversion Hwhole; subst.
    assert (Hchild : ValidSRun B child).
    { eapply valid_sruns_frame_member_stateful; eauto. }
    assert (Hnew : ValidSRun B (replace_subrun_at path replacement delta)).
    { eapply IHpath; eauto. }
    destruct (replace_subrun_at_root d q child focus replacement path delta
      Hstate Hcounter) as [Hnewstate Hnewcounter].
    econstructor.
    + exact H2.
    + eapply valid_sruns_frame_replace_stateful; eauto.
    + repeat rewrite sruns_configs_append in H4 |- *.
      repeat rewrite List.map_app in H4 |- *. cbn in H4 |- *.
      change (Permutation
        (List.map fst (sruns_configs before) ++
          fst (root_config (replace_subrun_at path replacement delta)) ::
          List.map fst (sruns_configs after)) (input_states rule)).
      change (Permutation
        (List.map fst (sruns_configs before) ++
          fst (root_config child) :: List.map fst (sruns_configs after))
        (input_states rule)) in H4.
      rewrite Hnewstate. exact H4.
    + repeat rewrite sruns_configs_append in H5 |- *.
      repeat rewrite List.map_app in H5 |- *. cbn in H5 |- *.
      change (add_displacement (rule_delta rule)
        (List.map snd (sruns_configs before) ++
          snd (root_config (replace_subrun_at path replacement delta)) ::
          List.map snd (sruns_configs after)) =
        Some (nvec_add (snd result) delta)).
      change (add_displacement (rule_delta rule)
        (List.map snd (sruns_configs before) ++ snd (root_config child) ::
          List.map snd (sruns_configs after)) = Some (snd result)) in H5.
      eapply add_displacement_frame_shift; eauto.
    + cbn. exact H6.
Qed.

Theorem subrun_replacement_exact : forall d q (B : SBVAS d q)
    (whole focus replacement : SRun d q)
    (path : SRunPath whole focus) delta,
    ValidSRun B whole -> ValidSRun B replacement ->
    fst (root_config replacement) = fst (root_config focus) ->
    snd (root_config replacement) =
      nvec_add (snd (root_config focus)) delta ->
    exists replaced,
      replaced = replace_subrun_at path replacement delta /\
      ValidSRun B replaced /\
      fst (root_config replaced) = fst (root_config whole) /\
      snd (root_config replaced) =
        nvec_add (snd (root_config whole)) delta /\
      run_node_count replaced + run_node_count focus =
        run_node_count whole + run_node_count replacement.
Proof.
  intros d q B whole focus replacement path delta Hwhole Hreplacement
    Hstate Hcounter.
  exists (replace_subrun_at path replacement delta). split; [reflexivity|].
  repeat split.
  - eapply replace_subrun_at_valid; eauto.
  - eapply (proj1 (replace_subrun_at_root d q whole focus replacement path
      delta Hstate Hcounter)).
  - eapply (proj2 (replace_subrun_at_root d q whole focus replacement path
      delta Hstate Hcounter)).
  - apply replace_subrun_at_node_count.
Qed.

(** Raise precisely the strict ancestors of the hole by [delta]. *)
Fixpoint scontext_add {d q} (delta : NVec d) (context : SContext d q) :
    SContext d q :=
  match context with
  | scontext_hole => scontext_hole
  | scontext_node rule before inner after result =>
      scontext_node rule before (scontext_add delta inner) after
        (fst result, nvec_add (snd result) delta)
  end.

Lemma scontext_add_node_count : forall d q (delta : NVec d)
    (context : SContext d q),
    context_node_count (scontext_add delta context) =
      context_node_count context.
Proof.
  intros d q delta context. induction context; cbn; [reflexivity|].
  now rewrite IHcontext.
Qed.

Fixpoint scontext_add_plug_path {d q} (context : SContext d q)
    (run : SRun d q) : SRunPath (scontext_plug context run) run :=
  match context with
  | scontext_hole => srun_path_here run
  | scontext_node rule before inner after result =>
      srun_path_child rule before (scontext_plug inner run) after result run
        (scontext_add_plug_path inner run)
  end.

Lemma scontext_add_plug_eq_replace : forall d q
    (context : SContext d q) (old replacement : SRun d q) delta,
    replace_subrun_at (scontext_add_plug_path context old)
      replacement delta =
    scontext_plug (scontext_add delta context) replacement.
Proof.
  intros d q context. induction context; intros old replacement delta; cbn.
  - reflexivity.
  - now rewrite IHcontext.
Qed.

Fixpoint append_context_families {d q} {left right : SRuns d q}
    (first : SContextFamilies left) (second : SContextFamilies right) :
    SContextFamilies (sruns_append left right) :=
  match first in SContextFamilies indexed return
      SContextFamilies (sruns_append indexed right) with
  | families_nil => second
  | families_cons family tail =>
      families_cons family (append_context_families tail second)
  end.

Fixpoint lift_family_through_context {d q} (context : SContext d q)
    {run : SRun d q} (family : SContextFamily run) (delta : NVec d) :
    SContextFamily (scontext_plug context run) :=
  match context with
  | scontext_hole => family
  | scontext_node rule before inner after result =>
      family_node scontext_hole
        (append_context_families (identity_context_families before)
          (families_cons (lift_family_through_context inner family delta)
            (identity_context_families after)))
        (fst result, nvec_add (snd result) delta)
  end.

Lemma insert_append_context_families : forall d q
    (left right : SRuns d q) (first : SContextFamilies left)
    (second : SContextFamilies right),
    insert_context_families (append_context_families first second) =
    sruns_append (insert_context_families first)
      (insert_context_families second).
Proof.
  intros d q left right first. induction first; intro second; cbn.
  - reflexivity.
  - now rewrite IHfirst.
Qed.

Lemma lift_family_insert : forall d q (context : SContext d q)
    (run : SRun d q) (family : SContextFamily run) delta,
    insert_context_family (lift_family_through_context context family delta) =
    scontext_plug (scontext_add delta context)
      (insert_context_family family).
Proof.
  intros d q context. induction context; intros run family delta; cbn.
  - reflexivity.
  - rewrite insert_append_context_families.
    rewrite (proj2 (insert_identity_context_family_mut d q) s0). cbn.
    rewrite (proj2 (insert_identity_context_family_mut d q) s1).
    now rewrite IHcontext.
Qed.

Lemma append_context_families_compatible : forall d q
    (left right : SRuns d q) (first : SContextFamilies left)
    (second : SContextFamilies right),
    CompatibleContextFamilies left first ->
    CompatibleContextFamilies right second ->
    CompatibleContextFamilies (sruns_append left right)
      (append_context_families first second).
Proof.
  intros d q left right first. induction first; intros second Hfirst Hsecond.
  - exact Hsecond.
  - cbn. constructor.
    + exact (compatible_families_head d q run runs
        (families_cons s first) Hfirst).
    + apply IHfirst.
      * exact (compatible_families_tail d q run runs
          (families_cons s first) Hfirst).
      * exact Hsecond.
Qed.

Lemma append_context_families_positive : forall d q
    (left right : SRuns d q) (first : SContextFamilies left)
    (second : SContextFamilies right),
    HereditarilyPositiveFamilies left first ->
    HereditarilyPositiveFamilies right second ->
    HereditarilyPositiveFamilies (sruns_append left right)
      (append_context_families first second).
Proof.
  intros d q left right first. induction first; intros second Hfirst Hsecond.
  - exact Hsecond.
  - cbn. constructor.
    + exact (positive_families_head d q run runs
        (families_cons s first) Hfirst).
    + apply IHfirst.
      * exact (positive_families_tail d q run runs
          (families_cons s first) Hfirst).
      * exact Hsecond.
Qed.

Lemma nvec_le_add_right : forall d (value delta : NVec d),
    nvec_le value (nvec_add value delta).
Proof.
  intros d value delta index. unfold nvec_add.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl). lia.
Qed.

Lemma lift_family_compatible : forall d q (context : SContext d q)
    (run : SRun d q) (family : SContextFamily run) delta,
    CompatibleContextFamily run family ->
    CompatibleContextFamily (scontext_plug context run)
      (lift_family_through_context context family delta).
Proof.
  intros d q context. induction context; intros run family delta Hfamily; cbn.
  - exact Hfamily.
  - constructor.
    + eapply append_context_families_compatible.
      * apply (proj2 (identity_context_family_compatible_mut d q)).
      * constructor.
        -- apply IHcontext. exact Hfamily.
        -- apply (proj2 (identity_context_family_compatible_mut d q)).
    + reflexivity.
    + reflexivity.
Qed.

Lemma lift_family_positive : forall d q (context : SContext d q)
    (run : SRun d q) (family : SContextFamily run) delta,
    HereditarilyPositive run family ->
    HereditarilyPositive (scontext_plug context run)
      (lift_family_through_context context family delta).
Proof.
  intros d q context. induction context; intros run family delta Hfamily; cbn.
  - exact Hfamily.
  - constructor.
    + eapply append_context_families_positive.
      * apply (proj2 (identity_context_family_positive_mut d q)).
      * constructor.
        -- apply IHcontext. exact Hfamily.
        -- apply (proj2 (identity_context_family_positive_mut d q)).
    + split; [reflexivity|apply nvec_le_add_right].
Qed.

Theorem context_order_lift_through_context : forall d q (B : SBVAS d q)
    (context : SContext d q) (left right : SRun d q) delta,
    ValidSRun B (scontext_plug context left) ->
    ContextOrder B left right ->
    snd (root_config right) = nvec_add (snd (root_config left)) delta ->
    ContextOrder B (scontext_plug context left)
      (scontext_plug (scontext_add delta context) right).
Proof.
  intros d q B context left right delta Houter
    [Hleft [Hright [family [Hcompatible [Hpositive Hiso]]]]] Hcounter.
  assert (Hstate : fst (root_config right) = fst (root_config left)).
  { symmetry. eapply context_order_root_state. repeat split; eauto. }
  assert (Hnew : ValidSRun B
      (scontext_plug (scontext_add delta context) right)).
  { rewrite <- (scontext_add_plug_eq_replace d q context left right delta).
    eapply replace_subrun_at_valid; eauto. }
  repeat split; try assumption.
  exists (lift_family_through_context context family delta). repeat split.
  - apply lift_family_compatible. exact Hcompatible.
  - apply lift_family_positive. exact Hpositive.
  - rewrite lift_family_insert.
    apply scontext_plug_isomorphic_local. exact Hiso.
Qed.

Lemma compatible_family_proper : forall d q (run : SRun d q)
    (family : SContextFamily run),
    CompatibleContextFamily run family -> CompatibleProper run family.
Proof.
  intros d q run family H. destruct H; constructor; assumption.
Qed.

Lemma positive_family_proper : forall d q (run : SRun d q)
    (family : SContextFamily run),
    HereditarilyPositive run family -> PositiveProper run family.
Proof.
  intros d q run family H. destruct H; constructor; assumption.
Qed.

(** The local "below a context" rule needed by the two-stage
    replacement construction.  Positivity is required only for the total
    root change, never for the local effect of [context]. *)
Theorem context_order_embed_below : forall d q (B : SBVAS d q)
    (small core : SRun d q) (context : SContext d q),
    ContextOrder B small core ->
    ValidSRun B (scontext_plug context core) ->
    fst (root_config small) =
      fst (root_config (scontext_plug context core)) ->
    nvec_le (snd (root_config small))
      (snd (root_config (scontext_plug context core))) ->
    ContextOrder B small (scontext_plug context core).
Proof.
  intros d q B small core context
    [Hsmall [Hcore [family [Hcompatible [Hpositive Hiso]]]]]
    Hplug Hstate Hcounter.
  repeat split; try assumption.
  exists (wrap_family_context context family). repeat split.
  - apply compatible_from_proper.
    + apply wrap_family_compatible_proper.
      now apply compatible_family_proper.
    + unfold family_root_compatible. rewrite insert_wrap_family_context.
      pose proof (scontext_plug_isomorphic_local d q context _ _ Hiso)
        as Hplugiso.
      rewrite (srun_isomorphic_root _ _ _ _ Hplugiso). symmetry. exact Hstate.
  - apply positive_from_proper.
    + apply wrap_family_positive_proper. now apply positive_family_proper.
    + rewrite insert_wrap_family_context.
      pose proof (scontext_plug_isomorphic_local d q context _ _ Hiso)
        as Hplugiso.
      rewrite (srun_isomorphic_root _ _ _ _ Hplugiso).
      split; assumption.
  - rewrite insert_wrap_family_context.
    apply scontext_plug_isomorphic_local. exact Hiso.
Qed.

Inductive PositionalContextOrders {d q} (B : SBVAS d q) :
    SRuns d q -> SRuns d q -> Prop :=
| positional_context_orders_nil :
    PositionalContextOrders B sruns_nil sruns_nil
| positional_context_orders_cons : forall left right lefts rights,
    ContextOrder B left right ->
    PositionalContextOrders B lefts rights ->
    PositionalContextOrders B (sruns_cons left lefts)
      (sruns_cons right rights).

Lemma positional_context_orders_family : forall d q (B : SBVAS d q)
    (left right : SRuns d q),
    PositionalContextOrders B left right ->
    exists families : SContextFamilies left,
      CompatibleContextFamilies left families /\
      HereditarilyPositiveFamilies left families /\
      SRunsIsomorphic (insert_context_families families) right.
Proof.
  intros d q B left right Horders. induction Horders.
  - exists families_nil. repeat split; constructor.
  - destruct H as [_ [_ [family [Hcompatible [Hpositive Hiso]]]]].
    destruct IHHorders as [families [Hfamilies_compatible
      [Hfamilies_positive Hfamilies_iso]]].
    exists (families_cons family families). repeat split; cbn.
    + constructor; assumption.
    + constructor; assumption.
    + apply sruns_iso_cons_same_position; assumption.
Qed.

Theorem context_order_same_root_rule : forall d q (B : SBVAS d q)
    (rule : SRule d q) left_children right_children left_result right_result,
    ValidSRun B (srun_node rule left_children left_result) ->
    ValidSRun B (srun_node rule right_children right_result) ->
    PositionalContextOrders B left_children right_children ->
    RootConfigLe left_result right_result ->
    ContextOrder B (srun_node rule left_children left_result)
      (srun_node rule right_children right_result).
Proof.
  intros d q B rule left_children right_children left_result right_result
    Hleft Hright Hchildren Hroot.
  destruct (positional_context_orders_family d q B _ _ Hchildren) as
    [families [Hcompatible [Hpositive Hiso]]].
  repeat split; try assumption.
  exists (family_node scontext_hole families right_result). repeat split; cbn.
  - constructor.
    + exact Hcompatible.
    + symmetry. exact (proj1 Hroot).
    + reflexivity.
  - constructor; assumption.
  - constructor. exact Hiso.
Qed.

Lemma positive_families_counters_le : forall d q
    (runs : SRuns d q) (families : SContextFamilies runs),
    HereditarilyPositiveFamilies runs families ->
    NVecListLe (List.map snd (sruns_configs runs))
      (List.map snd (sruns_configs (insert_context_families families))).
Proof.
  intros d q runs families Hpositive. induction Hpositive; cbn.
  - constructor.
  - constructor.
    + exact (proj2 (positive_context_family_root_general H)).
    + exact IHHpositive.
Qed.

(** Although a local context may have negative effect, the matched core of
    a node is monotone.  This follows from positivity of every inserted
    child and validity under the unchanged root rule. *)
Lemma family_node_core_root_monotone : forall d q (B : SBVAS d q)
    (rule : SRule d q) children result context
    (families : SContextFamilies children) matched,
    ValidSRun B (srun_node rule children result) ->
    ValidSRun B (insert_context_family
      (@family_node d q rule children result context families matched)) ->
    HereditarilyPositiveFamilies children families ->
    nvec_le (snd result) (snd matched).
Proof.
  intros d q B rule children result context families matched
    Hbase Hinsert Hpositive.
  assert (Hcore : ValidSRun B
      (srun_node rule (insert_context_families families) matched)).
  { cbn in Hinsert. eapply valid_scontext_plug_core; eauto. }
  inversion Hbase; subst. inversion Hcore; subst.
  eapply add_displacement_mono.
  - exact (positive_families_counters_le d q children families Hpositive).
  - exact H5.
  - exact H10.
Qed.

Lemma nvec_add_exchange : forall d (a b c e : NVec d),
    a = nvec_add b c -> e = nvec_add b a ->
    e = nvec_add a b.
Proof.
  intros d a b c e Ha He. subst.
  apply nvec_add_comm_stateful.
Qed.

Lemma nvec_shift_square : forall d (s x b t df eg : NVec d),
    x = nvec_add s df -> b = nvec_add s eg ->
    t = nvec_add b df -> t = nvec_add x eg.
Proof.
  intros d s x b t df eg Hx Hb Ht. subst.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma nvec_add_mono_right : forall d (a b delta : NVec d),
    nvec_le a b -> nvec_le (nvec_add a delta) (nvec_add b delta).
Proof.
  intros d a b delta Hle index. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  specialize (Hle index). lia.
Qed.

Lemma nvec_add_cancel_left_stateful : forall d (base left right : NVec d),
    nvec_add base left = nvec_add base right -> left = right.
Proof.
  intros d base left right Heq.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Hindex; subst index'.
  apply (f_equal (fun value => Vector.nth value index)) in Heq.
  unfold nvec_add in Heq.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl)
    in Heq.
  now apply Nat.add_cancel_l in Heq.
Qed.

(** The two context replacements used at every node of the mutual
    induction.  Only the total hereditary inequalities [S <= A] and
    [S <= BETA] occur here. *)
Theorem amalgamate_context_extensions : forall d q (B : SBVAS d q)
    (S X Y Z : SRun d q) (CF CG : SContext d q),
    ValidSRun B S ->
    ValidSRun B (scontext_plug CF X) ->
    ValidSRun B (scontext_plug CG Y) ->
    ValidSRun B Z ->
    ContextOrder B X Z -> ContextOrder B Y Z ->
    nvec_le (snd (root_config S)) (snd (root_config X)) ->
    nvec_le (snd (root_config S))
      (snd (root_config (scontext_plug CF X))) ->
    nvec_le (snd (root_config S))
      (snd (root_config (scontext_plug CG Y))) ->
    fst (root_config S) = fst (root_config X) ->
    fst (root_config S) = fst (root_config Y) ->
    fst (root_config S) = fst (root_config (scontext_plug CF X)) ->
    fst (root_config S) = fst (root_config (scontext_plug CG Y)) ->
    nvec_add (snd (root_config S)) (snd (root_config Z)) =
      nvec_add (snd (root_config X)) (snd (root_config Y)) ->
    run_node_count S + run_node_count Z =
      run_node_count X + run_node_count Y ->
    exists gamma,
      ValidSRun B gamma /\
      ContextOrder B (scontext_plug CF X) gamma /\
      ContextOrder B (scontext_plug CG Y) gamma /\
      nvec_add (snd (root_config S)) (snd (root_config gamma)) =
        nvec_add (snd (root_config (scontext_plug CF X)))
          (snd (root_config (scontext_plug CG Y))) /\
      run_node_count S + run_node_count gamma =
        run_node_count (scontext_plug CF X) +
          run_node_count (scontext_plug CG Y).
Proof.
  intros d q B S X Y Z CF CG HS HA HB HZ HXZ HYZ HSX HSA HSB
    HstateX HstateY HstateA HstateB Hcore Hnodes.
  destruct (nvec_le_exact_difference d _ _ HSX) as [df Hxdf].
  assert (Hzdf : snd (root_config Z) =
      nvec_add (snd (root_config Y)) df).
  { rewrite Hxdf in Hcore.
    apply nvec_add_cancel_left_stateful with
      (base := snd (root_config S)).
    assert (Hshuffle :
        nvec_add (nvec_add (snd (root_config S)) df)
          (snd (root_config Y)) =
        nvec_add (snd (root_config S))
          (nvec_add (snd (root_config Y)) df)).
    { apply (proj1 (Vector.eq_nth_iff nat d _ _)).
      intros index index' Heq; subst index'. unfold nvec_add.
      repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
      lia. }
    now rewrite <- Hshuffle. }
  set (T := scontext_plug (scontext_add df CG) Z).
  assert (HTvalid : ValidSRun B T).
  { subst T. rewrite <- (scontext_add_plug_eq_replace d q CG Y Z df).
    eapply replace_subrun_at_valid; eauto.
    symmetry. eapply context_order_root_state; exact HYZ. }
  assert (HBT : ContextOrder B (scontext_plug CG Y) T).
  { subst T. eapply context_order_lift_through_context; eauto. }
  destruct (nvec_le_exact_difference d _ _ HSB) as [eg Hbeg].
  assert (HTdf : snd (root_config T) =
      nvec_add (snd (root_config (scontext_plug CG Y))) df).
  { subst T. rewrite <- (scontext_add_plug_eq_replace d q CG Y Z df).
    pose proof (replace_subrun_at_root d q
      (scontext_plug CG Y) Y Z (scontext_add_plug_path CG Y) df
      ltac:(symmetry; eapply context_order_root_state; exact HYZ) Hzdf) as Hroot.
    exact (proj2 Hroot). }
  assert (HTcounter : snd (root_config T) =
      nvec_add (snd (root_config X)) eg).
  { eapply nvec_shift_square; eauto. }
  assert (HXT : ContextOrder B X T).
  { subst T. eapply context_order_embed_below with (core := Z).
    - exact HXZ.
    - exact HTvalid.
    - transitivity (fst (root_config S)).
      + symmetry. exact HstateX.
      + cbn. transitivity (fst (root_config (scontext_plug CG Y))).
        * exact HstateB.
        * eapply context_order_root_state. exact HBT.
    - rewrite HTcounter. apply nvec_le_add_right. }
  set (gamma := scontext_plug (scontext_add eg CF) T).
  assert (Hgamma_valid : ValidSRun B gamma).
  { subst gamma. rewrite <- (scontext_add_plug_eq_replace d q CF X T eg).
    eapply replace_subrun_at_valid; eauto.
    symmetry. eapply context_order_root_state; exact HXT. }
  assert (HAgamma : ContextOrder B (scontext_plug CF X) gamma).
  { subst gamma. eapply context_order_lift_through_context; eauto. }
  assert (Hgammaeg : snd (root_config gamma) =
      nvec_add (snd (root_config (scontext_plug CF X))) eg).
  { subst gamma. rewrite <- (scontext_add_plug_eq_replace d q CF X T eg).
    pose proof (replace_subrun_at_root d q
      (scontext_plug CF X) X T (scontext_add_plug_path CF X) eg
      ltac:(symmetry; eapply context_order_root_state; exact HXT) HTcounter)
      as Hroot. exact (proj2 Hroot). }
  exists gamma. split; [exact Hgamma_valid|].
  split; [exact HAgamma|]. split.
  - eapply context_order_embed_below with (core := T).
    + exact HBT.
    + exact Hgamma_valid.
    + transitivity (fst (root_config S)); [symmetry; exact HstateB|].
      transitivity (fst (root_config (scontext_plug CF X))).
      * exact HstateA.
      * eapply context_order_root_state. exact HAgamma.
    + change (nvec_le (snd (root_config (scontext_plug CG Y)))
        (snd (root_config gamma))).
      rewrite Hgammaeg, Hbeg.
      apply nvec_add_mono_right. exact HSA.
  - split.
    + rewrite Hgammaeg, Hbeg.
      apply (proj1 (Vector.eq_nth_iff nat d _ _)).
      intros index index' Heq; subst index'. unfold nvec_add.
      repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
      lia.
    + subst gamma T. repeat rewrite context_plug_node_count.
      repeat rewrite scontext_add_node_count. lia.
Qed.

Lemma positional_context_orders_states : forall d q (B : SBVAS d q)
    (left right : SRuns d q),
    PositionalContextOrders B left right ->
    List.map fst (sruns_configs left) = List.map fst (sruns_configs right).
Proof.
  intros d q B left right H. induction H; cbn; [reflexivity|].
  rewrite IHPositionalContextOrders.
  f_equal. eapply context_order_root_state; exact H.
Qed.

Lemma positional_context_orders_counters : forall d q (B : SBVAS d q)
    (left right : SRuns d q),
    PositionalContextOrders B left right ->
    NVecListLe (List.map snd (sruns_configs left))
      (List.map snd (sruns_configs right)).
Proof.
  intros d q B left right H. induction H; cbn; constructor; auto.
  destruct H as [_ [_ [family [_ [Hpositive Hiso]]]]].
  rewrite <- (srun_isomorphic_root _ _ _ _ Hiso).
  exact (proj2 (positive_context_family_root_general Hpositive)).
Qed.

Lemma add_displacement_sum_shift : forall d (offset : ZVec d)
    left right target delta,
    nvec_sum right = nvec_add (nvec_sum left) delta ->
    add_displacement offset left = Some target ->
    add_displacement offset right = Some (nvec_add target delta).
Proof.
  intros d offset left right target delta Hsum Happly.
  unfold add_displacement in Happly |- *.
  assert (Hold : zvec_add offset (nvec_to_zvec (nvec_sum left)) =
      nvec_to_zvec target).
  { apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros index index' Heq; subst index'. unfold nvec_to_zvec.
    rewrite (nth_map Z.of_nat target index index eq_refl).
    eapply zvec_to_nvec_sound; eauto. }
  rewrite Hsum, nvec_to_zvec_add, zvec_add_assoc, Hold,
    <- nvec_to_zvec_add. apply zvec_to_nvec_of_nvec.
Qed.

Lemma nvec_sum_exact_cons_stateful : forall d
    (s a b g : NVec d) ss aa bb gg,
    nvec_add s g = nvec_add a b ->
    nvec_add (nvec_sum ss) (nvec_sum gg) =
      nvec_add (nvec_sum aa) (nvec_sum bb) ->
    nvec_add (nvec_sum (s :: ss)) (nvec_sum (g :: gg)) =
      nvec_add (nvec_sum (a :: aa)) (nvec_sum (b :: bb)).
Proof.
  intros. repeat rewrite nvec_sum_cons_context.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  apply (f_equal (fun v => Vector.nth v index)) in H.
  apply (f_equal (fun v => Vector.nth v index)) in H0.
  unfold nvec_add in *.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in *.
  lia.
Qed.

Lemma add_displacement_four_exact : forall d (offset : ZVec d)
    ss aa bb gg s a b g,
    nvec_add (nvec_sum ss) (nvec_sum gg) =
      nvec_add (nvec_sum aa) (nvec_sum bb) ->
    add_displacement offset ss = Some s ->
    add_displacement offset aa = Some a ->
    add_displacement offset bb = Some b ->
    add_displacement offset gg = Some g ->
    nvec_add s g = nvec_add a b.
Proof.
  intros d offset ss aa bb gg s a b g Hsum Hs Ha Hb Hg.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  pose proof (zvec_to_nvec_sound d _ _ Hs index) as Es.
  pose proof (zvec_to_nvec_sound d _ _ Ha index) as Ea.
  pose proof (zvec_to_nvec_sound d _ _ Hb index) as Eb.
  pose proof (zvec_to_nvec_sound d _ _ Hg index) as Eg.
  apply (f_equal (fun v => Vector.nth v index)) in Hsum.
  unfold zvec_add, nvec_to_zvec, nvec_add in *.
  repeat rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl) in *.
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl) in *.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in *.
  lia.
Qed.

Lemma valid_sruns_head_stateful : forall d q (B : SBVAS d q)
    (run : SRun d q) runs,
    ValidSRuns B (sruns_cons run runs) -> ValidSRun B run.
Proof. intros d q B run runs H; inversion H; assumption. Qed.

Lemma valid_sruns_tail_stateful : forall d q (B : SBVAS d q)
    (run : SRun d q) runs,
    ValidSRuns B (sruns_cons run runs) -> ValidSRuns B runs.
Proof. intros d q B run runs H; inversion H; assumption. Qed.

Lemma inserted_family_amalgamation_mut : forall d q (B : SBVAS d q),
  (forall (run : SRun d q) (first : SContextFamily run),
    forall second : SContextFamily run,
    ValidSRun B run ->
    ValidSRun B (insert_context_family first) ->
    ValidSRun B (insert_context_family second) ->
    CompatibleContextFamily run first ->
    CompatibleContextFamily run second ->
    HereditarilyPositive run first ->
    HereditarilyPositive run second ->
    exists merged,
      ValidSRun B merged /\
      ContextOrder B (insert_context_family first) merged /\
      ContextOrder B (insert_context_family second) merged /\
      nvec_add (snd (root_config run)) (snd (root_config merged)) =
        nvec_add (snd (root_config (insert_context_family first)))
          (snd (root_config (insert_context_family second))) /\
      run_node_count run + run_node_count merged =
        run_node_count (insert_context_family first) +
          run_node_count (insert_context_family second)) /\
  (forall (runs : SRuns d q) (first : SContextFamilies runs),
    forall second : SContextFamilies runs,
    ValidSRuns B runs ->
    ValidSRuns B (insert_context_families first) ->
    ValidSRuns B (insert_context_families second) ->
    CompatibleContextFamilies runs first ->
    CompatibleContextFamilies runs second ->
    HereditarilyPositiveFamilies runs first ->
    HereditarilyPositiveFamilies runs second ->
    exists merged,
      ValidSRuns B merged /\
      PositionalContextOrders B (insert_context_families first) merged /\
      PositionalContextOrders B (insert_context_families second) merged /\
      nvec_add (nvec_sum (List.map snd (sruns_configs runs)))
        (nvec_sum (List.map snd (sruns_configs merged))) =
      nvec_add (nvec_sum (List.map snd
        (sruns_configs (insert_context_families first))))
        (nvec_sum (List.map snd
          (sruns_configs (insert_context_families second)))) /\
      runs_node_count runs + runs_node_count merged =
        runs_node_count (insert_context_families first) +
          runs_node_count (insert_context_families second)).
Proof.
  intros d q B. apply SContextFamily_SContextFamilies_ind.
  - intros config CF second Hbase HF HG HCF HCG HPF HPG.
    rewrite <- (context_family_leaf_eta d q config second) in *.
    pose (base := srun_leaf config).
    eapply amalgamate_context_extensions with
      (S := base) (X := base) (Y := base) (Z := base)
      (CF := CF) (CG := context_family_context second); try eassumption.
    + apply context_order_refl. exact Hbase.
    + apply context_order_refl. exact Hbase.
    + apply nvec_le_refl.
    + exact (proj2 (positive_context_family_root_general HPF)).
    + exact (proj2 (positive_context_family_root_general HPG)).
    + reflexivity.
    + reflexivity.
    + symmetry. exact (compatible_context_family_root _ _ _ _ HCF).
    + symmetry. exact (compatible_context_family_root _ _ _ _ HCG).
    + apply nvec_add_comm_stateful.
    + lia.
  - intros rule children result CF first_children IH matchedF second
      Hbase HF HG HCF HCG HPF HPG.
    pose (second_children := context_family_children second).
    pose (matchedG := context_family_matched second).
    assert (HGcore : ValidSRun B
      (srun_node rule (insert_context_families second_children) matchedG)).
    { unfold second_children, matchedG. eapply valid_scontext_plug_core.
      pose proof (context_family_node_eta d q rule children result second) as E.
      rewrite <- E in HG. exact HG. }
    assert (HFcore : ValidSRun B
      (srun_node rule (insert_context_families first_children) matchedF)).
    { cbn in HF. eapply valid_scontext_plug_core; eauto. }
    assert (Hbase_children : ValidSRuns B children).
    { inversion Hbase; subst; assumption. }
    assert (HFchildren : ValidSRuns B (insert_context_families first_children)).
    { inversion HFcore; subst; assumption. }
    assert (HGchildren : ValidSRuns B (insert_context_families second_children)).
    { inversion HGcore; subst; assumption. }
    destruct (IH second_children Hbase_children HFchildren HGchildren
      (compatible_family_children_general HCF)
      (compatible_family_children_general HCG)
      (positive_family_children_general HPF)
      (positive_family_children_general HPG)) as
      [merged_children [HMvalid [HFM [HGM [Hsum Hcount]]]]].
    destruct (nvec_le_exact_difference d
      (nvec_sum (List.map snd (sruns_configs
        (insert_context_families first_children))))
      (nvec_sum (List.map snd (sruns_configs merged_children)))
      (nvec_sum_le d _ _
        (positional_context_orders_counters d q B _ _ HFM))) as [delta Hdelta].
    set (merged_result :=
      (fst matchedF, nvec_add (snd matchedF) delta)).
    set (Z := srun_node rule merged_children merged_result).
    assert (HZ : ValidSRun B Z).
    { subst Z merged_result. inversion HFcore; subst. econstructor; eauto.
      - rewrite <- (positional_context_orders_states d q B _ _ HFM).
        match goal with
        | Hstates : Permutation
            (List.map fst (sruns_configs (insert_context_families first_children)))
            (input_states rule) |- _ => exact Hstates
        end.
      - eapply add_displacement_sum_shift; eauto. }
    assert (Hcore_exact :
      nvec_add (snd result) (snd (root_config Z)) =
      nvec_add (snd matchedF) (snd matchedG)).
    { subst Z merged_result. cbn.
      inversion Hbase; subst. inversion HFcore; subst. inversion HGcore; subst.
      inversion HZ; subst.
      eapply add_displacement_four_exact; eauto. }
    assert (HXF : nvec_le (snd result) (snd matchedF)).
    { eapply family_node_core_root_monotone; eauto.
      exact (positive_family_children_general HPF). }
    assert (HmatchedGdelta : snd matchedG = nvec_add (snd result) delta).
    { unfold Z, merged_result in Hcore_exact. cbn in Hcore_exact.
      apply nvec_add_cancel_left_stateful with (base := snd matchedF).
      assert (Hshuffle :
        nvec_add (snd result) (nvec_add (snd matchedF) delta) =
        nvec_add (snd matchedF) (nvec_add (snd result) delta)).
      { rewrite <- nvec_add_assoc_stateful.
        rewrite (nvec_add_comm_stateful d (snd result) (snd matchedF)).
        apply nvec_add_assoc_stateful. }
      rewrite <- Hshuffle. symmetry. exact Hcore_exact. }
    assert (HXZ : ContextOrder B
      (srun_node rule (insert_context_families first_children) matchedF) Z).
    { subst Z merged_result. eapply context_order_same_root_rule; eauto.
      split.
      - reflexivity.
      - apply nvec_le_add_right. }
    assert (HYZ : ContextOrder B
      (srun_node rule (insert_context_families second_children) matchedG) Z).
    { subst Z merged_result. eapply context_order_same_root_rule; eauto.
      split.
      - transitivity (fst result).
        * exact (compatible_family_matched_state_general HCG).
        * symmetry. exact (compatible_family_matched_state_general HCF).
      - rewrite HmatchedGdelta. apply nvec_add_mono_right. exact HXF. }
    pose proof (context_family_node_eta d q rule children result second) as Esecond.
    rewrite <- Esecond.
    eapply amalgamate_context_extensions with
      (S := srun_node rule children result)
      (X := srun_node rule (insert_context_families first_children) matchedF)
      (Y := srun_node rule (insert_context_families second_children) matchedG)
      (Z := Z) (CF := CF) (CG := context_family_context second);
      try eassumption.
    + pose proof (context_family_node_eta d q rule children result second) as E.
      rewrite <- E in HG. exact HG.
    + exact (proj2 (positive_context_family_root_general HPF)).
    + pose proof (proj2 (positive_context_family_root_general HPG)) as H.
      rewrite <- Esecond in H. exact H.
    + symmetry. exact (compatible_family_matched_state_general HCF).
    + symmetry. exact (compatible_family_matched_state_general HCG).
    + symmetry. exact (compatible_context_family_root _ _ _ _ HCF).
    + pose proof (compatible_context_family_root _ _ _ _ HCG) as H.
      rewrite <- Esecond in H. symmetry. exact H.
    + subst Z. cbn in Hcount |- *. lia.
  - intros second Hbase HF HG HCF HCG HPF HPG.
    pose proof (context_families_eta_general second) as Esecond_nil.
    rewrite Esecond_nil in *.
    exists sruns_nil.
    refine (conj (@valid_sruns_nil d q B)
      (conj (@positional_context_orders_nil d q B)
        (conj (@positional_context_orders_nil d q B) (conj _ eq_refl)))).
    cbn. rewrite !nvec_add_zero_left_stateful. reflexivity.
  - intros run runs first IHrun firsts IHruns second Hbase HF HG
      HCF HCG HPF HPG.
    pose (second_head := context_families_head second).
    pose (second_tail := context_families_tail second).
    pose proof (context_families_eta d q run runs second) as Esecond.
    rewrite <- Esecond in *.
    cbn in HF, HG.
    destruct (IHrun second_head
      (valid_sruns_head_stateful d q B run runs Hbase)
      (valid_sruns_head_stateful d q B
        (insert_context_family first) (insert_context_families firsts) HF)
      (valid_sruns_head_stateful d q B
        (insert_context_family second_head)
        (insert_context_families second_tail) HG)
      (compatible_families_head d q run runs (families_cons first firsts) HCF)
      (compatible_families_head d q run runs
        (families_cons second_head second_tail) HCG)
      (positive_families_head d q run runs (families_cons first firsts) HPF)
      (positive_families_head d q run runs
        (families_cons second_head second_tail) HPG)) as
      [merged [HM [HFM [HGM [Hexact Hnodes]]]]].
    destruct (IHruns second_tail
      (valid_sruns_tail_stateful d q B run runs Hbase)
      (valid_sruns_tail_stateful d q B
        (insert_context_family first) (insert_context_families firsts) HF)
      (valid_sruns_tail_stateful d q B
        (insert_context_family second_head)
        (insert_context_families second_tail) HG)
      (compatible_families_tail d q run runs (families_cons first firsts) HCF)
      (compatible_families_tail d q run runs
        (families_cons second_head second_tail) HCG)
      (positive_families_tail d q run runs (families_cons first firsts) HPF)
      (positive_families_tail d q run runs
        (families_cons second_head second_tail) HPG)) as
      [mergeds [HMs [HFMs [HGMs [Hexacts Hnodess]]]]].
    exists (sruns_cons merged mergeds). repeat split; cbn.
    + constructor; assumption.
    + constructor; assumption.
    + constructor; assumption.
    + eapply nvec_sum_exact_cons_stateful; eauto.
    + unfold second_head, second_tail in Hnodes, Hnodess |- *.
      cbn in Hnodes, Hnodess |- *. lia.
Qed.

Theorem inserted_family_amalgamation : forall d q (B : SBVAS d q)
    (run : SRun d q) (first second : SContextFamily run),
    ValidSRun B run ->
    ValidSRun B (insert_context_family first) ->
    ValidSRun B (insert_context_family second) ->
    CompatibleContextFamily run first ->
    CompatibleContextFamily run second ->
    HereditarilyPositive run first ->
    HereditarilyPositive run second ->
    exists merged,
      ValidSRun B merged /\
      ContextOrder B (insert_context_family first) merged /\
      ContextOrder B (insert_context_family second) merged /\
      nvec_add (snd (root_config run)) (snd (root_config merged)) =
        nvec_add (snd (root_config (insert_context_family first)))
          (snd (root_config (insert_context_family second))) /\
      run_node_count run + run_node_count merged =
        run_node_count (insert_context_family first) +
          run_node_count (insert_context_family second).
Proof.
  intros. eapply (proj1 (inserted_family_amalgamation_mut d q B)); eauto.
Qed.

Theorem stateful_context_order_amalgamation : forall d q (B : SBVAS d q)
    (sigma alpha beta : SRun d q),
    ValidSRun B sigma ->
    ValidSRun B alpha ->
    ValidSRun B beta ->
    ContextOrder B sigma alpha ->
    ContextOrder B sigma beta ->
    exists gamma : SRun d q,
      ValidSRun B gamma /\
      ContextOrder B alpha gamma /\
      ContextOrder B beta gamma /\
      nvec_add (snd (root_config sigma)) (snd (root_config gamma)) =
        nvec_add (snd (root_config alpha)) (snd (root_config beta)) /\
      run_node_count sigma + run_node_count gamma =
        run_node_count alpha + run_node_count beta.
Proof.
  intros d q B sigma alpha beta Hsigma Halpha Hbeta Hsa Hsb.
  destruct Hsa as [_ [_ [first [Hfirst_compatible
    [Hfirst_positive Hfirst_iso]]]]].
  destruct Hsb as [_ [_ [second [Hsecond_compatible
    [Hsecond_positive Hsecond_iso]]]]].
  assert (Hfirst_valid : ValidSRun B (insert_context_family first)).
  { eapply srun_isomorphic_valid; [|exact Halpha].
    apply srun_isomorphic_sym_stateful. exact Hfirst_iso. }
  assert (Hsecond_valid : ValidSRun B (insert_context_family second)).
  { eapply srun_isomorphic_valid; [|exact Hbeta].
    apply srun_isomorphic_sym_stateful. exact Hsecond_iso. }
  destruct (inserted_family_amalgamation d q B sigma first second
    Hsigma Hfirst_valid Hsecond_valid Hfirst_compatible Hsecond_compatible
    Hfirst_positive Hsecond_positive) as
    [gamma [Hgamma [Hfirst_gamma [Hsecond_gamma [Hexact Hcount]]]]].
  exists gamma. split; [exact Hgamma|]. split.
  - eapply context_order_trans with
      (second := insert_context_family first).
    + eapply context_order_of_isomorphism; eauto.
      apply srun_isomorphic_sym_stateful. exact Hfirst_iso.
    + exact Hfirst_gamma.
  - split.
    + eapply context_order_trans with
        (second := insert_context_family second).
      * eapply context_order_of_isomorphism; eauto.
        apply srun_isomorphic_sym_stateful. exact Hsecond_iso.
      * exact Hsecond_gamma.
    + split.
      * rewrite <- (srun_isomorphic_root_counter d q _ _ Hfirst_iso).
        rewrite <- (srun_isomorphic_root_counter d q _ _ Hsecond_iso).
        exact Hexact.
      * rewrite <- (srun_isomorphic_node_count d q _ _ Hfirst_iso).
        rewrite <- (srun_isomorphic_node_count d q _ _ Hsecond_iso).
        exact Hcount.
Qed.

Lemma context_order_root_counter_le_stateful : forall d q
    (B : SBVAS d q) left right,
    ContextOrder B left right ->
    nvec_le (snd (root_config left)) (snd (root_config right)).
Proof.
  intros d q B left right [_ [_ [family [_ [Hpositive Hiso]]]]].
  rewrite <- (srun_isomorphic_root_counter d q _ _ Hiso).
  exact (proj2 (positive_context_family_root_general Hpositive)).
Qed.

Lemma srun_path_valid_focus : forall d q (B : SBVAS d q)
    (whole focus : SRun d q) (path : SRunPath whole focus),
    ValidSRun B whole -> ValidSRun B focus.
Proof.
  intros d q B whole focus path. induction path; intro Hvalid.
  - exact Hvalid.
  - apply IHpath. inversion Hvalid; subst.
    eapply valid_sruns_frame_member_stateful; eauto.
Qed.

Theorem stateful_context_transfer_lemma_8 : forall d q (B : SBVAS d q)
    (sigma alpha beta nu : SRun d q)
    (path : SRunPath beta nu),
    ValidSRun B sigma ->
    ValidSRun B alpha ->
    ValidSRun B beta ->
    ContextOrder B sigma alpha ->
    ContextOrder B sigma nu ->
    exists beta' : SRun d q,
      ValidSRun B beta' /\
      fst (root_config alpha) = fst (root_config sigma) /\
      fst (root_config beta') = fst (root_config beta) /\
      nvec_add (snd (root_config alpha)) (snd (root_config beta)) =
        nvec_add (snd (root_config sigma)) (snd (root_config beta')) /\
      run_node_count alpha + run_node_count beta =
        run_node_count sigma + run_node_count beta'.
Proof.
  intros d q B sigma alpha beta nu path Hsigma Halpha Hbeta Hsa Hsnu.
  assert (Hnu : ValidSRun B nu).
  { eapply srun_path_valid_focus; eauto. }
  destruct (stateful_context_order_amalgamation d q B sigma alpha nu
    Hsigma Halpha Hnu Hsa Hsnu) as
    [nu' [Hnu' [Hanu' [Hnunu' [Hamalg_counter Hamalg_nodes]]]]].
  destruct (nvec_le_exact_difference d _ _
    (context_order_root_counter_le_stateful d q B _ _ Hsa)) as
    [delta Halpha_delta].
  assert (Hnu'_delta : snd (root_config nu') =
      nvec_add (snd (root_config nu)) delta).
  { apply nvec_add_cancel_left_stateful with
      (base := snd (root_config sigma)).
    rewrite Hamalg_counter, Halpha_delta.
    apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros index index' Heq; subst index'. unfold nvec_add.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
    lia. }
  assert (Hnu'_state : fst (root_config nu') = fst (root_config nu)).
  { symmetry. eapply context_order_root_state. exact Hnunu'. }
  destruct (subrun_replacement_exact d q B beta nu nu' path delta
    Hbeta Hnu' Hnu'_state Hnu'_delta) as
    [beta' [Hbeta'_def [Hbeta' [Hbeta'_state
      [Hbeta'_counter Hreplace_nodes]]]]].
  exists beta'. split; [exact Hbeta'|]. split.
  - symmetry. eapply context_order_root_state. exact Hsa.
  - split; [exact Hbeta'_state|]. split.
    + rewrite Halpha_delta, Hbeta'_counter.
      apply (proj1 (Vector.eq_nth_iff nat d _ _)).
      intros index index' Heq; subst index'. unfold nvec_add.
      repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
      lia.
    + lia.
Qed.
