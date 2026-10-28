From Coq Require Import List Vector ZArith Lia Arith.PeanoNat Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.BVASS Require Import Stateful.

Definition RootConfigLe {d q} (left right : SConfig d q) : Prop :=
  fst left = fst right /\ nvec_le (snd left) (snd right).

Inductive SRunsIn {d q} (run : SRun d q) : SRuns d q -> Prop :=
| sruns_in_here : forall runs, SRunsIn run (sruns_cons run runs)
| sruns_in_later : forall other runs,
    SRunsIn run runs -> SRunsIn run (sruns_cons other runs).

Inductive OrderedDecorEmbed {d q} : SRun d q -> SRun d q -> Prop :=
| ordered_embed_leaf : forall config,
    OrderedDecorEmbed (srun_leaf config) (srun_leaf config)
| ordered_embed_node : forall rule left_children right_children
    left_result right_result,
    OrderedDecorEmbeds left_children right_children ->
    OrderedDecorEmbed (srun_node rule left_children left_result)
      (srun_node rule right_children right_result)
| ordered_embed_below : forall small rule children result child,
    SRunsIn child children -> OrderedDecorEmbed small child ->
    OrderedDecorEmbed small (srun_node rule children result)
with OrderedDecorEmbeds {d q} : SRuns d q -> SRuns d q -> Prop :=
| ordered_embeds_nil : OrderedDecorEmbeds sruns_nil sruns_nil
| ordered_embeds_cons : forall left right lefts rights,
    RootConfigLe (root_config left) (root_config right) ->
    OrderedDecorEmbed left right -> OrderedDecorEmbeds lefts rights ->
    OrderedDecorEmbeds (sruns_cons left lefts) (sruns_cons right rights).

Scheme OrderedDecorEmbed_ind' := Induction for OrderedDecorEmbed Sort Prop
with OrderedDecorEmbeds_ind' := Induction for OrderedDecorEmbeds Sort Prop.
Combined Scheme OrderedDecorEmbed_mutind
  from OrderedDecorEmbed_ind', OrderedDecorEmbeds_ind'.

Fixpoint sruns_append {d q} (left right : SRuns d q) : SRuns d q :=
  match left with
  | sruns_nil => right
  | sruns_cons run tail => sruns_cons run (sruns_append tail right)
  end.

Inductive SContext (d q : nat) : Type :=
| scontext_hole : SContext d q
| scontext_node : SRule d q -> SRuns d q -> SContext d q ->
    SRuns d q -> SConfig d q -> SContext d q.

Arguments scontext_hole {d q}.
Arguments scontext_node {d q} _ _ _ _ _.

Fixpoint scontext_plug {d q} (context : SContext d q) (run : SRun d q) :=
  match context with
  | scontext_hole => run
  | scontext_node rule before inner after result =>
      srun_node rule
        (sruns_append before (sruns_cons (scontext_plug inner run) after))
        result
  end.

Fixpoint scontext_compose {d q} (outer inner : SContext d q) : SContext d q :=
  match outer with
  | scontext_hole => inner
  | scontext_node rule before nested after result =>
      scontext_node rule before (scontext_compose nested inner) after result
  end.

Lemma scontext_plug_compose : forall d q (outer inner : SContext d q) run,
    scontext_plug (scontext_compose outer inner) run =
    scontext_plug outer (scontext_plug inner run).
Proof. intros d q outer; induction outer; intros; cbn; now rewrite ?IHouter. Qed.

Definition ContextCompatible {d q} (context : SContext d q)
    (run : SRun d q) : Prop :=
  fst (root_config (scontext_plug context run)) = fst (root_config run).

Lemma context_compatible_replace : forall d q (context : SContext d q)
    (left right : SRun d q),
    ContextCompatible context left ->
    fst (root_config left) = fst (root_config right) ->
    ContextCompatible context right.
Proof.
  intros d q context. induction context; intros left right Hcompatible Hroot;
    unfold ContextCompatible in *; cbn in *.
  - reflexivity.
  - now rewrite <- Hroot.
Qed.

Inductive SRunsRemove {d q} (run : SRun d q) : SRuns d q -> SRuns d q -> Prop :=
| sruns_remove_here : forall runs,
    SRunsRemove run (sruns_cons run runs) runs
| sruns_remove_later : forall head runs remainder,
    SRunsRemove run runs remainder ->
    SRunsRemove run (sruns_cons head runs) (sruns_cons head remainder).

(* Unordered tree isomorphism.  Removal is by occurrence, so duplicate
   equal-state children remain separately accounted for. *)
Inductive SRunIsomorphic {d q} : SRun d q -> SRun d q -> Prop :=
| srun_iso_leaf : forall config,
    SRunIsomorphic (srun_leaf config) (srun_leaf config)
| srun_iso_node : forall rule left right result,
    SRunsIsomorphic left right ->
    SRunIsomorphic (srun_node rule left result) (srun_node rule right result)
with SRunsIsomorphic {d q} : SRuns d q -> SRuns d q -> Prop :=
| sruns_iso_nil : SRunsIsomorphic sruns_nil sruns_nil
| sruns_iso_cons : forall left lefts right rights remainder,
    SRunsRemove right rights remainder ->
    SRunIsomorphic left right ->
    SRunsIsomorphic lefts remainder ->
    SRunsIsomorphic (sruns_cons left lefts) rights.

Scheme SRunIsomorphic_ind' := Induction for SRunIsomorphic Sort Prop
with SRunsIsomorphic_ind' := Induction for SRunsIsomorphic Sort Prop.
Combined Scheme SRunIsomorphic_mutind
  from SRunIsomorphic_ind', SRunsIsomorphic_ind'.

Lemma sruns_remove_commute : forall d q (first second : SRun d q)
    source after_first after_both,
    SRunsRemove first source after_first ->
    SRunsRemove second after_first after_both ->
    exists after_second,
      SRunsRemove second source after_second /\
      SRunsRemove first after_second after_both.
Proof.
  intros d q first second source after_first after_both Hfirst.
  revert after_both. induction Hfirst; intros after_both Hsecond.
  - exists (sruns_cons first after_both). split.
    + constructor 2. exact Hsecond.
    + constructor.
  - inversion Hsecond as [remaining|kept runs' remainder' Hlater]; subst.
    + exists runs. split; [constructor|exact Hfirst].
    + destruct (IHHfirst _ Hlater) as [after_second [Hremove2 Hremove1]].
      exists (sruns_cons head after_second). split; constructor; assumption.
Qed.

Lemma sruns_iso_remove_image : forall d q (selected : SRun d q)
    source remainder,
    SRunsRemove selected source remainder ->
    forall target, SRunsIsomorphic source target ->
    exists selected_target target_remainder,
      SRunsRemove selected_target target target_remainder /\
      SRunIsomorphic selected selected_target /\
      SRunsIsomorphic remainder target_remainder.
Proof.
  intros d q selected source remainder Hremove.
  induction Hremove; intros target Hiso.
  - inversion Hiso; subst.
    eexists _, _. repeat split; eauto.
  - inversion Hiso; subst.
    match goal with
    | Htail_iso : SRunsIsomorphic runs ?right_remainder |- _ =>
        destruct (IHHremove _ Htail_iso) as
          [selected_target [target_remainder
            [Hselected_remove [Hselected_iso Htail_after]]]]
    end.
    match goal with
    | Hhead_remove : SRunsRemove ?right_head target ?right_remainder |- _ =>
        destruct (sruns_remove_commute d q right_head selected_target
          target right_remainder target_remainder
          Hhead_remove Hselected_remove) as
          [after_selected [Hremove_selected Hremove_head]]
    end.
    exists selected_target, after_selected. repeat split; try assumption.
    eapply sruns_iso_cons; eauto.
Qed.

Fixpoint srun_size {d q} (run : SRun d q) : nat :=
  match run with
  | srun_leaf _ => 1
  | srun_node _ children _ => S (sruns_size children)
  end
with sruns_size {d q} (runs : SRuns d q) : nat :=
  match runs with
  | sruns_nil => 0
  | sruns_cons run tail => S (srun_size run + sruns_size tail)
  end.

Lemma srun_children_size_lt : forall d q rule children result,
    sruns_size children < srun_size (@srun_node d q rule children result).
Proof. cbn; lia. Qed.

Lemma sruns_head_size_lt : forall d q (run : SRun d q) tail,
    srun_size run < sruns_size (sruns_cons run tail).
Proof. cbn; lia. Qed.

Lemma sruns_tail_size_lt : forall d q (run : SRun d q) tail,
    sruns_size tail < sruns_size (sruns_cons run tail).
Proof. cbn; lia. Qed.

Lemma srun_isomorphic_trans_bounded : forall d q bound,
  (forall first : SRun d q, srun_size first < bound ->
    forall second third,
      SRunIsomorphic first second -> SRunIsomorphic second third ->
      SRunIsomorphic first third) /\
  (forall first : SRuns d q, sruns_size first < bound ->
    forall second third,
      SRunsIsomorphic first second -> SRunsIsomorphic second third ->
      SRunsIsomorphic first third).
Proof.
  intros d q bound. induction bound as [|bound IH].
  - split; intros; lia.
  - destruct IH as [IHrun IHruns]. split.
    + intros first Hsize second third Hfirst Hsecond.
      inversion Hfirst; subst.
      * inversion Hsecond; subst; constructor.
      * inversion Hsecond; subst. constructor.
        eapply IHruns.
        -- cbn in Hsize. lia.
        -- exact H.
        -- assumption.
    + intros first Hsize second third Hfirst Hsecond.
      inversion Hfirst; subst.
      * inversion Hsecond; subst; constructor.
      * destruct (sruns_iso_remove_image d q right second remainder H
          third Hsecond) as
          [third_head [third_tail [Hremove [Hmiddle_head Hmiddle_tail]]]].
        eapply sruns_iso_cons with
          (right := third_head) (remainder := third_tail).
        -- exact Hremove.
        -- eapply IHrun.
           ++ cbn in Hsize. lia.
           ++ exact H0.
           ++ exact Hmiddle_head.
        -- eapply IHruns.
           ++ cbn in Hsize. lia.
           ++ exact H1.
           ++ exact Hmiddle_tail.
Qed.

Theorem srun_isomorphic_trans : forall d q (first second third : SRun d q),
    SRunIsomorphic first second -> SRunIsomorphic second third ->
    SRunIsomorphic first third.
Proof.
  intros d q first second third Hfirst Hsecond.
  eapply (proj1 (srun_isomorphic_trans_bounded d q
    (S (srun_size first))) first); eauto; lia.
Qed.

Theorem sruns_isomorphic_trans : forall d q (first second third : SRuns d q),
    SRunsIsomorphic first second -> SRunsIsomorphic second third ->
    SRunsIsomorphic first third.
Proof.
  intros d q first second third Hfirst Hsecond.
  eapply (proj2 (srun_isomorphic_trans_bounded d q
    (S (sruns_size first))) first); eauto; lia.
Qed.


(* Exactly one context is stored for every node of the indexed run. *)
Inductive SContextFamily {d q} : SRun d q -> Type :=
| family_leaf : forall config,
    SContext d q -> SContextFamily (srun_leaf config)
| family_node : forall rule children result,
    SContext d q -> SContextFamilies children -> SConfig d q ->
    SContextFamily (srun_node rule children result)
with SContextFamilies {d q} : SRuns d q -> Type :=
| families_nil : SContextFamilies sruns_nil
| families_cons : forall run runs,
    SContextFamily run -> SContextFamilies runs ->
    SContextFamilies (sruns_cons run runs).

Arguments family_leaf {d q config} _.
Arguments family_node {d q rule children result} _ _ _.
Arguments families_nil {d q}.
Arguments families_cons {d q run runs} _ _.

Scheme SContextFamily_ind' := Induction for SContextFamily Sort Prop
with SContextFamilies_ind' := Induction for SContextFamilies Sort Prop.
Combined Scheme SContextFamily_SContextFamilies_ind
  from SContextFamily_ind', SContextFamilies_ind'.

Fixpoint insert_context_family {d q} {run : SRun d q}
    (family : SContextFamily run) : SRun d q :=
  match family with
  | family_leaf context => scontext_plug context run
  | @family_node _ _ rule children result context families matched =>
      scontext_plug context
        (srun_node rule (insert_context_families families) matched)
  end
with insert_context_families {d q} {runs : SRuns d q}
    (families : SContextFamilies runs) : SRuns d q :=
  match families with
  | families_nil => sruns_nil
  | families_cons family families' =>
      sruns_cons (insert_context_family family)
        (insert_context_families families')
  end.

(* The signed effect of a context is its root counter minus its hole
   counter.  A family effect is the sum of the effects assigned to all
   original nodes in the corresponding subtree. *)
Definition signed_counter_effect {d} (lower upper : NVec d) : ZVec d :=
  Vector.map2 Z.sub (nvec_to_zvec upper) (nvec_to_zvec lower).

Definition scontext_effect {d q} (context : SContext d q)
    (hole : SRun d q) : ZVec d :=
  signed_counter_effect (snd (root_config hole))
    (snd (root_config (scontext_plug context hole))).

Fixpoint context_family_effect {d q} {run : SRun d q}
    (family : SContextFamily run) : ZVec d :=
  match family with
  | @family_leaf _ _ config context =>
      scontext_effect context (srun_leaf config)
  | @family_node _ _ rule children result context families matched =>
      zvec_add
        (scontext_effect context
          (srun_node rule (insert_context_families families) matched))
        (context_families_effect families)
  end
with context_families_effect {d q} {runs : SRuns d q}
    (families : SContextFamilies runs) : ZVec d :=
  match families with
  | families_nil => zvec_zero d
  | families_cons family tail =>
      zvec_add (context_family_effect family)
        (context_families_effect tail)
  end.

Definition context_families_head {d q} {runs : SRuns d q}
    (families : SContextFamilies runs) :
    match runs return Type with
    | sruns_nil => unit
    | sruns_cons run _ => SContextFamily run
    end :=
  match families with
  | families_nil => tt
  | families_cons family _ => family
  end.

Definition context_families_tail {d q} {runs : SRuns d q}
    (families : SContextFamilies runs) :
    match runs return Type with
    | sruns_nil => unit
    | sruns_cons _ tail => SContextFamilies tail
    end :=
  match families with
  | families_nil => tt
  | families_cons _ tail => tail
  end.

Definition context_family_context {d q} {run : SRun d q}
    (family : SContextFamily run) : SContext d q :=
  match family with
  | family_leaf context => context
  | family_node context _ _ => context
  end.

Definition context_family_children {d q} {run : SRun d q}
    (family : SContextFamily run) :
    match run return Type with
    | srun_leaf _ => unit
    | srun_node _ children _ => SContextFamilies children
    end :=
  match family with
  | family_leaf _ => tt
  | family_node _ families _ => families
  end.

Definition context_family_matched {d q} {run : SRun d q}
    (family : SContextFamily run) :
    match run return Type with
    | srun_leaf _ => unit
    | srun_node _ _ _ => SConfig d q
    end :=
  match family with
  | family_leaf _ => tt
  | family_node _ _ matched => matched
  end.

Definition context_families_eta_general {d q} {runs : SRuns d q}
    (families : SContextFamilies runs) :
    match runs as indexed return SContextFamilies indexed -> Prop with
    | sruns_nil => fun current => current = families_nil
    | sruns_cons run tail => fun current =>
        families_cons (context_families_head current)
          (context_families_tail current) = current
    end families :=
  match families with
  | families_nil => eq_refl
  | families_cons _ _ => eq_refl
  end.

Lemma context_families_eta : forall d q (run : SRun d q) runs
    (families : SContextFamilies (sruns_cons run runs)),
    families_cons (context_families_head families)
      (context_families_tail families) = families.
Proof. intros; exact (context_families_eta_general families). Qed.

Definition context_family_eta_general {d q} {run : SRun d q}
    (family : SContextFamily run) :
    match run as indexed return SContextFamily indexed -> Prop with
    | srun_leaf _ => fun current =>
        family_leaf (context_family_context current) = current
    | srun_node _ _ _ => fun current =>
        family_node (context_family_context current)
          (context_family_children current) (context_family_matched current) =
        current
    end family :=
  match family with
  | family_leaf _ => eq_refl
  | family_node _ _ _ => eq_refl
  end.

Lemma context_family_leaf_eta : forall d q config
    (family : SContextFamily (@srun_leaf d q config)),
    family_leaf (context_family_context family) = family.
Proof. intros; exact (context_family_eta_general family). Qed.

Lemma context_family_node_eta : forall d q rule children result
    (family : SContextFamily (@srun_node d q rule children result)),
    family_node (context_family_context family)
      (context_family_children family) (context_family_matched family) = family.
Proof. intros; exact (context_family_eta_general family). Qed.

Record ContextFamiliesSplit {d q} (before : SRuns d q)
    (focus : SRun d q) (after : SRuns d q)
    (families : SContextFamilies
      (sruns_append before (sruns_cons focus after))) : Type := {
  split_before_families : SContextFamilies before;
  split_focus_family : SContextFamily focus;
  split_after_families : SContextFamilies after;
  split_families_insert :
    insert_context_families families =
      sruns_append (insert_context_families split_before_families)
        (sruns_cons (insert_context_family split_focus_family)
          (insert_context_families split_after_families))
}.

Arguments split_before_families {d q before focus after families} _.
Arguments split_focus_family {d q before focus after families} _.
Arguments split_after_families {d q before focus after families} _.
Arguments split_families_insert {d q before focus after families} _.

Fixpoint split_context_families {d q} (before : SRuns d q) :
    forall (focus : SRun d q) (after : SRuns d q)
      (families : SContextFamilies
        (sruns_append before (sruns_cons focus after))),
      ContextFamiliesSplit before focus after families.
Proof.
  destruct before as [|head tail].
  - intros focus after families.
    refine {| split_before_families := families_nil;
      split_focus_family := context_families_head families;
      split_after_families := context_families_tail families |}.
    symmetry. exact (f_equal (@insert_context_families d q _)
      (context_families_eta d q focus after families)).
  - intros focus after families.
    pose (parts := @split_context_families d q tail focus after
      (context_families_tail families)).
    refine {| split_before_families :=
        families_cons (context_families_head families)
          (split_before_families parts);
      split_focus_family := split_focus_family parts;
      split_after_families := split_after_families parts |}.
    transitivity (sruns_cons
      (insert_context_family (context_families_head families))
      (insert_context_families (context_families_tail families))).
    + symmetry. exact (f_equal (@insert_context_families d q _)
        (context_families_eta d q head
          (sruns_append tail (sruns_cons focus after)) families)).
    + cbn. f_equal. exact (split_families_insert parts).
Defined.

Fixpoint decompose_family_through_context {d q}
    (context : SContext d q) (core : SRun d q) :
    SContextFamily (scontext_plug context core) ->
    { outer : SContext d q & SContextFamily core } :=
  match context as current return
    SContextFamily (scontext_plug current core) ->
    { outer : SContext d q & SContextFamily core } with
  | scontext_hole => fun family => existT _ scontext_hole family
  | scontext_node rule before inner after result => fun family =>
      let outer := context_family_context family in
      let families := context_family_children family in
      let matched := context_family_matched family in
      let parts := split_context_families before
        (scontext_plug inner core) after families in
      let before_families := split_before_families parts in
      let inner_family := split_focus_family parts in
      let after_families := split_after_families parts in
      let decomposition :=
        decompose_family_through_context inner core inner_family in
      existT _
        (scontext_compose outer
          (scontext_node rule
            (insert_context_families before_families)
            (projT1 decomposition)
            (insert_context_families after_families) matched))
        (projT2 decomposition)
  end.

Fixpoint compose_context_family {d q} {run : SRun d q}
    (first : SContextFamily run) :
    SContextFamily (insert_context_family first) -> SContextFamily run :=
  match first as current in SContextFamily indexed return
    SContextFamily (insert_context_family current) ->
      SContextFamily indexed with
  | @family_leaf _ _ config context => fun second =>
      let decomposition :=
        decompose_family_through_context context (srun_leaf config) second in
      family_leaf
        (scontext_compose (projT1 decomposition)
          (context_family_context (projT2 decomposition)))
  | @family_node _ _ rule children result context families matched =>
      fun second =>
      let decomposition := decompose_family_through_context context
        (srun_node rule (insert_context_families families) matched) second in
      family_node
        (scontext_compose (projT1 decomposition)
          (context_family_context (projT2 decomposition)))
        (compose_context_families families
          (context_family_children (projT2 decomposition)))
        (context_family_matched (projT2 decomposition))
  end
with compose_context_families {d q} {runs : SRuns d q}
    (first : SContextFamilies runs) :
    SContextFamilies (insert_context_families first) ->
      SContextFamilies runs :=
  match first as current in SContextFamilies indexed return
    SContextFamilies (insert_context_families current) ->
      SContextFamilies indexed with
  | families_nil => fun _ => families_nil
  | families_cons head tail => fun second =>
      families_cons
        (compose_context_family head (context_families_head second))
        (compose_context_families tail (context_families_tail second))
  end.

Lemma decompose_family_through_context_insert : forall d q
    (context : SContext d q) core
    (family : SContextFamily (scontext_plug context core)),
    insert_context_family family =
      scontext_plug
        (projT1 (decompose_family_through_context context core family))
        (insert_context_family
          (projT2 (decompose_family_through_context context core family))).
Proof.
  intros d q context. induction context as
    [|rule before inner IH after result]; intros core family; cbn.
  - reflexivity.
  - cbn.
    pose (parts := split_context_families before
      (scontext_plug inner core) after (context_family_children family)).
    set (before_families := split_before_families parts).
    set (inner_family := split_focus_family parts).
    set (after_families := split_after_families parts).
    cbn [decompose_family_through_context].
    transitivity (scontext_plug (context_family_context family)
      (srun_node rule
        (insert_context_families (context_family_children family))
        (context_family_matched family))).
    + symmetry. exact (f_equal (@insert_context_family d q _)
        (context_family_node_eta d q rule
          (sruns_append before
            (sruns_cons (scontext_plug inner core) after)) result family)).
    + rewrite scontext_plug_compose. cbn.
      f_equal.
      f_equal.
      transitivity (sruns_append
        (insert_context_families (split_before_families parts))
        (sruns_cons
          (insert_context_family (split_focus_family parts))
          (insert_context_families (split_after_families parts)))).
      * exact (split_families_insert parts).
      * f_equal. f_equal.
      pose proof (IH core inner_family) as Hinner.
      unfold inner_family in Hinner. exact Hinner.
Qed.

Lemma compose_context_family_insert_mut : forall d q,
  (forall (run : SRun d q) (first : SContextFamily run)
      (second : SContextFamily (insert_context_family first)),
    insert_context_family (compose_context_family first second) =
      insert_context_family second) /\
  (forall (runs : SRuns d q) (first : SContextFamilies runs)
      (second : SContextFamilies (insert_context_families first)),
    insert_context_families (compose_context_families first second) =
      insert_context_families second).
Proof.
  intros d q. apply SContextFamily_SContextFamilies_ind.
  - intros config context second. cbn.
    rewrite scontext_plug_compose.
    transitivity (scontext_plug
      (projT1 (decompose_family_through_context context
        (srun_leaf config) second))
      (insert_context_family
        (projT2 (decompose_family_through_context context
          (srun_leaf config) second)))).
    + f_equal.
      pose proof (context_family_leaf_eta d q config
        (projT2 (decompose_family_through_context context
          (srun_leaf config) second))) as Heta.
      exact (f_equal (@insert_context_family d q _) Heta).
    + symmetry. apply decompose_family_through_context_insert.
  - intros rule children result context families IH matched second. cbn.
    rewrite scontext_plug_compose. cbn. rewrite IH.
    transitivity (scontext_plug
      (projT1 (decompose_family_through_context context
        (srun_node rule (insert_context_families families) matched) second))
      (insert_context_family
        (projT2 (decompose_family_through_context context
          (srun_node rule (insert_context_families families) matched) second)))).
    + f_equal.
      pose proof (context_family_node_eta d q rule
        (insert_context_families families) matched
        (projT2 (decompose_family_through_context context
          (srun_node rule (insert_context_families families) matched)
          second))) as Heta.
      exact (f_equal (@insert_context_family d q _) Heta).
    + symmetry. apply decompose_family_through_context_insert.
  - intros second. exact (eq_sym
      (f_equal (@insert_context_families d q _)
        (context_families_eta_general second))).
  - intros run runs family IHfamily families IHfamilies second. cbn.
    rewrite IHfamily, IHfamilies.
    exact (f_equal (@insert_context_families d q _)
      (context_families_eta d q (insert_context_family family)
        (insert_context_families families) second)).
Qed.

Theorem compose_context_family_insert : forall d q (run : SRun d q)
    (first : SContextFamily run)
    (second : SContextFamily (insert_context_family first)),
    insert_context_family (compose_context_family first second) =
      insert_context_family second.
Proof. intros; apply (proj1 (compose_context_family_insert_mut d q)). Qed.

Inductive CompatibleContextFamily {d q : nat} :
    forall run : SRun d q, @SContextFamily d q run -> Prop :=
| compatible_family_leaf : forall config context,
    ContextCompatible context (srun_leaf config) ->
    CompatibleContextFamily (srun_leaf config) (family_leaf context)
| compatible_family_node : forall rule children result context families matched,
    CompatibleContextFamilies children families ->
    fst matched = fst result ->
    ContextCompatible context
      (srun_node rule (insert_context_families families) matched) ->
    CompatibleContextFamily (srun_node rule children result)
      (family_node context families matched)
with CompatibleContextFamilies {d q : nat} :
    forall runs : SRuns d q, @SContextFamilies d q runs -> Prop :=
| compatible_families_nil :
    CompatibleContextFamilies sruns_nil families_nil
| compatible_families_cons : forall run runs family families,
    CompatibleContextFamily run family ->
    CompatibleContextFamilies runs families ->
    CompatibleContextFamilies (sruns_cons run runs)
      (families_cons family families).

Inductive HereditarilyPositive {d q : nat} :
    forall run : SRun d q, @SContextFamily d q run -> Prop :=
| positive_family_leaf : forall config context,
    RootConfigLe config
      (root_config (insert_context_family (@family_leaf d q config context))) ->
    HereditarilyPositive (srun_leaf config) (@family_leaf d q config context)
| positive_family_node : forall rule children result context families matched,
    HereditarilyPositiveFamilies children families ->
    RootConfigLe result
      (root_config (insert_context_family
        (@family_node d q rule children result context families matched))) ->
    HereditarilyPositive (srun_node rule children result)
      (@family_node d q rule children result context families matched)
with HereditarilyPositiveFamilies {d q : nat} :
    forall runs : SRuns d q, @SContextFamilies d q runs -> Prop :=
| positive_families_nil :
    HereditarilyPositiveFamilies sruns_nil families_nil
| positive_families_cons : forall run runs family families,
    HereditarilyPositive run family ->
    HereditarilyPositiveFamilies runs families ->
    HereditarilyPositiveFamilies (sruns_cons run runs)
      (families_cons family families).

Inductive CompatibleProper {d q : nat} :
    forall run : SRun d q, @SContextFamily d q run -> Prop :=
| compatible_proper_leaf : forall config context,
    CompatibleProper (srun_leaf config) (family_leaf context)
| compatible_proper_node : forall rule children result context families matched,
    CompatibleContextFamilies children families ->
    fst matched = fst result ->
    CompatibleProper (srun_node rule children result)
      (family_node context families matched).

Inductive PositiveProper {d q : nat} :
    forall run : SRun d q, @SContextFamily d q run -> Prop :=
| positive_proper_leaf : forall config context,
    PositiveProper (srun_leaf config) (family_leaf context)
| positive_proper_node : forall rule children result context families matched,
    HereditarilyPositiveFamilies children families ->
    PositiveProper (srun_node rule children result)
      (family_node context families matched).

Definition compatible_families_head_general {d q} {runs : SRuns d q}
    {families : SContextFamilies runs}
    (proof : CompatibleContextFamilies runs families) :
    match runs as indexed return SContextFamilies indexed -> Prop with
    | sruns_nil => fun _ => True
    | sruns_cons run _ => fun current =>
        CompatibleContextFamily run (context_families_head current)
    end families :=
  match proof with
  | @compatible_families_nil _ _ => I
  | @compatible_families_cons _ _ _ _ _ _ head _ => head
  end.

Definition compatible_families_tail_general {d q} {runs : SRuns d q}
    {families : SContextFamilies runs}
    (proof : CompatibleContextFamilies runs families) :
    match runs as indexed return SContextFamilies indexed -> Prop with
    | sruns_nil => fun _ => True
    | sruns_cons _ tail => fun current =>
        CompatibleContextFamilies tail (context_families_tail current)
    end families :=
  match proof with
  | @compatible_families_nil _ _ => I
  | @compatible_families_cons _ _ _ _ _ _ _ tail => tail
  end.

Definition positive_families_head_general {d q} {runs : SRuns d q}
    {families : SContextFamilies runs}
    (proof : HereditarilyPositiveFamilies runs families) :
    match runs as indexed return SContextFamilies indexed -> Prop with
    | sruns_nil => fun _ => True
    | sruns_cons run _ => fun current =>
        HereditarilyPositive run (context_families_head current)
    end families :=
  match proof with
  | @positive_families_nil _ _ => I
  | @positive_families_cons _ _ _ _ _ _ head _ => head
  end.

Definition positive_families_tail_general {d q} {runs : SRuns d q}
    {families : SContextFamilies runs}
    (proof : HereditarilyPositiveFamilies runs families) :
    match runs as indexed return SContextFamilies indexed -> Prop with
    | sruns_nil => fun _ => True
    | sruns_cons _ tail => fun current =>
        HereditarilyPositiveFamilies tail (context_families_tail current)
    end families :=
  match proof with
  | @positive_families_nil _ _ => I
  | @positive_families_cons _ _ _ _ _ _ _ tail => tail
  end.

Definition compatible_family_children_general {d q} {run : SRun d q}
    {family : SContextFamily run}
    (proof : CompatibleContextFamily run family) :
    match run as indexed return SContextFamily indexed -> Prop with
    | srun_leaf _ => fun _ => True
    | srun_node _ children _ => fun current =>
        CompatibleContextFamilies children (context_family_children current)
    end family :=
  match proof as witness in CompatibleContextFamily indexed current return
    match indexed as run' return SContextFamily run' -> Prop with
    | srun_leaf _ => fun _ => True
    | srun_node _ children _ => fun current' =>
        CompatibleContextFamilies children
          (context_family_children current')
    end current with
  | @compatible_family_leaf _ _ _ _ _ => I
  | @compatible_family_node _ _ _ _ _ _ _ _ children _ _ => children
  end.

Definition compatible_family_matched_state_general {d q}
    {run : SRun d q} {family : SContextFamily run}
    (proof : CompatibleContextFamily run family) :
    match run as indexed return SContextFamily indexed -> Prop with
    | srun_leaf _ => fun _ => True
    | srun_node _ _ result => fun current =>
        fst (context_family_matched current) = fst result
    end family :=
  match proof as witness in CompatibleContextFamily indexed current return
    match indexed as run' return SContextFamily run' -> Prop with
    | srun_leaf _ => fun _ => True
    | srun_node _ _ result => fun current' =>
        fst (context_family_matched current') = fst result
    end current with
  | @compatible_family_leaf _ _ _ _ _ => I
  | @compatible_family_node _ _ _ _ _ _ _ _ _ state _ => state
  end.

Definition compatible_family_local_general {d q} {run : SRun d q}
    {family : SContextFamily run}
    (proof : CompatibleContextFamily run family) :
    match run as indexed return SContextFamily indexed -> Prop with
    | srun_leaf config => fun current =>
        ContextCompatible (context_family_context current)
          (srun_leaf config)
    | srun_node rule _ _ => fun current =>
        ContextCompatible (context_family_context current)
          (srun_node rule
            (insert_context_families (context_family_children current))
            (context_family_matched current))
    end family :=
  match proof as witness in CompatibleContextFamily indexed current return
    match indexed as run' return SContextFamily run' -> Prop with
    | srun_leaf config => fun current' =>
        ContextCompatible (context_family_context current')
          (srun_leaf config)
    | srun_node rule _ _ => fun current' =>
        ContextCompatible (context_family_context current')
          (srun_node rule
            (insert_context_families (context_family_children current'))
            (context_family_matched current'))
    end current with
  | @compatible_family_leaf _ _ _ _ local => local
  | @compatible_family_node _ _ _ _ _ _ _ _ _ _ local => local
  end.

Definition positive_family_children_general {d q} {run : SRun d q}
    {family : SContextFamily run}
    (proof : HereditarilyPositive run family) :
    match run as indexed return SContextFamily indexed -> Prop with
    | srun_leaf _ => fun _ => True
    | srun_node _ children _ => fun current =>
        HereditarilyPositiveFamilies children
          (context_family_children current)
    end family :=
  match proof as witness in HereditarilyPositive indexed current return
    match indexed as run' return SContextFamily run' -> Prop with
    | srun_leaf _ => fun _ => True
    | srun_node _ children _ => fun current' =>
        HereditarilyPositiveFamilies children
          (context_family_children current')
    end current with
  | @positive_family_leaf _ _ _ _ _ => I
  | @positive_family_node _ _ _ _ _ _ _ _ children _ => children
  end.

Lemma compatible_families_head : forall (d q : nat) (run : SRun d q)
    (runs : SRuns d q)
    (families : SContextFamilies (sruns_cons run runs)),
    CompatibleContextFamilies (sruns_cons run runs) families ->
    CompatibleContextFamily run (context_families_head families).
Proof.
  intros; exact (compatible_families_head_general H).
Qed.

Lemma compatible_families_tail : forall (d q : nat) (run : SRun d q)
    (runs : SRuns d q)
    (families : SContextFamilies (sruns_cons run runs)),
    CompatibleContextFamilies (sruns_cons run runs) families ->
    CompatibleContextFamilies runs (context_families_tail families).
Proof.
  intros; exact (compatible_families_tail_general H).
Qed.

Lemma positive_families_head : forall (d q : nat) (run : SRun d q)
    (runs : SRuns d q)
    (families : SContextFamilies (sruns_cons run runs)),
    HereditarilyPositiveFamilies (sruns_cons run runs) families ->
    HereditarilyPositive run (context_families_head families).
Proof.
  intros; exact (positive_families_head_general H).
Qed.

Lemma positive_families_tail : forall (d q : nat) (run : SRun d q)
    (runs : SRuns d q)
    (families : SContextFamilies (sruns_cons run runs)),
    HereditarilyPositiveFamilies (sruns_cons run runs) families ->
    HereditarilyPositiveFamilies runs (context_families_tail families).
Proof.
  intros; exact (positive_families_tail_general H).
Qed.

Lemma split_focus_compatible : forall d q (before : SRuns d q) focus after
    (families : SContextFamilies
      (sruns_append before (sruns_cons focus after))),
    CompatibleContextFamilies
      (sruns_append before (sruns_cons focus after)) families ->
    CompatibleContextFamily focus
      (split_focus_family (split_context_families before focus after families)).
Proof.
  intros d q before. induction before as [|head tail IH];
    intros focus after families Hcompatible; cbn.
  - exact (compatible_families_head d q focus after families Hcompatible).
  - apply IH. exact (compatible_families_tail d q head _ families Hcompatible).
Qed.

Lemma split_focus_positive : forall d q (before : SRuns d q) focus after
    (families : SContextFamilies
      (sruns_append before (sruns_cons focus after))),
    HereditarilyPositiveFamilies
      (sruns_append before (sruns_cons focus after)) families ->
    HereditarilyPositive focus
      (split_focus_family (split_context_families before focus after families)).
Proof.
  intros d q before. induction before as [|head tail IH];
    intros focus after families Hpositive; cbn.
  - exact (positive_families_head d q focus after families Hpositive).
  - apply IH. exact (positive_families_tail d q head _ families Hpositive).
Qed.

Lemma decompose_family_compatible_core : forall d q
    (context : SContext d q) core
    (family : SContextFamily (scontext_plug context core)),
    CompatibleContextFamily (scontext_plug context core) family ->
    CompatibleContextFamily core
      (projT2 (decompose_family_through_context context core family)).
Proof.
  intros d q context. induction context as
    [|rule before inner IH after result]; intros core family Hcompatible; cbn.
  - exact Hcompatible.
  - apply IH. eapply split_focus_compatible.
    exact (compatible_family_children_general Hcompatible).
Qed.

Lemma decompose_family_positive_core : forall d q
    (context : SContext d q) core
    (family : SContextFamily (scontext_plug context core)),
    HereditarilyPositive (scontext_plug context core) family ->
    HereditarilyPositive core
      (projT2 (decompose_family_through_context context core family)).
Proof.
  intros d q context. induction context as
    [|rule before inner IH after result]; intros core family Hpositive; cbn.
  - exact Hpositive.
  - apply IH. eapply split_focus_positive.
    exact (positive_family_children_general Hpositive).
Qed.

Definition family_root_compatible {d q} {run : SRun d q}
    (family : SContextFamily run) : Prop :=
  fst (root_config (insert_context_family family)) = fst (root_config run).

Lemma compatible_from_proper : forall d q (run : SRun d q)
    (family : SContextFamily run),
    CompatibleProper run family -> family_root_compatible family ->
    CompatibleContextFamily run family.
Proof.
  intros d q run family Hproper. destruct Hproper.
  - intro Hroot. constructor. exact Hroot.
  - intro Hroot. constructor.
    + exact H.
    + exact H0.
    + unfold ContextCompatible, family_root_compatible in *. cbn in *.
      now rewrite Hroot, H0.
Qed.

Lemma positive_from_proper : forall d q (run : SRun d q)
    (family : SContextFamily run),
    PositiveProper run family ->
    RootConfigLe (root_config run)
      (root_config (insert_context_family family)) ->
    HereditarilyPositive run family.
Proof.
  intros d q run family Hproper Hroot. destruct Hproper; constructor;
    assumption.
Qed.

Definition wrap_family_context {d q} {run : SRun d q}
    (outer : SContext d q) (family : SContextFamily run) : SContextFamily run :=
  match family with
  | family_leaf inner => family_leaf (scontext_compose outer inner)
  | @family_node _ _ rule children result inner families matched =>
      @family_node d q rule children result
        (scontext_compose outer inner) families matched
  end.

Lemma insert_wrap_family_context : forall d q (run : SRun d q)
    (outer : SContext d q) (family : SContextFamily run),
    insert_context_family (wrap_family_context outer family) =
    scontext_plug outer (insert_context_family family).
Proof.
  intros d q run outer family.
  destruct family as [config context|rule children result context families matched].
  - change (scontext_plug (scontext_compose outer context) (srun_leaf config) =
      scontext_plug outer (scontext_plug context (srun_leaf config))).
    apply scontext_plug_compose.
  - change (scontext_plug (scontext_compose outer context)
      (srun_node rule (insert_context_families families) matched) =
      scontext_plug outer (scontext_plug context
        (srun_node rule (insert_context_families families) matched))).
    apply scontext_plug_compose.
Qed.

Lemma wrap_family_compatible_proper : forall d q (run : SRun d q)
    (outer : SContext d q) (family : SContextFamily run),
    CompatibleProper run family ->
    CompatibleProper run (wrap_family_context outer family).
Proof. intros d q run outer family H; destruct H; constructor; assumption. Qed.

Lemma wrap_family_positive_proper : forall d q (run : SRun d q)
    (outer : SContext d q) (family : SContextFamily run),
    PositiveProper run family ->
    PositiveProper run (wrap_family_context outer family).
Proof. intros d q run outer family H; destruct H; constructor; assumption. Qed.

Lemma valid_sruns_append_focus : forall d q (S : SBVAS d q)
    before (focus : SRun d q) after,
    ValidSRuns S (sruns_append before (sruns_cons focus after)) ->
    ValidSRun S focus.
Proof.
  intros d q S before. induction before; intros focus after Hvalid; cbn in Hvalid.
  - inversion Hvalid; subst; assumption.
  - inversion Hvalid; subst. eapply IHbefore; eauto.
Qed.

Lemma valid_scontext_plug_core : forall d q (S : SBVAS d q)
    (context : SContext d q) run,
    ValidSRun S (scontext_plug context run) -> ValidSRun S run.
Proof.
  intros d q S context. induction context; intros run Hvalid; cbn in Hvalid.
  - exact Hvalid.
  - inversion Hvalid; subst.
    apply IHcontext. eapply valid_sruns_append_focus; eauto.
Qed.

Lemma valid_srun_node_counter_equation : forall d q (S : SBVAS d q)
    rule children result,
    ValidSRun S (srun_node rule children result) ->
    forall index,
      (Vector.nth (rule_delta rule) index +
       Z.of_nat (Vector.nth
         (nvec_sum (List.map snd (sruns_configs children))) index) =
       Z.of_nat (Vector.nth (snd result) index))%Z.
Proof.
  intros d q S rule children result Hvalid index.
  inversion Hvalid; subst.
  match goal with
  | Happly : add_displacement _ _ = Some _ |- _ =>
      pose proof (zvec_to_nvec_sound d _ _ Happly index) as Heq
  end.
  unfold zvec_add, nvec_to_zvec in Heq.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (nth_map Z.of_nat _ index index eq_refl) in Heq.
  exact Heq.
Qed.

Lemma nvec_sum_cons_context : forall d (head : NVec d) tail,
    nvec_sum (head :: tail) = nvec_add head (nvec_sum tail).
Proof.
  intros d head tail. repeat rewrite nvec_sum_rsum. reflexivity.
Qed.

Lemma context_family_effect_scalar_mut : forall d q (S : SBVAS d q),
  (forall (run : SRun d q) (family : SContextFamily run),
    ValidSRun S run -> ValidSRun S (insert_context_family family) ->
    forall index,
      Vector.nth (context_family_effect family) index =
      (Z.of_nat (Vector.nth
        (snd (root_config (insert_context_family family))) index) -
       Z.of_nat (Vector.nth (snd (root_config run)) index))%Z) /\
  (forall (runs : SRuns d q) (families : SContextFamilies runs),
    ValidSRuns S runs -> ValidSRuns S (insert_context_families families) ->
    forall index,
      Vector.nth (context_families_effect families) index =
      (Z.of_nat (Vector.nth
        (nvec_sum (List.map snd
          (sruns_configs (insert_context_families families)))) index) -
       Z.of_nat (Vector.nth
        (nvec_sum (List.map snd (sruns_configs runs))) index))%Z).
Proof.
  intros d q S. apply SContextFamily_SContextFamilies_ind.
  - intros config context Hvalid Hinsert index. cbn.
    unfold scontext_effect, signed_counter_effect, nvec_to_zvec.
    rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl).
    repeat rewrite (nth_map Z.of_nat _ index index eq_refl). reflexivity.
  - intros rule children result context families IH matched
      Hvalid Hinsert index. cbn.
    assert (Hcore : ValidSRun S
      (srun_node rule (insert_context_families families) matched)).
    { eapply valid_scontext_plug_core; eauto. }
    assert (Hold := valid_srun_node_counter_equation d q S
      rule children result Hvalid index).
    assert (Hnew := valid_srun_node_counter_equation d q S
      rule (insert_context_families families) matched Hcore index).
    assert (Hchildren_old : ValidSRuns S children).
    { inversion Hvalid; subst; assumption. }
    assert (Hchildren_new :
      ValidSRuns S (insert_context_families families)).
    { inversion Hcore; subst; assumption. }
    specialize (IH Hchildren_old Hchildren_new index).
    unfold scontext_effect, signed_counter_effect, zvec_add, nvec_to_zvec.
    rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
      (nth_map2 Z.sub _ _ index index index eq_refl eq_refl).
    repeat rewrite (nth_map Z.of_nat _ index index eq_refl).
    cbn in IH |- *. lia.
  - intros Hvalid Hinsert index. cbn.
    unfold zvec_zero, nvec_sum.
    rewrite (const_nth Z 0%Z d index). cbn.
    lia.
  - intros run runs family IHfamily families IHfamilies
      Hvalid Hinsert index.
    cbn [context_families_effect insert_context_families sruns_configs].
    inversion Hvalid; subst. inversion Hinsert; subst.
    match goal with
    | Hrun : ValidSRun S run,
      Hruns : ValidSRuns S runs,
      Hnewrun : ValidSRun S (insert_context_family family),
      Hnewruns : ValidSRuns S (insert_context_families families) |- _ =>
        specialize (IHfamily Hrun Hnewrun index);
        specialize (IHfamilies Hruns Hnewruns index)
    end.
    unfold zvec_add.
    rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl).
    cbn [List.map].
    repeat rewrite nvec_sum_cons_context.
    unfold nvec_add.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
    repeat rewrite Nat2Z.inj_add.
    lia.
Qed.

Theorem context_family_effect_exact : forall d q (S : SBVAS d q)
    (run : SRun d q) (family : SContextFamily run),
    ValidSRun S run -> ValidSRun S (insert_context_family family) ->
    nvec_to_zvec (snd (root_config (insert_context_family family))) =
    zvec_add (nvec_to_zvec (snd (root_config run)))
      (context_family_effect family).
Proof.
  intros d q S run family Hvalid Hinsert.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  pose proof (proj1 (context_family_effect_scalar_mut d q S)
    run family Hvalid Hinsert index) as Heffect.
  unfold zvec_add, nvec_to_zvec.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl).
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl). lia.
Qed.

Definition ContextOrder {d q} (S : SBVAS d q)
    (left right : SRun d q) : Prop :=
  ValidSRun S left /\ ValidSRun S right /\
  exists family : SContextFamily left,
    CompatibleContextFamily left family /\
    HereditarilyPositive left family /\
    SRunIsomorphic (insert_context_family family) right.

Lemma srun_isomorphic_refl_mut : forall d q,
  (forall run : SRun d q, SRunIsomorphic run run) /\
  (forall runs : SRuns d q, SRunsIsomorphic runs runs).
Proof.
  intros d q. apply SRun_SRuns_ind.
  - intros config. constructor.
  - intros rule children IH result. constructor. exact IH.
  - constructor.
  - intros run IHrun runs IHruns.
    eapply sruns_iso_cons with (right := run) (remainder := runs).
    + constructor.
    + exact IHrun.
    + exact IHruns.
Qed.

Fixpoint identity_context_family {d q} (run : SRun d q) :
    SContextFamily run :=
  match run with
  | srun_leaf config => @family_leaf d q config scontext_hole
  | srun_node rule children result =>
      @family_node d q rule children result scontext_hole
        (identity_context_families children) result
  end
with identity_context_families {d q} (runs : SRuns d q) :
    SContextFamilies runs :=
  match runs with
  | sruns_nil => families_nil
  | sruns_cons run tail =>
      families_cons (identity_context_family run)
        (identity_context_families tail)
  end.

Lemma insert_identity_context_family_mut : forall d q,
  (forall run : SRun d q,
    insert_context_family (identity_context_family run) = run) /\
  (forall runs : SRuns d q,
    insert_context_families (identity_context_families runs) = runs).
Proof.
  intros d q. apply SRun_SRuns_ind; cbn; intros; try reflexivity.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Lemma identity_context_family_compatible_mut : forall d q,
  (forall run : SRun d q,
    CompatibleContextFamily run (identity_context_family run)) /\
  (forall runs : SRuns d q,
    CompatibleContextFamilies runs (identity_context_families runs)).
Proof.
  intros d q. apply SRun_SRuns_ind; cbn.
  - intros config. constructor. reflexivity.
  - intros rule children IH result. constructor.
    + exact IH.
    + reflexivity.
    + cbn. now rewrite
        (proj2 (insert_identity_context_family_mut d q) children).
  - constructor.
  - intros run IHrun runs IHruns. constructor; assumption.
Qed.

Lemma root_config_le_refl : forall d q (config : SConfig d q),
    RootConfigLe config config.
Proof. intros d q [state counters]. split; [reflexivity|apply nvec_le_refl]. Qed.

Lemma identity_context_family_positive_mut : forall d q,
  (forall run : SRun d q,
    HereditarilyPositive run (identity_context_family run)) /\
  (forall runs : SRuns d q,
    HereditarilyPositiveFamilies runs (identity_context_families runs)).
Proof.
  intros d q. apply SRun_SRuns_ind; cbn.
  - intros config. constructor. apply root_config_le_refl.
  - intros rule children IH result. constructor; [exact IH|].
    apply root_config_le_refl.
  - constructor.
  - intros run IHrun runs IHruns. constructor; assumption.
Qed.

Theorem context_order_of_isomorphism : forall d q (S : SBVAS d q) left right,
    ValidSRun S left -> ValidSRun S right ->
    SRunIsomorphic left right -> ContextOrder S left right.
Proof.
  intros d q S left right Hleft Hright Hiso.
  split; [exact Hleft|]. split; [exact Hright|].
  exists (identity_context_family left). repeat split.
  - apply (proj1 (identity_context_family_compatible_mut d q)).
  - apply (proj1 (identity_context_family_positive_mut d q)).
  - rewrite (proj1 (insert_identity_context_family_mut d q) left). exact Hiso.
Qed.

Theorem context_order_refl : forall d q (S : SBVAS d q) run,
    ValidSRun S run -> ContextOrder S run run.
Proof.
  intros. apply context_order_of_isomorphism; try assumption.
  apply (proj1 (srun_isomorphic_refl_mut d q)).
Qed.

Lemma srun_isomorphic_root : forall d q (left right : SRun d q),
    SRunIsomorphic left right -> root_config left = root_config right.
Proof. intros d q left right H; inversion H; reflexivity. Qed.

Lemma compatible_context_family_root : forall d q (run : SRun d q)
    (family : SContextFamily run),
    CompatibleContextFamily run family ->
    fst (root_config (insert_context_family family)) = fst (root_config run).
Proof.
  intros d q run family H. case H.
  - intros config context Hcompatible. exact Hcompatible.
  - intros rule children result context families matched Hfamilies Hstate
      Hcompatible.
    unfold ContextCompatible in Hcompatible. cbn in Hcompatible |- *.
    now rewrite Hcompatible, Hstate.
Qed.

Definition positive_context_family_root_general {d q} {run : SRun d q}
    {family : SContextFamily run}
    (proof : HereditarilyPositive run family) :
    RootConfigLe (root_config run)
      (root_config (insert_context_family family)) :=
  match proof as witness in HereditarilyPositive indexed current return
    RootConfigLe (root_config indexed)
      (root_config (insert_context_family current)) with
  | positive_family_leaf _ _ root_positive => root_positive
  | positive_family_node _ _ _ _ _ _ _ root_positive => root_positive
  end.

Theorem hereditary_positive_effect_nonnegative : forall d q
    (S : SBVAS d q) (run : SRun d q) (family : SContextFamily run),
    ValidSRun S run -> ValidSRun S (insert_context_family family) ->
    HereditarilyPositive run family ->
    forall index, (0 <= Vector.nth (context_family_effect family) index)%Z.
Proof.
  intros d q S run family Hvalid Hinsert Hpositive index.
  pose proof (proj1 (context_family_effect_scalar_mut d q S)
    run family Hvalid Hinsert index) as Heffect.
  pose proof (positive_context_family_root_general Hpositive) as [_ Hle].
  specialize (Hle index). lia.
Qed.

Lemma root_config_le_trans : forall d q (first second third : SConfig d q),
    RootConfigLe first second -> RootConfigLe second third ->
    RootConfigLe first third.
Proof.
  intros d q [first_state first_counters]
    [second_state second_counters] [third_state third_counters].
  intros [Hfirst Hleft] [Hsecond Hright]. cbn in *.
  split; [now transitivity second_state|]. intro index. specialize (Hleft index).
  specialize (Hright index). exact (Nat.le_trans _ _ _ Hleft Hright).
Qed.

Lemma compose_family_root_compatible : forall d q (run : SRun d q)
    (first : SContextFamily run)
    (second : SContextFamily (insert_context_family first)),
    CompatibleContextFamily run first ->
    CompatibleContextFamily (insert_context_family first) second ->
    family_root_compatible (compose_context_family first second).
Proof.
  intros d q run first second Hfirst Hsecond.
  unfold family_root_compatible.
  rewrite compose_context_family_insert.
  transitivity (fst (root_config (insert_context_family first))).
  - apply compatible_context_family_root. exact Hsecond.
  - apply compatible_context_family_root. exact Hfirst.
Qed.

Lemma compose_family_root_positive : forall d q (run : SRun d q)
    (first : SContextFamily run)
    (second : SContextFamily (insert_context_family first)),
    HereditarilyPositive run first ->
    HereditarilyPositive (insert_context_family first) second ->
    RootConfigLe (root_config run)
      (root_config (insert_context_family
        (compose_context_family first second))).
Proof.
  intros d q run first second Hfirst Hsecond.
  rewrite compose_context_family_insert.
  eapply root_config_le_trans.
  - exact (positive_context_family_root_general Hfirst).
  - exact (positive_context_family_root_general Hsecond).
Qed.

Lemma compose_context_family_compatible_mut : forall d q,
  (forall (run : SRun d q) (first : SContextFamily run),
    CompatibleContextFamily run first ->
    forall second : SContextFamily (insert_context_family first),
      CompatibleContextFamily (insert_context_family first) second ->
      CompatibleContextFamily run (compose_context_family first second)) /\
  (forall (runs : SRuns d q) (first : SContextFamilies runs),
    CompatibleContextFamilies runs first ->
    forall second : SContextFamilies (insert_context_families first),
      CompatibleContextFamilies (insert_context_families first) second ->
      CompatibleContextFamilies runs (compose_context_families first second)).
Proof.
  intros d q. apply SContextFamily_SContextFamilies_ind.
  - intros config context Hfirst second Hsecond.
    apply compatible_from_proper; [constructor|].
    eapply compose_family_root_compatible; eauto.
  - intros rule children result context families IH matched Hfirst second Hsecond.
    set (core := srun_node rule (insert_context_families families) matched).
    set (core_family := projT2
      (decompose_family_through_context context core second)).
    assert (Hcore : CompatibleContextFamily core core_family).
    { unfold core_family. apply decompose_family_compatible_core. exact Hsecond. }
    apply compatible_from_proper.
    + constructor.
      * apply IH.
        -- exact (compatible_family_children_general Hfirst).
        -- exact (compatible_family_children_general Hcore).
      * transitivity (fst matched).
        -- exact (compatible_family_matched_state_general Hcore).
        -- exact (compatible_family_matched_state_general Hfirst).
    + eapply compose_family_root_compatible; eauto.
  - intros Hfirst second Hsecond. constructor.
  - intros run runs family IHfamily families IHfamilies Hfirst second Hsecond.
    constructor.
    + apply IHfamily.
      * exact (compatible_families_head d q run runs
          (families_cons family families) Hfirst).
      * exact (compatible_families_head d q
          (insert_context_family family) (insert_context_families families)
          second Hsecond).
    + apply IHfamilies.
      * exact (compatible_families_tail d q run runs
          (families_cons family families) Hfirst).
      * exact (compatible_families_tail d q
          (insert_context_family family) (insert_context_families families)
          second Hsecond).
Qed.

Lemma compose_context_family_positive_mut : forall d q,
  (forall (run : SRun d q) (first : SContextFamily run),
    HereditarilyPositive run first ->
    forall second : SContextFamily (insert_context_family first),
      HereditarilyPositive (insert_context_family first) second ->
      HereditarilyPositive run (compose_context_family first second)) /\
  (forall (runs : SRuns d q) (first : SContextFamilies runs),
    HereditarilyPositiveFamilies runs first ->
    forall second : SContextFamilies (insert_context_families first),
      HereditarilyPositiveFamilies (insert_context_families first) second ->
      HereditarilyPositiveFamilies runs (compose_context_families first second)).
Proof.
  intros d q. apply SContextFamily_SContextFamilies_ind.
  - intros config context Hfirst second Hsecond.
    apply positive_from_proper; [constructor|].
    eapply compose_family_root_positive; eauto.
  - intros rule children result context families IH matched Hfirst second Hsecond.
    set (core := srun_node rule (insert_context_families families) matched).
    set (core_family := projT2
      (decompose_family_through_context context core second)).
    assert (Hcore : HereditarilyPositive core core_family).
    { unfold core_family. apply decompose_family_positive_core. exact Hsecond. }
    apply positive_from_proper.
    + constructor. apply IH.
      * exact (positive_family_children_general Hfirst).
      * exact (positive_family_children_general Hcore).
    + eapply compose_family_root_positive; eauto.
  - intros Hfirst second Hsecond. constructor.
  - intros run runs family IHfamily families IHfamilies Hfirst second Hsecond.
    constructor.
    + apply IHfamily.
      * exact (positive_families_head d q run runs
          (families_cons family families) Hfirst).
      * exact (positive_families_head d q
          (insert_context_family family) (insert_context_families families)
          second Hsecond).
    + apply IHfamilies.
      * exact (positive_families_tail d q run runs
          (families_cons family families) Hfirst).
      * exact (positive_families_tail d q
          (insert_context_family family) (insert_context_families families)
          second Hsecond).
Qed.

Theorem compose_context_family_compatible : forall d q (run : SRun d q)
    (first : SContextFamily run)
    (second : SContextFamily (insert_context_family first)),
    CompatibleContextFamily run first ->
    CompatibleContextFamily (insert_context_family first) second ->
    CompatibleContextFamily run (compose_context_family first second).
Proof.
  intros; eapply (proj1 (compose_context_family_compatible_mut d q)); eauto.
Qed.

Theorem compose_context_family_positive : forall d q (run : SRun d q)
    (first : SContextFamily run)
    (second : SContextFamily (insert_context_family first)),
    HereditarilyPositive run first ->
    HereditarilyPositive (insert_context_family first) second ->
    HereditarilyPositive run (compose_context_family first second).
Proof.
  intros; eapply (proj1 (compose_context_family_positive_mut d q)); eauto.
Qed.

Lemma sruns_iso_cons_same_position : forall d q
    (left right : SRun d q) lefts rights,
    SRunIsomorphic left right -> SRunsIsomorphic lefts rights ->
    SRunsIsomorphic (sruns_cons left lefts) (sruns_cons right rights).
Proof.
  intros. eapply sruns_iso_cons with (right := right) (remainder := rights).
  - constructor.
  - exact H.
  - exact H0.
Qed.

Lemma sruns_iso_append_context : forall d q
    (before after : SRuns d q) (left right : SRun d q),
    SRunIsomorphic left right ->
    SRunsIsomorphic
      (sruns_append before (sruns_cons left after))
      (sruns_append before (sruns_cons right after)).
Proof.
  intros d q before. induction before; intros after left right Hiso; cbn.
  - apply sruns_iso_cons_same_position; [exact Hiso|].
    apply (proj2 (srun_isomorphic_refl_mut d q)).
  - apply sruns_iso_cons_same_position.
    + apply (proj1 (srun_isomorphic_refl_mut d q)).
    + apply IHbefore. exact Hiso.
Qed.

Lemma scontext_plug_isomorphic_local : forall d q
    (context : SContext d q) left right,
    SRunIsomorphic left right ->
    SRunIsomorphic (scontext_plug context left) (scontext_plug context right).
Proof.
  intros d q context. induction context; intros left right Hiso; cbn.
  - exact Hiso.
  - constructor. apply sruns_iso_append_context. apply IHcontext. exact Hiso.
Qed.

Lemma remove_context_family_properties : forall d q (run : SRun d q)
    source remainder,
    SRunsRemove run source remainder ->
    forall families : SContextFamilies source,
      CompatibleContextFamilies source families ->
      HereditarilyPositiveFamilies source families ->
      exists removed remaining,
        SRunsRemove (insert_context_family removed)
          (insert_context_families families)
          (insert_context_families remaining) /\
        CompatibleContextFamily run removed /\
        CompatibleContextFamilies remainder remaining /\
        HereditarilyPositive run removed /\
        HereditarilyPositiveFamilies remainder remaining.
Proof.
  intros d q run source remainder Hremove.
  induction Hremove; intros families Hcompatible Hpositive.
  - exists (context_families_head families),
      (context_families_tail families). repeat split.
    + pose proof (context_families_eta d q run runs families) as Heta.
      pose proof (f_equal (@insert_context_families d q _) Heta) as Hinsert.
      cbn in Hinsert. rewrite <- Hinsert. constructor.
    + exact (compatible_families_head d q run runs families Hcompatible).
    + exact (compatible_families_tail d q run runs families Hcompatible).
    + exact (positive_families_head d q run runs families Hpositive).
    + exact (positive_families_tail d q run runs families Hpositive).
  - destruct (IHHremove (context_families_tail families)
      (compatible_families_tail d q head runs families Hcompatible)
      (positive_families_tail d q head runs families Hpositive)) as
      [removed [remaining [Hremove_insert
        [Hremoved_compatible [Hremaining_compatible
          [Hremoved_positive Hremaining_positive]]]]]].
    exists removed,
      (families_cons (context_families_head families) remaining).
    repeat split.
    + pose proof (context_families_eta d q head runs families) as Heta.
      pose proof (f_equal (@insert_context_families d q _) Heta) as Hinsert.
      cbn in Hinsert. rewrite <- Hinsert. constructor. exact Hremove_insert.
    + exact Hremoved_compatible.
    + constructor.
      * exact (compatible_families_head d q head runs families Hcompatible).
      * exact Hremaining_compatible.
    + exact Hremoved_positive.
    + constructor.
      * exact (positive_families_head d q head runs families Hpositive).
      * exact Hremaining_positive.
Qed.

Lemma transport_context_family_isomorphic_mut : forall (d q : nat),
  (forall (left right : SRun d q), SRunIsomorphic left right ->
    forall family : SContextFamily right,
      CompatibleContextFamily right family ->
      HereditarilyPositive right family ->
      exists transported : SContextFamily left,
        CompatibleContextFamily left transported /\
        HereditarilyPositive left transported /\
        SRunIsomorphic (insert_context_family transported)
          (insert_context_family family)) /\
  (forall (left right : SRuns d q), SRunsIsomorphic left right ->
    forall families : SContextFamilies right,
      CompatibleContextFamilies right families ->
      HereditarilyPositiveFamilies right families ->
      exists transported : SContextFamilies left,
        CompatibleContextFamilies left transported /\
        HereditarilyPositiveFamilies left transported /\
        SRunsIsomorphic (insert_context_families transported)
          (insert_context_families families)).
Proof.
  intros d q. apply SRunIsomorphic_mutind.
  - intros config family Hcompatible Hpositive.
    exists (family_leaf (context_family_context family)). repeat split.
    + constructor. exact (compatible_family_local_general Hcompatible).
    + constructor.
      pose proof (positive_context_family_root_general Hpositive) as Hroot.
      pose proof (context_family_leaf_eta d q config family) as Heta.
      pose proof (f_equal (@insert_context_family d q _) Heta) as Hinsert.
      rewrite Hinsert. exact Hroot.
    + pose proof (context_family_leaf_eta d q config family) as Heta.
      pose proof (f_equal (@insert_context_family d q _) Heta) as Hinsert.
      rewrite Hinsert.
      apply (proj1 (srun_isomorphic_refl_mut d q)).
  - intros rule left right result Hchildren IH family Hcompatible Hpositive.
    destruct (IH (context_family_children family)
      (compatible_family_children_general Hcompatible)
      (positive_family_children_general Hpositive)) as
      [transported_children [Hchildren_compatible
        [Hchildren_positive Hchildren_iso]]].
    set (transported := @family_node d q rule left result
      (context_family_context family) transported_children
      (context_family_matched family)).
    assert (Hinsert_iso : SRunIsomorphic
        (insert_context_family transported)
        (insert_context_family family)).
    { pose proof (context_family_node_eta d q rule right result family) as Heta.
      pose proof (f_equal (@insert_context_family d q _) Heta) as Hinsert.
      rewrite <- Hinsert. unfold transported. cbn.
      apply scontext_plug_isomorphic_local.
      constructor. exact Hchildren_iso. }
    exists transported. repeat split.
    + unfold transported. constructor.
      * exact Hchildren_compatible.
      * exact (compatible_family_matched_state_general Hcompatible).
      * eapply context_compatible_replace.
        -- exact (compatible_family_local_general Hcompatible).
        -- reflexivity.
    + unfold transported. constructor.
      * exact Hchildren_positive.
      * unfold transported in Hinsert_iso.
        rewrite (srun_isomorphic_root _ _ _ _ Hinsert_iso).
        exact (positive_context_family_root_general Hpositive).
    + exact Hinsert_iso.
  - intros families Hcompatible Hpositive.
    exists families. repeat split; try assumption.
    apply (proj2 (srun_isomorphic_refl_mut d q)).
  - intros left lefts right rights remainder Hremove Hhead IHhead Htail
      IHtail families Hcompatible Hpositive.
    destruct (remove_context_family_properties d q right rights remainder
      Hremove families Hcompatible Hpositive) as
      [removed [remaining [Hremove_insert
        [Hremoved_compatible [Hremaining_compatible
          [Hremoved_positive Hremaining_positive]]]]]].
    destruct (IHhead removed Hremoved_compatible Hremoved_positive) as
      [transported_head [Hhead_compatible [Hhead_positive Hhead_iso]]].
    destruct (IHtail remaining Hremaining_compatible Hremaining_positive) as
      [transported_tail [Htail_compatible [Htail_positive Htail_iso]]].
    exists (families_cons transported_head transported_tail). repeat split.
    + constructor; assumption.
    + constructor; assumption.
    + cbn. eapply sruns_iso_cons; eauto.
Qed.

Theorem transport_context_family_isomorphic : forall d q
    (left right : SRun d q),
    SRunIsomorphic left right ->
    forall family : SContextFamily right,
      CompatibleContextFamily right family ->
      HereditarilyPositive right family ->
      exists transported : SContextFamily left,
        CompatibleContextFamily left transported /\
        HereditarilyPositive left transported /\
        SRunIsomorphic (insert_context_family transported)
          (insert_context_family family).
Proof.
  intros. eapply (proj1 (transport_context_family_isomorphic_mut d q)); eauto.
Qed.

Theorem context_order_trans : forall d q (S : SBVAS d q)
    (first second third : SRun d q),
    ContextOrder S first second -> ContextOrder S second third ->
    ContextOrder S first third.
Proof.
  intros d q S first second third
    [Hfirst_valid [Hsecond_valid
      [first_family [Hfirst_compatible [Hfirst_positive Hfirst_iso]]]]]
    [_ [Hthird_valid
      [second_family [Hsecond_compatible [Hsecond_positive Hsecond_iso]]]]].
  destruct (transport_context_family_isomorphic d q
    (insert_context_family first_family) second Hfirst_iso
    second_family Hsecond_compatible Hsecond_positive) as
    [transported [Htransported_compatible
      [Htransported_positive Htransported_iso]]].
  split; [exact Hfirst_valid|]. split; [exact Hthird_valid|].
  exists (compose_context_family first_family transported). repeat split.
  - eapply compose_context_family_compatible; eauto.
  - eapply compose_context_family_positive; eauto.
  - rewrite compose_context_family_insert.
    eapply srun_isomorphic_trans; eauto.
Qed.

Theorem context_order_root_state : forall d q (S : SBVAS d q) left right,
    ContextOrder S left right ->
    fst (root_config left) = fst (root_config right).
Proof.
  intros d q S left right [_ [_ [family [Hcompat [_ Hiso]]]]].
  rewrite <- (srun_isomorphic_root _ _ _ _ Hiso).
  symmetry. now apply compatible_context_family_root.
Qed.

Lemma nvec_le_exact_difference : forall d (left right : NVec d),
    nvec_le left right -> exists delta, right = nvec_add left delta.
Proof.
  intros d left right Hle.
  exists (Vector.map2 Nat.sub right left).
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
  specialize (Hle index). lia.
Qed.

Theorem context_family_root_effect_exact : forall d q
    (run : SRun d q) (family : SContextFamily run),
    HereditarilyPositive run family ->
    exists delta,
      snd (root_config (insert_context_family family)) =
      nvec_add (snd (root_config run)) delta.
Proof.
  intros d q run family Hpositive. inversion Hpositive; subst;
    match goal with
    | Hroot : RootConfigLe _ _ |- _ =>
        destruct Hroot as [_ Hle]; apply nvec_le_exact_difference; exact Hle
    end.
Qed.
