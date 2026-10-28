From Coq Require Import List.
From Mell.BVASS Require Import Stateful ContextInsertion.

Lemma sruns_in_split : forall d q (run : SRun d q) runs,
    SRunsIn run runs ->
    exists before after,
      runs = sruns_append before (sruns_cons run after).
Proof.
  intros d q run runs Hin. induction Hin.
  - exists sruns_nil, runs. reflexivity.
  - destruct IHHin as [before [after Heq]]. subst runs.
    exists (sruns_cons other before), after. reflexivity.
Qed.

Lemma valid_sruns_member : forall d q (S : SBVAS d q) run runs,
    ValidSRuns S runs -> SRunsIn run runs -> ValidSRun S run.
Proof.
  intros d q S run runs Hvalid Hin. induction Hin.
  - inversion Hvalid; subst. assumption.
  - inversion Hvalid; subst. apply IHHin. assumption.
Qed.

Lemma sruns_iso_cons_positional : forall d q
    (left right : SRun d q) lefts rights,
    SRunIsomorphic left right -> SRunsIsomorphic lefts rights ->
    SRunsIsomorphic (sruns_cons left lefts) (sruns_cons right rights).
Proof.
  intros. eapply sruns_iso_cons with (right := right) (remainder := rights).
  - constructor.
  - exact H.
  - exact H0.
Qed.

Lemma sruns_iso_append_hole : forall d q
    (before after : SRuns d q) (left right : SRun d q),
    SRunIsomorphic left right ->
    SRunsIsomorphic
      (sruns_append before (sruns_cons left after))
      (sruns_append before (sruns_cons right after)).
Proof.
  intros d q before. induction before; intros after left right Hiso; cbn.
  - apply sruns_iso_cons_positional; [exact Hiso|].
    apply (proj2 (srun_isomorphic_refl_mut d q)).
  - apply sruns_iso_cons_positional.
    + apply (proj1 (srun_isomorphic_refl_mut d q)).
    + apply IHbefore. exact Hiso.
Qed.

Lemma scontext_plug_isomorphic : forall d q (context : SContext d q) left right,
    SRunIsomorphic left right ->
    SRunIsomorphic (scontext_plug context left) (scontext_plug context right).
Proof.
  intros d q context. induction context; intros left right Hiso; cbn.
  - exact Hiso.
  - constructor. apply sruns_iso_append_hole. apply IHcontext. exact Hiso.
Qed.

Definition FamilyEmbedWitness {d q} (left right : SRun d q) : Prop :=
  exists family : SContextFamily left,
    CompatibleProper left family /\ PositiveProper left family /\
    SRunIsomorphic (insert_context_family family) right.

Definition FamiliesEmbedWitness {d q} (left right : SRuns d q) : Prop :=
  exists families : SContextFamilies left,
    CompatibleContextFamilies left families /\
    HereditarilyPositiveFamilies left families /\
    SRunsIsomorphic (insert_context_families families) right.

Lemma valid_node_parts : forall d q (S : SBVAS d q) rule children result,
    ValidSRun S (srun_node rule children result) ->
    ValidSRuns S children /\ fst result = output_state rule.
Proof. intros d q S rule children result H; inversion H; subst; auto. Qed.

Lemma valid_cons_parts : forall d q (S : SBVAS d q) run runs,
    ValidSRuns S (sruns_cons run runs) ->
    ValidSRun S run /\ ValidSRuns S runs.
Proof. intros d q S run runs H; inversion H; subst; auto. Qed.

Lemma ordered_embed_family_mut : forall d q (S : SBVAS d q),
  (forall left right, OrderedDecorEmbed left right ->
    ValidSRun S left -> ValidSRun S right -> FamilyEmbedWitness left right) /\
  (forall left right, OrderedDecorEmbeds left right ->
    ValidSRuns S left -> ValidSRuns S right -> FamiliesEmbedWitness left right).
Proof.
  intros d q S. apply OrderedDecorEmbed_mutind.
  - intros config Hleft Hright.
    exists (identity_context_family (srun_leaf config)). repeat split.
    + constructor.
    + constructor.
    + cbn. constructor.
  - intros rule left_children right_children left_result right_result
      Hchildren IH Hleft Hright.
    destruct (valid_node_parts d q S rule left_children left_result Hleft)
      as [Hleft_children Hleft_state].
    destruct (valid_node_parts d q S rule right_children right_result Hright)
      as [Hright_children Hright_state].
    destruct (IH Hleft_children Hright_children) as
      [families [Hcompatible [Hpositive Hiso]]].
    exists (@family_node d q rule left_children left_result
      scontext_hole families right_result). repeat split.
    + constructor; [exact Hcompatible|]. now rewrite Hleft_state, Hright_state.
    + constructor. exact Hpositive.
    + cbn. constructor. exact Hiso.
  - intros small rule children result child Hin Hembed IH Hsmall Hwhole.
    destruct (valid_node_parts d q S rule children result Hwhole)
      as [Hchildren Hstate].
    pose proof (valid_sruns_member d q S child children Hchildren Hin) as Hchild.
    destruct (IH Hsmall Hchild) as [family [Hcompatible [Hpositive Hiso]]].
    destruct (sruns_in_split d q child children Hin) as
      [before [after Hsplit]].
    set (outer := scontext_node rule before scontext_hole after result).
    exists (wrap_family_context outer family). repeat split.
    + apply wrap_family_compatible_proper. exact Hcompatible.
    + apply wrap_family_positive_proper. exact Hpositive.
    + rewrite insert_wrap_family_context.
      pose proof (scontext_plug_isomorphic d q outer _ _ Hiso) as Houter.
      unfold outer in Houter. cbn in Houter.
      rewrite <- Hsplit in Houter. exact Houter.
  - intros Hleft Hright. exists families_nil. repeat split; constructor.
  - intros left right lefts rights Hroot Hembed IHembed Htails IHtails
      Hleft Hright.
    destruct (valid_cons_parts d q S left lefts Hleft) as [Hlv Hls].
    destruct (valid_cons_parts d q S right rights Hright) as [Hrv Hrs].
    destruct (IHembed Hlv Hrv) as [family [Hproper [Hpproper Hiso]]].
    destruct (IHtails Hls Hrs) as [families [Hcompat [Hpositive Hisos]]].
    assert (Hstate : family_root_compatible family).
    { unfold family_root_compatible. rewrite (srun_isomorphic_root _ _ _ _ Hiso).
      symmetry. exact (proj1 Hroot). }
    assert (Hroot_family : RootConfigLe (root_config left)
        (root_config (insert_context_family family))).
    { rewrite (srun_isomorphic_root _ _ _ _ Hiso). exact Hroot. }
    exists (families_cons family families). repeat split.
    + constructor.
      * apply compatible_from_proper; assumption.
      * exact Hcompat.
    + constructor.
      * apply positive_from_proper; [exact Hpproper|exact Hroot_family].
      * exact Hpositive.
    + cbn. apply sruns_iso_cons_positional; assumption.
Qed.

Theorem ordered_embed_implies_context_insert :
    forall d q (S : SBVAS d q) alpha beta,
      ValidSRun S alpha -> ValidSRun S beta ->
      RootConfigLe (root_config alpha) (root_config beta) ->
      OrderedDecorEmbed alpha beta ->
      ContextOrder S alpha beta.
Proof.
  intros d q S alpha beta Halpha Hbeta Hroot Hembed.
  destruct (proj1 (ordered_embed_family_mut d q S) alpha beta Hembed
    Halpha Hbeta) as [family [Hproper [Hpproper Hiso]]].
  split; [exact Halpha|]. split; [exact Hbeta|]. exists family. repeat split.
  - apply compatible_from_proper; [exact Hproper|].
    unfold family_root_compatible. rewrite (srun_isomorphic_root _ _ _ _ Hiso).
    symmetry. exact (proj1 Hroot).
  - apply positive_from_proper; [exact Hpproper|].
    rewrite (srun_isomorphic_root _ _ _ _ Hiso). exact Hroot.
  - exact Hiso.
Qed.
