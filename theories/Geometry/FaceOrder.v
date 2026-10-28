From Coq Require Import Arith.PeanoNat Arith.Wf_nat Classical_Prop Lia List Permutation
  RelationClasses SetoidList SetoidPermutation.
From Mell.Geometry Require Import Faces FiniteFaces LatticeGordanInterface
  MathCompBridge QConeCore RationalDefinability.

Import ListNotations.

Definition FaceSubset {d} (left right : QSet d) : Prop :=
  forall point, left point -> right point.

Definition ProperFaceSubset {d} (left right : QSet d) : Prop :=
  FaceSubset left right /\ ~ SameSet left right.

Lemma face_subset_refl : forall d (face : QSet d), FaceSubset face face.
Proof. firstorder. Qed.

Lemma face_subset_trans : forall d (left middle right : QSet d),
    FaceSubset left middle -> FaceSubset middle right ->
    FaceSubset left right.
Proof. firstorder. Qed.

Lemma face_subset_antisym_same_set : forall d (left right : QSet d),
    FaceSubset left right -> FaceSubset right left -> SameSet left right.
Proof. firstorder. Qed.

Lemma same_set_face_subset_both : forall d (left right : QSet d),
    SameSet left right <->
    FaceSubset left right /\ FaceSubset right left.
Proof.
  intros d left right. split; [firstorder|].
  intros [Hleft Hright]. now apply face_subset_antisym_same_set.
Qed.

Lemma proper_face_subset_irrefl : forall d (face : QSet d),
    ~ ProperFaceSubset face face.
Proof. intros d face [_ Hproper]. apply Hproper, same_set_refl. Qed.

Lemma proper_face_subset_trans : forall d (left middle right : QSet d),
    ProperFaceSubset left middle -> ProperFaceSubset middle right ->
    ProperFaceSubset left right.
Proof.
  intros d left middle right [Hlm Hneq_lm] [Hmr Hneq_mr]. split.
  - now apply face_subset_trans with (middle := middle).
  - intro Hlr. apply Hneq_lm, face_subset_antisym_same_set; [exact Hlm|].
    apply face_subset_trans with (middle := right); [exact Hmr|].
    exact (proj2 (proj1 (same_set_face_subset_both d left right) Hlr)).
Qed.

Lemma face_subset_set_ext : forall d
    (left left' right right' : QSet d),
    SameSet left left' -> SameSet right right' ->
    (FaceSubset left right <-> FaceSubset left' right').
Proof. firstorder. Qed.

Lemma proper_face_subset_set_ext : forall d
    (left left' right right' : QSet d),
    SameSet left left' -> SameSet right right' ->
    (ProperFaceSubset left right <-> ProperFaceSubset left' right').
Proof.
  intros d left left' right right' Hleft Hright. split;
    intros [Hsubset Hproper]; split.
  - apply (proj1 (face_subset_set_ext d left left' right right'
      Hleft Hright)); exact Hsubset.
  - intro Hsame. apply Hproper.
    eapply same_set_trans; [exact Hleft|].
    eapply same_set_trans; [exact Hsame|apply same_set_sym; exact Hright].
  - apply (proj2 (face_subset_set_ext d left left' right right'
      Hleft Hright)); exact Hsubset.
  - intro Hsame. apply Hproper.
    eapply same_set_trans; [apply same_set_sym; exact Hleft|].
    eapply same_set_trans; [exact Hsame|exact Hright].
Qed.

Lemma face_of_set_ext_both : forall d
    (cone cone' face face' : QSet d),
    SameSet cone cone' -> SameSet face face' ->
    (FaceOf cone face <-> FaceOf cone' face').
Proof.
  intros d cone cone' face face' Hcone Hface. split; intro H.
  - apply face_of_face_ext with (left := face); [exact Hface|].
    now apply face_of_cone_ext with (left := cone).
  - apply face_of_face_ext with (left := face');
      [apply same_set_sym; exact Hface|].
    apply face_of_cone_ext with (left := cone');
      [apply same_set_sym; exact Hcone|exact H].
Qed.

Definition ExtensionalNoDup {d} (faces : list (QSet d)) : Prop :=
  NoDupA (@SameSet (QVec d)) faces.

Lemma same_set_equivalence : forall A,
    Equivalence (@SameSet A).
Proof.
  intro A. constructor.
  - intro set. apply same_set_refl.
  - intros left right H. now apply same_set_sym.
  - intros left middle right Hleft Hright.
    now apply same_set_trans with (middle := middle).
Qed.

Lemma permutation_to_same_set_permutation : forall A
    (left right : list (A -> Prop)),
    Permutation left right ->
    @PermutationA (A -> Prop) (@SameSet A) left right.
Proof.
  intros A left right Hperm. induction Hperm.
  - constructor.
  - apply permA_skip; [apply same_set_refl|exact IHHperm].
  - apply permA_swap.
  - eapply permA_trans; eassumption.
Qed.

Lemma extensional_nodup_permutation : forall d
    (left right : list (QSet d)),
    Permutation left right -> ExtensionalNoDup left ->
    ExtensionalNoDup right.
Proof.
  intros d left right Hperm Hnodup.
  eapply (@PermutationA_preserves_NoDupA (QSet d)
    (@SameSet (QVec d)) (same_set_equivalence (QVec d)) left right).
  - now apply permutation_to_same_set_permutation.
  - exact Hnodup.
Qed.

Lemma list_subsequence_in : forall A (selected source : list A) value,
    ListSubsequence selected source ->
    List.In value selected -> List.In value source.
Proof.
  intros A selected source value Hsub. induction Hsub; cbn; intuition.
Qed.

Lemma extensional_nodup_subsequence : forall d
    (selected source : list (QSet d)),
    ListSubsequence selected source ->
    ExtensionalNoDup source -> ExtensionalNoDup selected.
Proof.
  intros d selected source Hsub. induction Hsub; intro Hnodup.
  - constructor.
  - inversion Hnodup; subst. now apply IHHsub.
  - inversion Hnodup as [|? ? Hfresh Htail]; subst. constructor.
    + intro Hin. apply Hfresh.
      apply InA_alt in Hin as [value [Hsame Hin]].
      apply InA_alt. exists value. split; [exact Hsame|].
      now apply list_subsequence_in with (selected := selected).
    + now apply IHHsub.
Qed.

Theorem deduplicate_same_set : forall d (faces : list (QSet d)),
    exists representatives,
      ListSubsequence representatives faces /\
      ExtensionalNoDup representatives /\
      (forall face, List.In face faces ->
        exists representative,
          List.In representative representatives /\
          SameSet face representative).
Proof.
  intros d faces. induction faces as
      [|face faces [representatives
        [Hsubsequence [Hnodup Hcomplete]]]].
  - exists []. repeat split; try constructor. contradiction.
  - destruct (classic (InA (@SameSet (QVec d)) face representatives))
      as [Hpresent|Hfresh].
    + exists representatives. repeat split.
      * now apply list_subsequence_skip.
      * exact Hnodup.
      * intros value [Heq|Hin].
        -- subst value. apply InA_alt in Hpresent as
             [representative [Hsame Hin]].
           exists representative. now split.
        -- now apply Hcomplete.
    + exists (face :: representatives). repeat split.
      * now apply list_subsequence_keep.
      * now constructor.
      * intros value [Heq|Hin].
        -- subst value. exists face. split; [now left|apply same_set_refl].
        -- destruct (Hcomplete value Hin) as
             [representative [Hrepresentative Hsame]].
           exists representative. split; [now right|exact Hsame].
Qed.

Lemma extensional_nodup_nth_error : forall d
    (faces : list (QSet d)),
    ExtensionalNoDup faces ->
    forall i j face_i face_j,
      nth_error faces i = Some face_i ->
      nth_error faces j = Some face_j ->
      i <> j -> ~ SameSet face_i face_j.
Proof.
  intros d faces Hnodup. induction Hnodup as [|head tail Hfresh Htail IH];
    intros i j face_i face_j Hi Hj Hneq.
  - destruct i; discriminate.
  - destruct i as [|i], j as [|j]; cbn in Hi, Hj.
    + contradiction.
    + injection Hi as Hi; subst face_i. intro Hsame.
      apply Hfresh, InA_alt. exists face_j. split; [exact Hsame|].
      now apply nth_error_In with (n := j).
    + injection Hj as Hj; subst face_j. intro Hsame.
      apply Hfresh, InA_alt. exists face_i. split.
      * now apply same_set_sym.
      * now apply nth_error_In with (n := i).
    + apply IH with (i := i) (j := j); try assumption. lia.
Qed.

Lemma finite_list_has_maximal : forall A (relation : A -> A -> Prop),
    Irreflexive relation -> Transitive relation ->
    forall source,
      source <> [] ->
      exists maximal remaining,
        Permutation source (maximal :: remaining) /\
        (forall value, List.In value remaining -> ~ relation maximal value).
Proof.
  intros A relation Hirrefl Htrans source.
  induction source as [|head tail IH]; intro Hnonempty; [contradiction|].
  destruct tail as [|next tail].
  - exists head, []. split; [apply Permutation_refl|contradiction].
  - destruct (IH ltac:(discriminate)) as
      [maximal [remaining [Hperm Hmaximal]]].
    destruct (classic (relation maximal head)) as [Hbelow|Hnotbelow].
    + exists head, (maximal :: remaining). split.
      * now apply perm_skip.
      * intros value [Heq|Hin] Hrelation.
        -- subst value. apply (Hirrefl maximal).
           now apply (Htrans maximal head maximal).
        -- apply (Hmaximal value Hin), (Htrans maximal head value);
             assumption.
    + exists maximal, (head :: remaining). split.
      * eapply Permutation_trans with
          (l' := head :: maximal :: remaining).
        -- apply perm_skip. exact Hperm.
        -- exact (perm_swap maximal head remaining).
      * intros value [Heq|Hin] Hrelation.
        -- subst value. contradiction.
        -- now apply (Hmaximal value Hin).
Qed.

Definition ReverseInclusionOrdered {d} (faces : list (QSet d)) : Prop :=
  forall i j face_i face_j,
    nth_error faces i = Some face_i ->
    nth_error faces j = Some face_j ->
    ProperFaceSubset face_i face_j -> j < i.

Lemma proper_face_subset_irreflexive_relation : forall d,
    Irreflexive (@ProperFaceSubset d).
Proof. intros d face; apply proper_face_subset_irrefl. Qed.

Lemma proper_face_subset_transitive_relation : forall d,
    Transitive (@ProperFaceSubset d).
Proof. intros d left middle right; apply proper_face_subset_trans. Qed.

Lemma finite_faces_reverse_inclusion_order : forall d
    (source : list (QSet d)),
    exists ordered,
      Permutation source ordered /\ ReverseInclusionOrdered ordered.
Proof.
  intros d source.
  remember (length source) as size eqn:Hsize.
  revert source Hsize. induction size using lt_wf_ind.
  intros source Hsize. destruct source as [|head tail].
  - exists []. split; [apply Permutation_refl|].
    intros i; destruct i; discriminate.
  - destruct (finite_list_has_maximal (QSet d) (@ProperFaceSubset d)
      (proper_face_subset_irreflexive_relation d)
      (proper_face_subset_transitive_relation d)
      (head :: tail) ltac:(discriminate)) as
      [maximal [remaining [Hperm Hmaximal]]].
    assert (Hlength : length remaining < size).
    { apply Permutation_length in Hperm. cbn in Hperm, Hsize. lia. }
    destruct (H (length remaining) Hlength remaining eq_refl) as
      [ordered [Hordered_perm Hordered]].
    exists (maximal :: ordered). split.
    + eapply Permutation_trans; [exact Hperm|]. now apply perm_skip.
    + intros i j face_i face_j Hi Hj Hproper.
      destruct i as [|i], j as [|j]; cbn in Hi, Hj.
      * injection Hi as Hi; injection Hj as Hj; subst.
        exfalso. now apply (proper_face_subset_irrefl d face_j).
      * injection Hi as Hi; subst face_i.
        exfalso. apply (Hmaximal face_j).
        -- eapply Permutation_in; [apply Permutation_sym; exact Hordered_perm|].
           now apply nth_error_In with (n := j).
        -- exact Hproper.
      * lia.
      * specialize (Hordered i j face_i face_j Hi Hj Hproper). lia.
Qed.

Lemma remove_cone_representatives : forall d (cone : QSet d)
    (faces : list (QSet d)),
    exists remaining,
      ListSubsequence remaining faces /\
      (forall face, List.In face remaining -> ~ SameSet cone face) /\
      (forall face, List.In face faces -> ~ SameSet cone face ->
        List.In face remaining).
Proof.
  intros d cone faces.
  apply select_property_subsequence.
Qed.

Theorem polyhedral_faces_linearized : forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists faces : list (QSet d),
      (exists tail, faces = cone :: tail) /\
      (forall face,
        List.In face faces -> FaceOf cone face) /\
      (forall face,
        FaceOf cone face ->
        exists representative,
          List.In representative faces /\
          SameSet face representative) /\
      (forall i j face_i face_j,
        nth_error faces i = Some face_i ->
        nth_error faces j = Some face_j ->
        i <> j -> ~ SameSet face_i face_j) /\
      (forall i j face_i face_j,
        nth_error faces i = Some face_i ->
        nth_error faces j = Some face_j ->
        FaceSubset face_j face_i -> i <= j).
Proof.
  intros d cone Hpolyhedral.
  destruct (polyhedral_faces_finite d cone Hpolyhedral) as
    [candidates [Hsound Hcomplete]].
  destruct (remove_cone_representatives d cone candidates) as
    [without_cone [Hwithout_sub [Hwithout_sound Hwithout_complete]]].
  destruct (deduplicate_same_set d without_cone) as
    [unique [Hunique_sub [Hunique_nodup Hunique_complete]]].
  destruct (finite_faces_reverse_inclusion_order d unique) as
    [ordered [Hordered_perm Hordered]].
  assert (Hordered_nodup : ExtensionalNoDup ordered).
  { apply extensional_nodup_permutation with (left := unique);
      [exact Hordered_perm|exact Hunique_nodup]. }
  assert (Hordered_not_cone : forall face,
      List.In face ordered -> ~ SameSet cone face).
  { intros face Hin. apply Hwithout_sound.
    apply (@Permutation_in _ ordered unique face
      (Permutation_sym Hordered_perm)) in Hin.
    now apply list_subsequence_in with (selected := unique). }
  assert (Hall_nodup : ExtensionalNoDup (cone :: ordered)).
  { constructor.
    - intro Hin. apply InA_alt in Hin as [face [Hsame Hin]].
      apply (Hordered_not_cone face Hin). exact Hsame.
    - exact Hordered_nodup. }
  exists (cone :: ordered). repeat split.
  - now exists ordered.
  - intros face [Heq|Hin].
    + subst face. apply face_self.
    + apply Hsound.
      eapply list_subsequence_in; [exact Hwithout_sub|].
      apply (@Permutation_in _ ordered unique face
        (Permutation_sym Hordered_perm)) in Hin.
      now apply list_subsequence_in with (selected := unique).
  - intros face Hface.
    destruct (classic (SameSet face cone)) as [Hsame|Hnot_same].
    + exists cone. split; [now left|exact Hsame].
    + destruct (Hcomplete face Hface) as
        [candidate [Hcandidate Hcandidate_same]].
      assert (Hcandidate_not_cone : ~ SameSet cone candidate).
      { intro Hcone_candidate. apply Hnot_same.
        eapply same_set_trans; [exact Hcandidate_same|].
        now apply same_set_sym. }
      pose proof (Hwithout_complete candidate Hcandidate
        Hcandidate_not_cone) as Hcandidate_without.
      destruct (Hunique_complete candidate Hcandidate_without) as
        [representative [Hrepresentative Hsame]].
      exists representative. split.
      * right. now apply (@Permutation_in _ unique ordered representative
          Hordered_perm).
      * now apply same_set_trans with (middle := candidate).
  - intros i j face_i face_j Hi Hj Hneq.
    now apply extensional_nodup_nth_error with
      (faces := cone :: ordered) (i := i) (j := j).
  - intros i j face_i face_j Hi Hj Hsubset.
    destruct (Nat.eq_dec i j) as [->|Hneq]; [lia|].
    assert (Hnot_same : ~ SameSet face_j face_i).
    { intro Hsame.
      apply (extensional_nodup_nth_error d (cone :: ordered)
        Hall_nodup i j face_i face_j Hi Hj Hneq).
      now apply same_set_sym. }
    assert (Hproper : ProperFaceSubset face_j face_i).
    { now split. }
    destruct i as [|i], j as [|j]; cbn in Hi, Hj.
    + contradiction.
    + lia.
    + injection Hj as Hj; subst face_j.
      exfalso. apply Hnot_same, face_subset_antisym_same_set.
      * exact Hsubset.
      * unfold FaceSubset.
        apply (face_subset d cone face_i).
        apply Hsound.
        eapply list_subsequence_in; [exact Hwithout_sub|].
        eapply list_subsequence_in; [exact Hunique_sub|].
        apply (@Permutation_in _ ordered unique face_i
          (Permutation_sym Hordered_perm)).
        now apply nth_error_In with (n := i).
    + specialize (Hordered j i face_j face_i Hj Hi Hproper). lia.
Qed.
