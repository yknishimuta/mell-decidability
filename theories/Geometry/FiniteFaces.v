From Coq Require Import Classical_Prop Lia List PeanoNat.
From Mell.Geometry Require Import Faces LatticeGordanInterface MathCompBridge
  QConeCore RationalDefinability.

Import ListNotations.

Inductive ListSubsequence {A : Type} : list A -> list A -> Prop :=
| list_subsequence_nil : forall source,
    ListSubsequence [] source
| list_subsequence_skip : forall head selected source,
    ListSubsequence selected source ->
    ListSubsequence selected (head :: source)
| list_subsequence_keep : forall head selected source,
    ListSubsequence selected source ->
    ListSubsequence (head :: selected) (head :: source).

Fixpoint all_sublists {A : Type} (source : list A) : list (list A) :=
  match source with
  | [] => [[]]
  | head :: tail =>
      all_sublists tail ++ List.map (cons head) (all_sublists tail)
  end.

Lemma all_sublists_contains_nil : forall A (source : list A),
    List.In [] (all_sublists source).
Proof.
  intros A source. induction source as [|head tail IH]; cbn.
  - now left.
  - apply in_or_app. now left.
Qed.

Lemma all_sublists_contains_source : forall A (source : list A),
    List.In source (all_sublists source).
Proof.
  intros A source. induction source as [|head tail IH]; cbn.
  - now left.
  - apply in_or_app. right. apply in_map_iff.
    exists tail. now split.
Qed.

Lemma all_sublists_complete : forall A (source selected : list A),
    ListSubsequence selected source ->
    List.In selected (all_sublists source).
Proof.
  intros A source selected Hselected. induction Hselected; cbn.
  - apply all_sublists_contains_nil.
  - apply in_or_app. now left.
  - apply in_or_app. right. apply in_map_iff.
    exists selected. now split.
Qed.

Lemma all_sublists_sound : forall A (source selected : list A),
    List.In selected (all_sublists source) ->
    ListSubsequence selected source.
Proof.
  intros A source. induction source as [|head tail IH]; intros selected Hin.
  - cbn in Hin. destruct Hin as [Heq|Hfalse].
    + subst selected. apply list_subsequence_nil.
    + contradiction.
  - cbn in Hin. apply in_app_or in Hin as [Hskip|Hkeep].
    + apply list_subsequence_skip, IH. exact Hskip.
    + apply in_map_iff in Hkeep as [kept [Heq Hin]].
      subst selected. apply list_subsequence_keep, IH. exact Hin.
Qed.

Lemma all_sublists_length : forall A (source : list A),
    length (all_sublists source) = Nat.pow 2 (length source).
Proof.
  intros A source. induction source as [|head tail IH]; cbn.
  - reflexivity.
  - rewrite List.length_app, List.length_map, IH. lia.
Qed.

Lemma list_subsequence_length : forall A (selected source : list A),
    ListSubsequence selected source ->
    (length selected <= length source)%nat.
Proof. intros A selected source H; induction H; cbn; lia. Qed.

Lemma filter_list_subsequence : forall A (test : A -> bool) source,
    ListSubsequence (List.filter test source) source.
Proof.
  intros A test source. induction source as [|head tail IH]; cbn.
  - constructor.
  - destruct (test head); [now apply list_subsequence_keep|].
    now apply list_subsequence_skip.
Qed.

Lemma same_set_refl : forall A (set : A -> Prop), SameSet set set.
Proof. intros A set value; reflexivity. Qed.

Lemma same_set_sym : forall A (left right : A -> Prop),
    SameSet left right -> SameSet right left.
Proof. intros A left right Heq value; symmetry; apply Heq. Qed.

Lemma same_set_trans : forall A (left middle right : A -> Prop),
    SameSet left middle -> SameSet middle right -> SameSet left right.
Proof.
  intros A left middle right Hleft Hright value.
  now rewrite (Hleft value), (Hright value).
Qed.

Lemma supporting_normal_set_ext : forall d (left right : QSet d) normal,
    SameSet left right ->
    (SupportingNormal left normal <-> SupportingNormal right normal).
Proof.
  intros d left right normal Heq. split; intros H point Hpoint.
  - apply H. exact (proj2 (Heq point) Hpoint).
  - apply H. exact (proj1 (Heq point) Hpoint).
Qed.

Lemma face_of_cone_ext : forall d (left right face : QSet d),
    SameSet left right ->
    FaceOf left face -> FaceOf right face.
Proof.
  intros d left right face Hcone [normals [Hsupport Hface]].
  exists normals. split.
  - apply (proj2 (List.Forall_forall _ _)). intros normal Hnormal.
    apply (proj1 (supporting_normal_set_ext d left right normal Hcone)).
    exact (proj1 (List.Forall_forall _ _) Hsupport normal Hnormal).
  - intro point. rewrite (Hface point), (Hcone point). reflexivity.
Qed.

Lemma face_of_face_ext : forall d (cone left right : QSet d),
    SameSet left right ->
    FaceOf cone left -> FaceOf cone right.
Proof.
  intros d cone left right Hfaces [normals [Hsupport Hleft]].
  exists normals. split; [exact Hsupport|].
  intro point. rewrite <- (Hfaces point). apply Hleft.
Qed.

Theorem face_has_sublist_generators : forall d
    (generators : list (QVec d)) (face : QSet d),
    FaceOf (qcone_generated generators) face ->
    exists selected : list (QVec d),
      List.In selected (all_sublists generators) /\
      SameSet face (qcone_generated selected).
Proof.
  intros d generators face [normals [Hsupport Hface]].
  exists (face_generators normals generators). split.
  - apply all_sublists_complete, filter_list_subsequence.
  - eapply same_set_trans; [exact Hface|].
    apply same_set_sym, face_generator_filter. exact Hsupport.
Qed.

Definition polyhedral_face_candidates {d}
    (generators : list (QVec d)) : list (QSet d) :=
  List.map (fun selected => qcone_generated selected)
    (all_sublists generators).

Lemma select_property_subsequence : forall A (property : A -> Prop)
    (source : list A),
    exists selected,
      ListSubsequence selected source /\
      (forall value, List.In value selected -> property value) /\
      (forall value, List.In value source -> property value ->
        List.In value selected).
Proof.
  intros A property source. induction source as
      [|head tail [selected [Hsubsequence [Hsound Hcomplete]]]].
  - exists []. repeat split.
    + constructor.
    + intros value Hvalue. contradiction.
    + intros value Hvalue. contradiction.
  - destruct (classic (property head)) as [Hhead|Hhead].
    + exists (head :: selected). repeat split.
      * now apply list_subsequence_keep.
      * intros value [->|Hvalue]; [exact Hhead|now apply Hsound].
      * intros value [->|Hvalue] Hproperty; [now left|].
        right. now apply Hcomplete.
    + exists selected. repeat split.
      * now apply list_subsequence_skip.
      * exact Hsound.
      * intros value [Heq|Hvalue] Hproperty.
        -- subst value. contradiction.
        -- now apply Hcomplete.
Qed.

Theorem polyhedral_faces_finite_bounded : forall d (cone : QSet d)
    (generators : list (QVec d)),
    SameSet cone (qcone_generated generators) ->
    exists faces : list (QSet d),
      (length faces <= Nat.pow 2 (length generators))%nat /\
      (forall face, List.In face faces -> FaceOf cone face) /\
      (forall face, FaceOf cone face ->
        exists representative,
          List.In representative faces /\
          SameSet face representative).
Proof.
  intros d cone generators Hcone.
  destruct (select_property_subsequence (QSet d) (FaceOf cone)
    (polyhedral_face_candidates generators)) as
    [faces [Hfaces_subsequence [Hfaces_sound Hfaces_complete]]].
  exists faces. split.
  - eapply Nat.le_trans.
    + exact (list_subsequence_length (QSet d) faces
        (polyhedral_face_candidates generators) Hfaces_subsequence).
    +
    unfold polyhedral_face_candidates. rewrite List.length_map,
      all_sublists_length. apply Nat.le_refl.
  - split; [exact Hfaces_sound|]. intros face Hface.
    assert (Hgenerated_face :
        FaceOf (qcone_generated generators) face).
    { now apply face_of_cone_ext with (left := cone). }
    destruct (face_has_sublist_generators d generators face Hgenerated_face)
      as [selected [Hselected Hsame]].
    exists (qcone_generated selected). split.
    + apply Hfaces_complete.
      * unfold polyhedral_face_candidates. apply in_map_iff.
        exists selected. now split.
      * now apply face_of_face_ext with (left := face).
    + exact Hsame.
Qed.

Theorem polyhedral_faces_finite : forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists faces : list (QSet d),
      (forall face,
        List.In face faces ->
        FaceOf cone face) /\
      (forall face,
        FaceOf cone face ->
        exists representative,
          List.In representative faces /\
          SameSet face representative).
Proof.
  intros d cone [generators Hcone].
  destruct (polyhedral_faces_finite_bounded d cone generators Hcone)
    as [faces [_ [Hsound Hcomplete]]].
  exists faces. now split.
Qed.
