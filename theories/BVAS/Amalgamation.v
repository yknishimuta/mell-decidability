From Coq Require Import List Vector VectorSpec ZArith Lia Program.Equality.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Contexts RunOrder.

Definition zvec_difference {d} (lower upper : NVec d) : ZVec d :=
  Vector.map2 Z.sub (nvec_to_zvec upper) (nvec_to_zvec lower).

Definition nvec_difference_checked {d} (lower upper : NVec d) : option (NVec d) :=
  zvec_to_nvec (zvec_difference lower upper).

Lemma nvec_difference_checked_correct : forall d (lower upper : NVec d),
    nvec_le lower upper ->
    exists delta,
      nvec_difference_checked lower upper = Some delta /\
      upper = nvec_add lower delta.
Proof.
  intros d lower upper Hle.
  set (delta := Vector.map2 Nat.sub upper lower).
  assert (Hdifference : zvec_difference lower upper = nvec_to_zvec delta).
  { apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros index index' Heq; subst index'.
    unfold zvec_difference, nvec_to_zvec, delta.
    rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl).
    repeat rewrite (nth_map Z.of_nat _ index index eq_refl).
    rewrite (nth_map2 Nat.sub _ _ index index index eq_refl eq_refl).
    specialize (Hle index). rewrite Nat2Z.inj_sub by exact Hle. lia. }
  exists delta. split.
  - unfold nvec_difference_checked. rewrite Hdifference.
    apply zvec_to_nvec_of_nvec.
  - apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros index index' Heq; subst index'. unfold delta, nvec_add.
    repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
    specialize (Hle index); lia.
Qed.

Lemma nvec_exact_delta : forall d (root left right merged delta : NVec d),
    right = nvec_add root delta ->
    nvec_add root merged = nvec_add left right ->
    merged = nvec_add left delta.
Proof.
  intros d root left right merged delta Hright Hexact; subst right.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  pose proof (f_equal (fun value => Vector.nth value index) Hexact) as Hscalar.
  unfold nvec_add in Hscalar |- *.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in Hscalar.
  rewrite (nth_map2 Nat.add left delta index index index eq_refl eq_refl).
  lia.
Qed.

Lemma apply_action_sum_shift : forall d (action : Action d)
    old_children new_children old_target delta,
    length old_children = length new_children ->
    nvec_sum new_children = nvec_add (nvec_sum old_children) delta ->
    apply_action action old_children = Some old_target ->
    apply_action action new_children = Some (nvec_add old_target delta).
Proof.
  intros d action old_children new_children old_target delta
    Hlength Hsum Happly.
  unfold apply_action in Happly |- *.
  destruct (Nat.eqb (length old_children) (action_arity action))
    eqn:Harity; [|discriminate].
  rewrite <- Hlength, Harity.
  unfold add_displacement in Happly |- *.
  assert (Hold :
    zvec_add (action_offset action) (nvec_to_zvec (nvec_sum old_children)) =
      nvec_to_zvec old_target).
  { apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros index index' Heq; subst index'. unfold nvec_to_zvec.
    rewrite (nth_map Z.of_nat old_target index index eq_refl).
    eapply zvec_to_nvec_sound; eauto. }
  rewrite Hsum, nvec_to_zvec_add, zvec_add_assoc, Hold,
    <- nvec_to_zvec_add.
  apply zvec_to_nvec_of_nvec.
Qed.

Inductive RootEmbed {d} : IRun d -> IRun d -> Prop :=
| root_embed_leaf : forall value,
    RootEmbed (irun_leaf value) (irun_leaf value)
| root_embed_node : forall action left_children right_children
    left_target right_target,
    nvec_le left_target right_target ->
    IRunsEmbed left_children right_children ->
    RootEmbed (irun_node action left_children left_target)
      (irun_node action right_children right_target).

(** For one original node, hereditary positivity is the non-negative total
    effect of the context family below that original subtree.  Prefixes
    internal to an inserted context are executions, but are not themselves
    original nodes.  Applying this predicate recursively at every matched
    child gives the context-family condition of R05. *)
Definition HereditaryContext {d} (root : IRun d)
    (context : IContext d) (matched : IRun d) : Prop :=
  nvec_le (irun_target root) (irun_target (context_plug context matched)).

Lemma iruns_in_split : forall d (run : IRun d) runs,
    IRunsIn run runs ->
    exists before after,
      runs = iruns_append before (iruns_cons run after).
Proof.
  intros d run runs Hin. induction Hin.
  - exists iruns_nil, runs; reflexivity.
  - destruct IHHin as [before [after Heq]]. subst runs.
    exists (iruns_cons other before), after; reflexivity.
Qed.

Lemma embed_decompose_structural : forall d (root whole : IRun d),
    IRunEmbed root whole ->
    exists context matched,
      whole = context_plug context matched /\
      RootEmbed root matched.
Proof.
  intros d root whole Hembed. induction Hembed.
  - exists context_hole, (irun_leaf value). split; [reflexivity|constructor].
  - exists context_hole, (irun_node action right_children right_target).
    split; [reflexivity|constructor; assumption].
  - destruct IHHembed as [inner [matched [Hchild Hroot]]].
    destruct (iruns_in_split d child children H)
      as [before [after Hchildren]].
    exists (context_node action before inner after target), matched.
    split.
    + cbn. rewrite <- Hchild, <- Hchildren; reflexivity.
    + exact Hroot.
Qed.

Lemma embed_decompose : forall d (root whole : IRun d),
    IRunLe root whole ->
    exists context matched,
      whole = context_plug context matched /\
      RootEmbed root matched /\
      HereditaryContext root context matched.
Proof.
  intros d root whole [Htarget Hembed].
  destruct (embed_decompose_structural d root whole Hembed)
    as [context [matched [Hplug Hmatched]]].
  exists context, matched. split; [exact Hplug|].
  split; [exact Hmatched|].
  unfold HereditaryContext. rewrite <- Hplug. exact Htarget.
Qed.

Lemma context_valid_inner : forall d (S : IBVAS d) context run,
    ValidIRun S (context_plug context run) -> ValidIRun S run.
Proof.
  intros d S context; induction context; intros run Hvalid; cbn in Hvalid.
  - exact Hvalid.
  - inversion Hvalid; subst.
    apply IHcontext. eapply valid_iruns_frame_member; eauto.
Qed.

Lemma context_add_target : forall d (context : IContext d) matched replacement delta,
    irun_target replacement = nvec_add (irun_target matched) delta ->
    irun_target (context_plug (context_add delta context) replacement) =
      nvec_add (irun_target (context_plug context matched)) delta.
Proof.
  intros d context; induction context; intros; cbn; assumption || reflexivity.
Qed.

Lemma context_embed : forall d (context : IContext d) left right,
    IRunEmbed left right -> IRunEmbed left (context_plug context right).
Proof.
  intros d context; induction context as
    [|action before inner IH after target]; intros left right Hembed; cbn.
  - exact Hembed.
  - eapply embed_below with (child := context_plug inner right).
    + clear IH. induction before; cbn; [constructor|constructor 2; assumption].
    + now apply IH.
Qed.

Lemma hereditary_context_embed : forall d (root : IRun d) (context : IContext d)
    (matched replacement candidate : IRun d) (delta : NVec d),
    HereditaryContext root context matched ->
    IRunEmbed candidate replacement ->
    irun_target replacement = nvec_add (irun_target matched) delta ->
    nvec_le (irun_target candidate) (nvec_add (irun_target root) delta) ->
    IRunEmbed candidate
      (context_plug (context_add delta context) replacement).
Proof.
  intros d root context matched replacement candidate delta
    Hcontext Hembed Hreplacement Hbound.
  apply context_embed. exact Hembed.
Qed.

Lemma iruns_embed_to_le : forall d (left right : IRuns d),
    IRunsEmbed left right -> IRunsLe left right.
Proof.
  intros d left right Hembed. induction Hembed; cbn; [exact I |].
  split; [split; assumption | exact IHHembed].
Qed.

Lemma iruns_embed_lengths : forall d (left right : IRuns d),
    IRunsEmbed left right ->
    length (iruns_targets left) = length (iruns_targets right).
Proof. intros d left right H; induction H; cbn; congruence. Qed.

Lemma nvec_sum_exact_cons : forall d
    (root left right merged : NVec d)
    (roots lefts rights mergeds : list (NVec d)),
    nvec_add root merged = nvec_add left right ->
    nvec_add (nvec_sum roots) (nvec_sum mergeds) =
      nvec_add (nvec_sum lefts) (nvec_sum rights) ->
    nvec_add (nvec_sum (root :: roots)) (nvec_sum (merged :: mergeds)) =
      nvec_add (nvec_sum (left :: lefts)) (nvec_sum (right :: rights)).
Proof.
  intros. repeat rewrite nvec_sum_rsum in *. cbn in *.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  apply (f_equal (fun value => Vector.nth value index)) in H.
  apply (f_equal (fun value => Vector.nth value index)) in H0.
  unfold nvec_add in *.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl) in *.
  lia.
Qed.

Lemma lift_local_amalgamation : forall d (S : IBVAS d)
    (root left right left_match right_match local_merge : IRun d)
    (left_context right_context : IContext d),
    left = context_plug left_context left_match ->
    right = context_plug right_context right_match ->
    HereditaryContext root left_context left_match ->
    HereditaryContext root right_context right_match ->
    ValidIRun S left -> ValidIRun S right -> ValidIRun S local_merge ->
    IRunLe root left -> IRunLe root right ->
    IRunLe root left_match -> IRunLe root right_match ->
    IRunLe left_match local_merge -> IRunLe right_match local_merge ->
    nvec_add (irun_target root) (irun_target local_merge) =
      nvec_add (irun_target left_match) (irun_target right_match) ->
    exists merged,
      ValidIRun S merged /\ IRunLe left merged /\ IRunLe right merged /\
      nvec_add (irun_target root) (irun_target merged) =
        nvec_add (irun_target left) (irun_target right).
Proof.
  intros d S root left right left_match right_match local_merge
    left_context right_context Hleft_eq Hright_eq Hleft_context Hright_context
    Hleft_valid Hright_valid Hmerge_valid Hroot_left Hroot_right
    Hroot_left_match Hroot_right_match Hleft_merge Hright_merge Hexact.
  destruct (nvec_difference_checked_correct d
    (irun_target left_match) (irun_target local_merge) (proj1 Hleft_merge))
    as [left_delta [_ Hmerge_target]].
  assert (Hright_match_delta :
      irun_target right_match = nvec_add (irun_target root) left_delta).
  { apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros index index' Heq; subst index'.
    apply (f_equal (fun value => Vector.nth value index)) in Hexact.
    apply (f_equal (fun value => Vector.nth value index)) in Hmerge_target.
    unfold nvec_add in Hexact, Hmerge_target |- *.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl)
      in Hexact, Hmerge_target |- *.
    rewrite (nth_map2 Nat.add (irun_target root) (irun_target local_merge)
      index index index eq_refl eq_refl) in Hexact.
    rewrite (nth_map2 Nat.add (irun_target left_match) (irun_target right_match)
      index index index eq_refl eq_refl) in Hexact.
    rewrite (nth_map2 Nat.add (irun_target left_match) left_delta
      index index index eq_refl eq_refl) in Hmerge_target.
    rewrite (nth_map2 Nat.add (irun_target root) left_delta
      index index index eq_refl eq_refl).
    lia. }
  assert (Hleft_context_valid :
      ValidIRun S (context_plug left_context left_match)).
  { rewrite <- Hleft_eq; exact Hleft_valid. }
  destruct (context_lift d S left_context left_match local_merge left_delta
    Hleft_context_valid Hmerge_valid Hleft_merge Hmerge_target)
    as [Htau_valid [Hleft_tau Htau_target]].
  rewrite <- Hleft_eq in Hleft_tau, Htau_target.
  set (tau := context_plug (context_add left_delta left_context) local_merge)
    in Htau_valid, Hleft_tau, Htau_target |- *.
  assert (Hright_match_tau_target :
      nvec_le (irun_target right_match) (irun_target tau)).
  { rewrite Hright_match_delta, Htau_target.
    intro index. unfold nvec_add.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
    pose proof (proj1 Hroot_left index) as Hle.
    exact (proj1 (Nat.add_le_mono_r _ _ _) Hle). }
  assert (Hright_match_tau_embed : IRunEmbed right_match tau).
  { subst tau. eapply hereditary_context_embed with
      (root := root) (matched := left_match) (delta := left_delta).
    - exact Hleft_context.
    - exact (proj2 Hright_merge).
    - exact Hmerge_target.
    - rewrite Hright_match_delta; apply nvec_le_refl. }
  assert (Hright_match_tau : IRunLe right_match tau).
  { split; assumption. }
  destruct (nvec_difference_checked_correct d
    (irun_target right_match) (irun_target tau) Hright_match_tau_target)
    as [right_delta [_ Htau_from_right]].
  assert (Hleft_root_delta :
      irun_target left = nvec_add (irun_target root) right_delta).
  { apply (proj1 (Vector.eq_nth_iff nat d _ _)).
    intros index index' Heq; subst index'.
    apply (f_equal (fun value => Vector.nth value index)) in Htau_target.
    apply (f_equal (fun value => Vector.nth value index)) in Htau_from_right.
    apply (f_equal (fun value => Vector.nth value index)) in Hright_match_delta.
    unfold nvec_add in Htau_target, Htau_from_right,
      Hright_match_delta |- *.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl)
      in Htau_target, Htau_from_right, Hright_match_delta |- *.
    rewrite (nth_map2 Nat.add (irun_target left) left_delta
      index index index eq_refl eq_refl) in Htau_target.
    rewrite (nth_map2 Nat.add (irun_target right_match) right_delta
      index index index eq_refl eq_refl) in Htau_from_right.
    rewrite (nth_map2 Nat.add (irun_target root) left_delta
      index index index eq_refl eq_refl) in Hright_match_delta.
    rewrite (nth_map2 Nat.add (irun_target root) right_delta
      index index index eq_refl eq_refl).
    lia. }
  assert (Hright_context_valid :
      ValidIRun S (context_plug right_context right_match)).
  { rewrite <- Hright_eq; exact Hright_valid. }
  destruct (context_lift d S right_context right_match tau right_delta
    Hright_context_valid Htau_valid Hright_match_tau Htau_from_right)
    as [Hfinal_valid [Hright_final Hfinal_target]].
  rewrite <- Hright_eq in Hright_final, Hfinal_target.
  set (final := context_plug (context_add right_delta right_context) tau)
    in Hfinal_valid, Hright_final, Hfinal_target |- *.
  assert (Hleft_final_target :
      nvec_le (irun_target left) (irun_target final)).
  { rewrite Hleft_root_delta, Hfinal_target.
    intro index. unfold nvec_add.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
    pose proof (proj1 Hroot_right index) as Hle.
    exact (proj1 (Nat.add_le_mono_r _ _ _) Hle). }
  assert (Hleft_final_embed : IRunEmbed left final).
  { subst final. eapply hereditary_context_embed with
      (root := root) (matched := right_match) (delta := right_delta).
    - exact Hright_context.
    - exact (proj2 Hleft_tau).
    - exact Htau_from_right.
    - rewrite Hleft_root_delta; apply nvec_le_refl. }
  exists final. split; [exact Hfinal_valid |].
  split; [split; assumption |].
  split; [exact Hright_final |].
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  apply (f_equal (fun value => Vector.nth value index)) in Hfinal_target.
  apply (f_equal (fun value => Vector.nth value index)) in Hleft_root_delta.
  unfold nvec_add in Hfinal_target, Hleft_root_delta |- *.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl)
    in Hfinal_target, Hleft_root_delta |- *.
  rewrite (nth_map2 Nat.add (irun_target right) right_delta
    index index index eq_refl eq_refl) in Hfinal_target.
  rewrite (nth_map2 Nat.add (irun_target root) right_delta
    index index index eq_refl eq_refl) in Hleft_root_delta.
  rewrite (nth_map2 Nat.add (irun_target root) (irun_target final)
    index index index eq_refl eq_refl).
  rewrite (nth_map2 Nat.add (irun_target left) (irun_target right)
    index index index eq_refl eq_refl).
  lia.
Qed.

(* The main proof is a simultaneous induction on the common run and its
   ordered list of children. *)
Lemma iruns_le_lengths : forall d (left right : IRuns d),
    IRunsLe left right ->
    length (iruns_targets left) = length (iruns_targets right).
Proof.
  intros d left; induction left; intros right Hle; destruct right; try contradiction;
    cbn in *; [reflexivity |]. destruct Hle; f_equal; auto.
Qed.

Lemma run_amalgamation_mutual : forall d,
  (forall root : IRun d, forall (S : IBVAS d) left right,
    ValidIRun S root -> ValidIRun S left -> ValidIRun S right ->
    IRunLe root left -> IRunLe root right ->
    exists merged,
      ValidIRun S merged /\ IRunLe left merged /\ IRunLe right merged /\
      nvec_add (irun_target root) (irun_target merged) =
        nvec_add (irun_target left) (irun_target right)) /\
  (forall roots : IRuns d, forall (S : IBVAS d) lefts rights,
    ValidIRuns S roots -> ValidIRuns S lefts -> ValidIRuns S rights ->
    IRunsLe roots lefts -> IRunsLe roots rights ->
    exists mergeds,
      ValidIRuns S mergeds /\ IRunsLe lefts mergeds /\ IRunsLe rights mergeds /\
      nvec_add (nvec_sum (iruns_targets roots))
        (nvec_sum (iruns_targets mergeds)) =
      nvec_add (nvec_sum (iruns_targets lefts))
        (nvec_sum (iruns_targets rights))).
Proof.
  intro d. apply IRun_IRuns_ind.
  - intros value S left right Hroot_valid Hleft_valid Hright_valid
      [Hroot_left Eleft] [Hroot_right Eright].
    destruct (embed_decompose d (irun_leaf value) left
      (conj Hroot_left Eleft))
      as [left_context [left_match [Hleft_eq [Hleft_root Hleft_context]]]].
    destruct (embed_decompose d (irun_leaf value) right
      (conj Hroot_right Eright))
      as [right_context [right_match [Hright_eq [Hright_root Hright_context]]]].
    inversion Hleft_root; subst. inversion Hright_root; subst.
    eapply (lift_local_amalgamation d S (irun_leaf value)
      (context_plug left_context (irun_leaf value))
      (context_plug right_context (irun_leaf value))
      (irun_leaf value) (irun_leaf value) (irun_leaf value)
      left_context right_context).
    + reflexivity.
    + reflexivity.
    + exact Hleft_context.
    + exact Hright_context.
    + exact Hleft_valid.
    + exact Hright_valid.
    + exact Hroot_valid.
    + split; assumption.
    + split; assumption.
    + apply irun_le_refl.
    + apply irun_le_refl.
    + apply irun_le_refl.
    + apply irun_le_refl.
    + reflexivity.
  - intros action root_children IHchildren root_target S left right
      Hroot_valid Hleft_valid Hright_valid
      [Hroot_left Eleft] [Hroot_right Eright].
    destruct (embed_decompose d
      (irun_node action root_children root_target) left
      (conj Hroot_left Eleft))
      as [left_context [left_match [Hleft_eq [Hleft_root Hleft_context]]]].
    destruct (embed_decompose d
      (irun_node action root_children root_target) right
      (conj Hroot_right Eright))
      as [right_context [right_match [Hright_eq [Hright_root Hright_context]]]].
    inversion Hleft_root as
      [|? ? left_children ? left_target Hroot_left_target Eleft_children]; subst.
    inversion Hright_root as
      [|? ? right_children ? right_target Hroot_right_target Eright_children]; subst.
    assert (Hleft_match_valid :
      ValidIRun S (irun_node action left_children left_target)).
    { eapply context_valid_inner. exact Hleft_valid. }
    assert (Hright_match_valid :
      ValidIRun S (irun_node action right_children right_target)).
    { eapply context_valid_inner. exact Hright_valid. }
    inversion Hroot_valid as
      [|? ? ? Haction Hroot_children_valid Hroot_apply]; subst.
    inversion Hleft_match_valid as
      [|? ? ? _ Hleft_children_valid Hleft_apply]; subst.
    inversion Hright_match_valid as
      [|? ? ? _ Hright_children_valid Hright_apply]; subst.
    destruct (IHchildren S left_children right_children
      Hroot_children_valid Hleft_children_valid Hright_children_valid
      (iruns_embed_to_le d root_children left_children Eleft_children)
      (iruns_embed_to_le d root_children right_children Eright_children))
      as [merged_children [Hmerged_children_valid
        [Hleft_children_merge [Hright_children_merge Hchildren_exact]]]].
    pose proof (iruns_targets_le d root_children right_children
      (iruns_embed_to_le d root_children right_children Eright_children))
      as Hroot_right_targets.
    destruct (nvec_difference_checked_correct d
      (nvec_sum (iruns_targets root_children))
      (nvec_sum (iruns_targets right_children))
      (nvec_sum_le d _ _ Hroot_right_targets))
      as [delta [_ Hright_sum]].
    assert (Hmerged_sum :
      nvec_sum (iruns_targets merged_children) =
      nvec_add (nvec_sum (iruns_targets left_children)) delta).
    { eapply nvec_exact_delta; eauto. }
    assert (Hmerged_apply :
      apply_action action (iruns_targets merged_children) =
        Some (nvec_add left_target delta)).
    { eapply apply_action_sum_shift.
      - eapply iruns_le_lengths; exact Hleft_children_merge.
      - exact Hmerged_sum.
      - exact Hleft_apply. }
    set (local_merge := irun_node action merged_children
      (nvec_add left_target delta)).
    assert (Hlocal_valid : ValidIRun S local_merge).
    { subst local_merge. econstructor; eauto. }
    assert (Hleft_local :
      IRunLe (irun_node action left_children left_target) local_merge).
    { subst local_merge. eapply root_same_action_mono; eauto. }
    assert (Hright_local :
      IRunLe (irun_node action right_children right_target) local_merge).
    { subst local_merge. eapply root_same_action_mono; eauto. }
    assert (Hright_target : right_target = nvec_add root_target delta).
    { assert (Hshift := apply_action_sum_shift d action
        (iruns_targets root_children) (iruns_targets right_children)
        root_target delta
        (iruns_embed_lengths d root_children right_children Eright_children)
        Hright_sum Hroot_apply).
      rewrite Hright_apply in Hshift; inversion Hshift; reflexivity. }
    assert (Hlocal_exact :
      nvec_add root_target (irun_target local_merge) =
        nvec_add left_target right_target).
    { subst local_merge. cbn. rewrite Hright_target.
      apply (proj1 (Vector.eq_nth_iff nat d _ _)).
      intros index index' Heq; subst index'. unfold nvec_add.
      repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
      lia. }
    eapply lift_local_amalgamation with
      (left_match := irun_node action left_children left_target)
      (right_match := irun_node action right_children right_target)
      (local_merge := local_merge)
      (left_context := left_context) (right_context := right_context);
      try eassumption; try reflexivity;
      try (split; [assumption | constructor; assumption]).
    all: split; assumption.
  - intros S lefts rights Hroot_valid Hleft_valid Hright_valid Hleft Hright.
    destruct lefts; try contradiction. destruct rights; try contradiction.
    exists iruns_nil. split; [constructor |]. split; [exact I |].
    split; [exact I | reflexivity].
  - intros root IHroot roots IHroots S lefts rights
      Hroot_valid Hleft_valid Hright_valid Hleft Hright.
    destruct lefts; try contradiction. destruct rights; try contradiction.
    cbn in Hleft, Hright. destruct Hleft as [Hleft_head Hleft_tail].
    destruct Hright as [Hright_head Hright_tail].
    inversion Hroot_valid; subst. inversion Hleft_valid; subst.
    inversion Hright_valid; subst.
    destruct (IHroot S i i0 H1 H3 H5 Hleft_head Hright_head)
      as [merged [Hmerged_valid [Hleft_merged [Hright_merged Hhead_exact]]]].
    destruct (IHroots S lefts rights H2 H4 H6 Hleft_tail Hright_tail)
      as [mergeds [Hmergeds_valid
        [Hlefts_merged [Hrights_merged Htail_exact]]]].
    exists (iruns_cons merged mergeds). split.
    + constructor; assumption.
    + split.
      * cbn; split; assumption.
      * split.
        -- cbn; split; assumption.
        -- cbn. eapply nvec_sum_exact_cons; eauto.
Qed.

Theorem run_amalgamation : forall d (S : IBVAS d) (root left right : IRun d),
    ValidIRun S root -> ValidIRun S left -> ValidIRun S right ->
    IRunLe root left -> IRunLe root right ->
    exists merged,
      ValidIRun S merged /\ IRunLe left merged /\ IRunLe right merged /\
      nvec_add (irun_target root) (irun_target merged) =
        nvec_add (irun_target left) (irun_target right).
Proof. intros; eapply (proj1 (run_amalgamation_mutual d)); eauto. Qed.
