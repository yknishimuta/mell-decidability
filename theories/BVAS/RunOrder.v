From Coq Require Import List Vector VectorSpec Arith.PeanoNat ZArith Lia.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Contexts.

Definition nvec_le {d} (left right : NVec d) : Prop :=
  forall index, Vector.nth left index <= Vector.nth right index.

Definition NVecListLe {d} (left right : list (NVec d)) : Prop :=
  List.Forall2 nvec_le left right.

Lemma nvec_le_refl : forall d (value : NVec d), nvec_le value value.
Proof. intros d value index; reflexivity. Qed.

Lemma nvec_le_trans : forall d (x y z : NVec d),
    nvec_le x y -> nvec_le y z -> nvec_le x z.
Proof. intros d x y z Hxy Hyz index; eapply Nat.le_trans; eauto. Qed.

Lemma nvec_le_add_right : forall d (value delta : NVec d),
    nvec_le value (nvec_add value delta).
Proof.
  intros d value delta index. unfold nvec_add.
  rewrite (nth_map2 Nat.add value delta index index index eq_refl eq_refl).
  lia.
Qed.

Lemma fold_left_nvec_add_le : forall d (left right : list (NVec d))
    left_acc right_acc,
    NVecListLe left right -> nvec_le left_acc right_acc ->
    nvec_le (List.fold_left nvec_add left left_acc)
      (List.fold_left nvec_add right right_acc).
Proof.
  intros d left right left_acc right_acc Hle.
  revert left_acc right_acc. induction Hle as [|x y xs ys Hxy Hxys IH];
    intros left_acc right_acc Hacc; cbn.
  - exact Hacc.
  - apply IH. intro index. unfold nvec_add.
    repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
    specialize (Hxy index); specialize (Hacc index); lia.
Qed.

Lemma nvec_sum_le : forall d (left right : list (NVec d)),
    NVecListLe left right -> nvec_le (nvec_sum left) (nvec_sum right).
Proof.
  intros d left right Hle. unfold nvec_sum.
  apply fold_left_nvec_add_le; [exact Hle | apply nvec_le_refl].
Qed.

Lemma zvec_to_nvec_sound : forall d (value : ZVec d) result,
    zvec_to_nvec value = Some result ->
    forall index, Vector.nth value index = Z.of_nat (Vector.nth result index).
Proof.
  intros d value result Hdecode index.
  unfold zvec_to_nvec in Hdecode.
  destruct (zvec_nonnegative value) eqn:Hnonnegative; inversion Hdecode; subst.
  rewrite (nth_map Z.to_nat value index index eq_refl).
  symmetry. apply Z2Nat.id.
  unfold zvec_nonnegative in Hnonnegative.
  apply forallb_forall with (x := Vector.nth value index) in Hnonnegative.
  - apply Z.geb_le in Hnonnegative; exact Hnonnegative.
  - apply (proj1 (to_list_In _ _ _ _)). apply In_nth.
Qed.

Lemma zvec_to_nvec_of_nvec : forall d (value : NVec d),
    zvec_to_nvec (nvec_to_zvec value) = Some value.
Proof.
  intros d value. unfold zvec_to_nvec, zvec_nonnegative.
  assert (Hnonnegative :
    forallb (fun z : Z => Z.geb z 0)
      (Vector.to_list (nvec_to_zvec value)) = true).
  { unfold nvec_to_zvec. rewrite to_list_map.
    apply forallb_forall. intros z Hz.
    apply in_map_iff in Hz. destruct Hz as [n [Hz _]]. subst z.
    apply Z.geb_le; lia. }
  rewrite Hnonnegative.
  enough (Vector.map Z.to_nat (nvec_to_zvec value) = value) as -> by reflexivity.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  unfold nvec_to_zvec.
  repeat rewrite (nth_map _ _ index index eq_refl).
  apply Nat2Z.id.
Qed.

Lemma nvec_add_assoc : forall d (x y z : NVec d),
    nvec_add (nvec_add x y) z = nvec_add x (nvec_add y z).
Proof.
  intros d x y z. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma nvec_add_zero_left : forall d (value : NVec d),
    nvec_add (nvec_zero d) value = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add, nvec_zero.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (const_nth nat 0 d index); lia.
Qed.

Lemma nvec_add_zero_right : forall d (value : NVec d),
    nvec_add value (nvec_zero d) = value.
Proof.
  intros d value. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add, nvec_zero.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (const_nth nat 0 d index); lia.
Qed.

Fixpoint nvec_rsum {d} (values : list (NVec d)) : NVec d :=
  match values with
  | List.nil => nvec_zero d
  | List.cons value values' => nvec_add value (nvec_rsum values')
  end.

Lemma fold_left_nvec_add : forall d (values : list (NVec d)) accumulator,
    List.fold_left nvec_add values accumulator =
      nvec_add accumulator (nvec_rsum values).
Proof.
  intros d values; induction values as [|value values IH]; intro accumulator; cbn.
  - symmetry; apply nvec_add_zero_right.
  - rewrite IH, nvec_add_assoc. reflexivity.
Qed.

Lemma nvec_sum_rsum : forall d (values : list (NVec d)),
    nvec_sum values = nvec_rsum values.
Proof.
  intros d values. unfold nvec_sum. rewrite fold_left_nvec_add.
  apply nvec_add_zero_left.
Qed.

Lemma nvec_rsum_app : forall d (left right : list (NVec d)),
    nvec_rsum (left ++ right) = nvec_add (nvec_rsum left) (nvec_rsum right).
Proof.
  intros d left; induction left as [|value left IH]; intro right; cbn.
  - symmetry; apply nvec_add_zero_left.
  - rewrite IH, nvec_add_assoc; reflexivity.
Qed.

Lemma nvec_sum_frame_shift : forall d (before after : list (NVec d))
    (left right delta : NVec d),
    right = nvec_add left delta ->
    nvec_sum (before ++ right :: after) =
      nvec_add (nvec_sum (before ++ left :: after)) delta.
Proof.
  intros d before after left right delta Hright. subst right.
  repeat rewrite nvec_sum_rsum.
  repeat rewrite nvec_rsum_app. cbn.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma nvec_to_zvec_add : forall d (left right : NVec d),
    nvec_to_zvec (nvec_add left right) =
      zvec_add (nvec_to_zvec left) (nvec_to_zvec right).
Proof.
  intros d left right. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  unfold nvec_to_zvec, nvec_add, zvec_add.
  rewrite (nth_map Z.of_nat _ index index eq_refl),
    (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (nth_map2 Z.add _ _ index index index eq_refl eq_refl).
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl).
  apply Nat2Z.inj_add.
Qed.

Lemma zvec_add_assoc : forall d (x y z : ZVec d),
    zvec_add x (zvec_add y z) = zvec_add (zvec_add x y) z.
Proof.
  intros d x y z. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'. unfold zvec_add.
  repeat rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma apply_action_frame_shift : forall d (action : Action d)
    before after left right target delta,
    right = nvec_add left delta ->
    apply_action action (before ++ left :: after) = Some target ->
    apply_action action (before ++ right :: after) =
      Some (nvec_add target delta).
Proof.
  intros d action before after left right target delta Hright Happly.
  unfold apply_action in Happly |- *.
  destruct (Nat.eqb (length (before ++ left :: after))
    (action_arity action)) eqn:Harity; [|discriminate].
  assert (Hlength : length (before ++ right :: after) =
      length (before ++ left :: after)).
  { repeat rewrite length_app; cbn; reflexivity. }
  rewrite Hlength, Harity.
  unfold add_displacement in Happly |- *.
  assert (Hold :
    zvec_add (action_offset action)
      (nvec_to_zvec (nvec_sum (before ++ left :: after))) =
    nvec_to_zvec target).
  { apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros index index' Heq; subst index'.
    unfold nvec_to_zvec.
    rewrite (nth_map Z.of_nat target index index eq_refl).
    apply zvec_to_nvec_sound with
      (value := zvec_add (action_offset action)
        (nvec_to_zvec (nvec_sum (before ++ left :: after)))).
    exact Happly. }
  rewrite (nvec_sum_frame_shift d before after left right delta Hright),
    nvec_to_zvec_add, zvec_add_assoc, Hold, <- nvec_to_zvec_add.
  apply zvec_to_nvec_of_nvec.
Qed.

Lemma add_displacement_mono : forall d offset
    (left right : list (NVec d)) left_target right_target,
    NVecListLe left right ->
    add_displacement offset left = Some left_target ->
    add_displacement offset right = Some right_target ->
    nvec_le left_target right_target.
Proof.
  intros d offset left right left_target right_target Hle Hleft Hright index.
  unfold add_displacement in Hleft, Hright.
  pose proof (zvec_to_nvec_sound _ _ _ Hleft index) as Eleft.
  pose proof (zvec_to_nvec_sound _ _ _ Hright index) as Eright.
  unfold zvec_add, nvec_to_zvec in Eleft, Eright.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (nth_map Z.of_nat _ index index eq_refl) in Eleft.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (nth_map Z.of_nat _ index index eq_refl) in Eright.
  pose proof (nvec_sum_le d left right Hle index) as Hsum.
  lia.
Qed.

Lemma apply_action_mono : forall d (action : Action d)
    left_children right_children left_target right_target,
    NVecListLe left_children right_children ->
    apply_action action left_children = Some left_target ->
    apply_action action right_children = Some right_target ->
    nvec_le left_target right_target.
Proof.
  intros d action left_children right_children left_target right_target
    Hle Hleft Hright.
  unfold apply_action in Hleft, Hright.
  destruct (Nat.eqb (length left_children) (action_arity action));
    [|discriminate].
  destruct (Nat.eqb (length right_children) (action_arity action));
    [|discriminate].
  eapply add_displacement_mono; eauto.
Qed.

Inductive IRunsIn {d} (run : IRun d) : IRuns d -> Prop :=
| iruns_in_here : forall runs, IRunsIn run (iruns_cons run runs)
| iruns_in_later : forall other runs,
    IRunsIn run runs -> IRunsIn run (iruns_cons other runs).

Inductive IRunEmbed {d} : IRun d -> IRun d -> Prop :=
| embed_leaf : forall value, IRunEmbed (irun_leaf value) (irun_leaf value)
| embed_node : forall action left_children right_children left_target right_target,
    nvec_le left_target right_target ->
    IRunsEmbed left_children right_children ->
    IRunEmbed (irun_node action left_children left_target)
      (irun_node action right_children right_target)
| embed_below : forall small action children target child,
    IRunsIn child children -> IRunEmbed small child ->
    IRunEmbed small (irun_node action children target)
with IRunsEmbed {d} : IRuns d -> IRuns d -> Prop :=
| embed_runs_nil : IRunsEmbed iruns_nil iruns_nil
| embed_runs_cons : forall left right lefts rights,
    nvec_le (irun_target left) (irun_target right) ->
    IRunEmbed left right -> IRunsEmbed lefts rights ->
    IRunsEmbed (iruns_cons left lefts) (iruns_cons right rights).

Scheme IRunEmbed_ind' := Induction for IRunEmbed Sort Prop
with IRunsEmbed_ind' := Induction for IRunsEmbed Sort Prop.
Combined Scheme IRunEmbed_IRunsEmbed_mutind
  from IRunEmbed_ind', IRunsEmbed_ind'.

Definition IRunLe {d} (left right : IRun d) : Prop :=
  nvec_le (irun_target left) (irun_target right) /\ IRunEmbed left right.

Fixpoint IRunsLe {d} (left right : IRuns d) : Prop :=
  match left, right with
  | iruns_nil, iruns_nil => True
  | iruns_cons left_run left_runs, iruns_cons right_run right_runs =>
      IRunLe left_run right_run /\ IRunsLe left_runs right_runs
  | _, _ => False
  end.

Lemma irun_embed_refl : forall d (run : IRun d), IRunEmbed run run
with iruns_embed_refl : forall d (runs : IRuns d), IRunsEmbed runs runs.
Proof.
  - intros d run; destruct run.
    + constructor.
    + constructor; [apply nvec_le_refl | apply iruns_embed_refl].
  - intros d runs; destruct runs.
    + constructor.
    + constructor.
      * apply nvec_le_refl.
      * apply irun_embed_refl.
      * apply iruns_embed_refl.
Qed.

Theorem irun_le_refl : forall d (run : IRun d), IRunLe run run.
Proof. intros d run; split; [apply nvec_le_refl | apply irun_embed_refl]. Qed.

Lemma irun_embed_trans_properties : forall d : nat,
  (forall (middle right : IRun d) (embedding : IRunEmbed middle right),
    forall left : IRun d,
      IRunEmbed left middle -> IRunEmbed left right) /\
  (forall (middles rights : IRuns d) (embedding : IRunsEmbed middles rights),
    (forall lefts : IRuns d,
      IRunsEmbed lefts middles -> IRunsEmbed lefts rights) /\
    (forall child : IRun d, IRunsIn child middles ->
      exists (right_child : IRun d)
          (child_embedding : IRunEmbed child right_child),
        nvec_le (irun_target child) (irun_target right_child) /\
        IRunsIn right_child rights /\
        forall small : IRun d,
          IRunEmbed small child ->
          IRunEmbed small right_child)).
Proof.
  intro d. apply IRunEmbed_IRunsEmbed_mutind.
  - intros value left Hleft. inversion Hleft; constructor.
  - intros action middle_children right_children middle_target right_target
      Htargets Echildren [IHchildren IHmember] left Hleft.
    inversion Hleft as
      [value
      |action0 left_children middle_children0 left_target middle_target0
          Hnode_targets Eleft
      |small action0 children0 target0 child0 Hinleft Eleft]; subst.
    + constructor.
      * eapply nvec_le_trans; eauto.
      * apply IHchildren; assumption.
    + destruct (IHmember _ Hinleft) as
        [right_child [Echild [Hchild [Hin Htrans]]]].
      eapply embed_below.
      * exact Hin.
      * eapply Htrans; eauto.
  - intros middle action children target child Hin Echild IH left Hleft.
    eapply (embed_below left action children target child).
    + exact Hin.
    + eapply IH; eauto.
  - split.
    + intros lefts Hlefts; inversion Hlefts; constructor.
    + intros child Hin; inversion Hin.
  - intros middle right middles rights Hhead Ehead IHhead Etail
      [IHtail IHmember] . split.
    + intros lefts Hlefts. inversion Hlefts; subst.
      constructor.
      * eapply nvec_le_trans; eauto.
      * eapply IHhead; eauto.
      * eapply IHtail; eauto.
    + intros child Hin. inversion Hin as [runs0|other runs0 Hin_tail]; subst.
      * exists right, Ehead. split; [exact Hhead |]. split; [constructor |].
        intros small Hsmall; eapply IHhead; eauto.
      * destruct (IHmember _ Hin_tail) as
          [right_child [Echild [Hchild [Hin_right Htrans]]]].
        exists right_child, Echild. split; [exact Hchild |].
        split; [now constructor 2 | exact Htrans].
Qed.

Theorem irun_le_trans : forall d (left middle right : IRun d),
    IRunLe left middle -> IRunLe middle right -> IRunLe left right.
Proof.
  intros d left middle right [Hlm Elm] [Hmr Emr]. split.
  - eapply nvec_le_trans; eauto.
  - eapply (proj1 (irun_embed_trans_properties d) middle right Emr); eauto.
Qed.

Lemma iruns_le_embed : forall d (left right : IRuns d),
    IRunsLe left right -> IRunsEmbed left right.
Proof.
  intros d left; induction left; intros right Hle; destruct right; try contradiction.
  - constructor.
  - cbn in Hle. destruct Hle as [[Htarget Hrun] Hruns].
    constructor.
    + exact Htarget.
    + exact Hrun.
    + apply IHleft; exact Hruns.
Qed.

Lemma iruns_targets_le : forall d (left right : IRuns d),
    IRunsLe left right -> NVecListLe (iruns_targets left) (iruns_targets right).
Proof.
  intros d left; induction left; intros right Hle; destruct right; try contradiction.
  - constructor.
  - cbn in Hle |- *. destruct Hle as [[Htarget _] Htail].
    constructor; [exact Htarget | apply IHleft; exact Htail].
Qed.

Lemma root_same_action_with_target_le : forall d (action : Action d)
    left_children right_children left_target right_target,
    IRunsLe left_children right_children ->
    nvec_le left_target right_target ->
    IRunLe (irun_node action left_children left_target)
      (irun_node action right_children right_target).
Proof.
  intros; split; [assumption |]. constructor.
  - assumption.
  - now apply iruns_le_embed.
Qed.

Theorem root_same_action_mono : forall d (action : Action d)
    left_children right_children left_target right_target,
    IRunsLe left_children right_children ->
    apply_action action (iruns_targets left_children) = Some left_target ->
    apply_action action (iruns_targets right_children) = Some right_target ->
    IRunLe (irun_node action left_children left_target)
      (irun_node action right_children right_target).
Proof.
  intros d action left_children right_children left_target right_target
    Hchildren Hleft Hright.
  apply root_same_action_with_target_le; [exact Hchildren |].
  eapply apply_action_mono; eauto. apply iruns_targets_le; exact Hchildren.
Qed.

Lemma iruns_le_refl : forall d (runs : IRuns d), IRunsLe runs runs.
Proof.
  intros d runs; induction runs; cbn; [exact I | split; [apply irun_le_refl | assumption]].
Qed.

Lemma iruns_frame_mono : forall d (before after : IRuns d) left right,
    IRunLe left right ->
    IRunsLe (iruns_append before (iruns_cons left after))
      (iruns_append before (iruns_cons right after)).
Proof.
  intros d before; induction before; intros after left right Hle; cbn.
  - split; [exact Hle | apply iruns_le_refl].
  - split; [apply irun_le_refl | apply IHbefore; exact Hle].
Qed.

Lemma iruns_targets_append : forall d (left right : IRuns d),
    iruns_targets (iruns_append left right) =
      iruns_targets left ++ iruns_targets right.
Proof.
  intros d left; induction left; intro right; cbn; [reflexivity |].
  rewrite IHleft; reflexivity.
Qed.

Lemma valid_iruns_frame_replace : forall d (S : IBVAS d)
    (before after : IRuns d) old replacement,
    ValidIRuns S (iruns_append before (iruns_cons old after)) ->
    ValidIRun S replacement ->
    ValidIRuns S (iruns_append before (iruns_cons replacement after)).
Proof.
  intros d S before; induction before; intros after old replacement Hold Hnew;
    cbn in *.
  - inversion Hold; subst. constructor; assumption.
  - inversion Hold; subst. constructor; [assumption |].
    eapply IHbefore; eauto.
Qed.

Lemma valid_iruns_frame_member : forall d (S : IBVAS d)
    (before after : IRuns d) run,
    ValidIRuns S (iruns_append before (iruns_cons run after)) ->
    ValidIRun S run.
Proof.
  intros d S before; induction before; intros after run Hvalid; cbn in Hvalid.
  - inversion Hvalid; assumption.
  - inversion Hvalid; subst. eapply IHbefore; eauto.
Qed.

Theorem context_order_lift : forall d (context : IContext d) left right delta,
    IRunLe left right ->
    irun_target right = nvec_add (irun_target left) delta ->
    IRunLe (context_plug context left)
      (context_plug (context_add delta context) right) /\
    irun_target (context_plug (context_add delta context) right) =
      nvec_add (irun_target (context_plug context left)) delta.
Proof.
  intros d context; induction context; intros left right delta Hle Htarget; cbn.
  - split; assumption.
  - split; [|reflexivity].
    apply root_same_action_with_target_le.
    + apply iruns_frame_mono. apply IHcontext; assumption.
    + apply nvec_le_add_right.
Qed.

Theorem context_lift : forall d (S : IBVAS d) (context : IContext d)
    left right delta,
    ValidIRun S (context_plug context left) ->
    ValidIRun S right ->
    IRunLe left right ->
    irun_target right = nvec_add (irun_target left) delta ->
    ValidIRun S (context_plug (context_add delta context) right) /\
    IRunLe (context_plug context left)
      (context_plug (context_add delta context) right) /\
    irun_target (context_plug (context_add delta context) right) =
      nvec_add (irun_target (context_plug context left)) delta.
Proof.
  intros d S context; induction context as
    [|action before inner IH after target];
    intros left right delta Hold Hright Hle Htarget; cbn in *.
  - split; [exact Hright |]. split; [exact Hle | exact Htarget].
  - inversion Hold as [|? ? ? Haction Hchildren Happly]; subst.
    assert (Hinner_old : ValidIRun S (context_plug inner left)).
    { eapply valid_iruns_frame_member; eauto. }
    destruct (IH left right delta Hinner_old Hright Hle Htarget)
      as [Hinner_new [Horder Hinner_target]].
    split.
    + apply valid_irun_node.
      * exact Haction.
      * eapply valid_iruns_frame_replace; eauto.
      * repeat rewrite iruns_targets_append in Happly |- *; cbn in Happly |- *.
        eapply apply_action_frame_shift; eauto.
    + split.
      * apply root_same_action_with_target_le.
        -- apply iruns_frame_mono; exact Horder.
        -- apply nvec_le_add_right.
      * reflexivity.
Qed.
