From Coq Require Import List Vector Lia Arith.PeanoNat Program.Equality
  Classical_Prop ClassicalChoice ClassicalEpsilon Sorting.Permutation.
From KruskalTrees Require Import idx vec ltree.
From KruskalAfProp Require Import af.af af.af_tools.
From KruskalHigmanProp Require Import embeddings.list_embed af.af_list_embed.
From KruskalThmProp Require Import embeddings.ltree_embed kruskal_theorems.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Contexts RunOrder Code.
From Mell.BVASS Require Import Stateful ContextInsertion Code OrderedBridge.
From Mell.Order Require Import AlmostFullBridge CountableFiniteBasis.

Import ListNotations idx_notations.

Fixpoint idx_to_fin {n} (index : idx n) : Fin.t n :=
  match index with
  | idx_fst => Fin.F1
  | idx_nxt tail => Fin.FS (idx_to_fin tail)
  end.

Definition nth_idx {A} (values : list A) (index : idx (length values)) : A :=
  Vector.nth (Vector.of_list values) (idx_to_fin index).

Lemma nth_idx_occurrence : forall A (values : list A) value,
    List.In value values -> exists index, nth_idx values index = value.
Proof.
  intros A values. induction values as [|head tail IH]; intros value Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + exists idx_fst. reflexivity.
    + destruct (IH value Hin) as [index Hindex].
      exists (idx_nxt index). exact Hindex.
Qed.

Definition IRunLabel {d} (S : IBVAS d) :=
  (idx (length (initial_vectors S)) +
   (idx (length (system_actions S)) * (NVec d * list (NVec d))))%type.

Definition IRunNodeLabelLe {d} (S : IBVAS d) :
    (idx (length (system_actions S)) * (NVec d * list (NVec d))) ->
    (idx (length (system_actions S)) * (NVec d * list (NVec d))) -> Prop :=
  fun left right =>
    fst left = fst right /\
    nvec_le (fst (snd left)) (fst (snd right)) /\
    list_embed nvec_le (snd (snd left)) (snd (snd right)).

Definition IRunLabelLe {d} (S : IBVAS d) :
    IRunLabel S -> IRunLabel S -> Prop :=
  fun left right =>
    match left, right with
    | inl left_index, inl right_index => left_index = right_index
    | inr left_node, inr right_node => IRunNodeLabelLe S left_node right_node
    | _, _ => False
    end.

Lemma irun_label_almost_full : forall d (S : IBVAS d),
    af (IRunLabelLe S).
Proof.
  intros d S. unfold IRunLabelLe, IRunNodeLabelLe.
  apply af_sum.
  - apply af_idx.
  - eapply af_mono with (R := fun '(li, (lt, lc)) '(ri, (rt, rc)) =>
        li = ri /\ (nvec_le lt rt /\ list_embed nvec_le lc rc)).
    + intros [li [lt lc]] [ri [rt rc]]. cbn. tauto.
    + pose proof (nvec_le_almost_full d) as Hvec.
      pose proof (af_list_embed Hvec) as Hlist.
      pose proof (af_product Hvec Hlist) as Hpair.
      pose proof (af_product (af_idx (length (system_actions S))) Hpair)
        as Hnode.
      eapply af_mono; [|exact Hnode].
      intros [li [lt lc]] [ri [rt rc]] Hrel. exact Hrel.
Qed.

Inductive DecoratesIRun {d} (S : IBVAS d) :
    ltree (IRunLabel S) -> IRun d -> Prop :=
| decorates_irun_leaf : forall index,
    DecoratesIRun S (ltree_cons (inl index) [])
      (irun_leaf (nth_idx (initial_vectors S) index))
| decorates_irun_node : forall index target children child_trees,
    DecoratesIRuns S child_trees children ->
    List.length (iruns_targets children) =
      action_arity (nth_idx (system_actions S) index) ->
    DecoratesIRun S
      (ltree_cons (inr (index, (target, iruns_targets children))) child_trees)
      (irun_node (nth_idx (system_actions S) index) children target)
with DecoratesIRuns {d} (S : IBVAS d) :
    list (ltree (IRunLabel S)) -> IRuns d -> Prop :=
| decorates_iruns_nil : DecoratesIRuns S [] iruns_nil
| decorates_iruns_cons : forall tree trees run runs,
    DecoratesIRun S tree run -> DecoratesIRuns S trees runs ->
    DecoratesIRuns S (tree :: trees) (iruns_cons run runs).

Scheme DecoratesIRun_ind' := Induction for DecoratesIRun Sort Prop
with DecoratesIRuns_ind' := Induction for DecoratesIRuns Sort Prop.
Combined Scheme DecoratesIRun_mutind from DecoratesIRun_ind', DecoratesIRuns_ind'.
Combined Scheme ValidIRun_mutind_local from ValidIRun_ind', ValidIRuns_ind'.

Lemma valid_irun_decorated_mut : forall d (S : IBVAS d),
  (forall run, ValidIRun S run -> exists tree, DecoratesIRun S tree run) /\
  (forall runs, ValidIRuns S runs -> exists trees, DecoratesIRuns S trees runs).
Proof.
  intros d S. apply ValidIRun_mutind_local.
  - intros value Hin.
    destruct (nth_idx_occurrence _ _ _ Hin) as [index Hindex].
    exists (ltree_cons (inl index) []). rewrite <- Hindex. constructor.
  - intros action children target Haction Hchildren IHchildren Happly.
    destruct IHchildren as [trees Htrees].
    destruct (nth_idx_occurrence _ _ _ Haction) as [index Hindex].
    exists (ltree_cons (inr (index, (target, iruns_targets children))) trees).
    rewrite <- Hindex. constructor.
    + exact Htrees.
    + rewrite Hindex. unfold apply_action in Happly.
      destruct (Nat.eqb (List.length (iruns_targets children))
        (action_arity action)) eqn:Harity; [now apply Nat.eqb_eq|discriminate].
  - exists []. constructor.
  - intros run runs Hrun IHrun Hruns IHruns.
    destruct IHrun as [tree Htree]. destruct IHruns as [trees Htrees].
    exists (tree :: trees). constructor; assumption.
Qed.

Lemma decorates_iruns_lengths : forall d (S : IBVAS d) trees runs,
    DecoratesIRuns S trees runs ->
    List.length trees = List.length (iruns_targets runs).
Proof. intros d S trees runs H; induction H; cbn; congruence. Qed.

Lemma list_embed_equal_length_Forall2 : forall A B (R : A -> B -> Prop) left right,
    list_embed R left right -> List.length left = List.length right ->
    List.Forall2 R left right.
Proof.
  intros A B R left right H. induction H; intro Hlength; cbn in Hlength.
  - constructor.
  - constructor; [exact H|]. apply IHlist_embed. lia.
  - exfalso. pose proof (list_embed_length H). cbn in Hlength. lia.
Qed.

Lemma decorated_tree_member : forall d (S : IBVAS d) trees runs tree,
    DecoratesIRuns S trees runs -> List.In tree trees ->
    exists run, IRunsIn run runs /\ DecoratesIRun S tree run.
Proof.
  intros d S trees runs tree Hdecor. induction Hdecor; cbn.
  - contradiction.
  - intros [<-|Hin].
    + exists run. split; [constructor|exact H].
    + destruct (IHHdecor Hin) as [found [Hfound Htree]].
      exists found. split; [constructor 2; exact Hfound|exact Htree].
Qed.

Lemma decorated_member_of_run : forall d (S : IBVAS d) label trees run tree,
    DecoratesIRun S (ltree_cons label trees) run -> List.In tree trees ->
    exists action runs target child,
      run = irun_node action runs target /\ IRunsIn child runs /\
      DecoratesIRun S tree child.
Proof.
  intros d S label trees run tree Hdecor Hin. inversion Hdecor; subst.
  - contradiction.
  - match goal with
    | Hchildren : DecoratesIRuns S trees ?runs |- _ =>
        destruct (decorated_tree_member d S trees runs tree Hchildren Hin)
          as [child [Hchild Htree]]
    end.
    eexists _, _, _, _. repeat split; eauto.
Qed.

Lemma decorates_leaf_inv : forall d (S : IBVAS d) index trees run,
    DecoratesIRun S (ltree_cons (inl index) trees) run ->
    trees = [] /\ run = irun_leaf (nth_idx (initial_vectors S) index).
Proof. intros. inversion H; subst. auto. Qed.

Lemma decorates_node_inv : forall d (S : IBVAS d) index target targets trees run,
    DecoratesIRun S (ltree_cons (inr (index, (target, targets))) trees) run ->
    exists runs,
      run = irun_node (nth_idx (system_actions S) index) runs target /\
      targets = iruns_targets runs /\ DecoratesIRuns S trees runs /\
      List.length (iruns_targets runs) =
        action_arity (nth_idx (system_actions S) index).
Proof.
  intros d S index target targets trees run H. inversion H; subst.
  eexists. repeat split; eauto.
Qed.

Lemma decorated_runs_embed : forall d (S : IBVAS d)
    left_trees right_trees left_runs right_runs,
    List.Forall2
      (fun left_tree right_tree =>
        forall left_run right_run,
          DecoratesIRun S left_tree left_run ->
          DecoratesIRun S right_tree right_run ->
          IRunEmbed left_run right_run)
      left_trees right_trees ->
    List.Forall2 nvec_le (iruns_targets left_runs) (iruns_targets right_runs) ->
    DecoratesIRuns S left_trees left_runs ->
    DecoratesIRuns S right_trees right_runs ->
    IRunsEmbed left_runs right_runs.
Proof.
  intros d S left_trees right_trees left_runs right_runs Htrees.
  revert left_runs right_runs.
  induction Htrees; intros left_runs right_runs Htargets Hleft Hright.
  - inversion Hleft; inversion Hright; subst. constructor.
  - inversion Hleft; inversion Hright; subst.
    inversion Htargets; subst. constructor.
    + assumption.
    + eapply H; eauto.
    + eapply IHHtrees; eauto.
Qed.

Theorem decorated_embedding_irun : forall d (S : IBVAS d) left_tree right_tree,
    ltree_homeo_embed (IRunLabelLe S) left_tree right_tree ->
    forall left right,
      DecoratesIRun S left_tree left ->
      DecoratesIRun S right_tree right ->
      IRunEmbed left right.
Proof.
  intros d S left_tree right_tree Hembed.
  induction Hembed as
    [small child label children Hmember Hembed IH
    |left_label left_children right_label right_children
      Hlabel Hchildren IHchildren];
    intros left right Hleft Hright.
  - destruct (decorated_member_of_run d S label children right child
      Hright Hmember) as
      [action [runs [target [right_child [-> [Hin Hdecor]]]]]].
    eapply embed_below with (child := right_child).
    + exact Hin.
    + eapply IH; eauto.
  - destruct left_label as [left_index|[left_index [left_target left_targets]]];
      destruct right_label as [right_index|[right_index [right_target right_targets]]];
      cbn in Hlabel; try contradiction.
    + subst right_index.
      destruct (decorates_leaf_inv d S left_index left_children left Hleft)
        as [-> ->].
      destruct (decorates_leaf_inv d S left_index right_children right Hright)
        as [-> ->]. constructor.
    + destruct Hlabel as [Hindex [Htarget Htargets]].
      cbn in Hindex, Htarget, Htargets. subst right_index.
      destruct (decorates_node_inv d S left_index left_target left_targets
        left_children left Hleft) as
        [left_runs [-> [Hleft_targets [Hleft_decor Hleft_length]]]].
      destruct (decorates_node_inv d S left_index right_target right_targets
        right_children right Hright) as
        [right_runs [-> [Hright_targets [Hright_decor Hright_length]]]].
      subst left_targets right_targets.
      assert (Htree_length : List.length left_children =
          List.length right_children).
      { rewrite (decorates_iruns_lengths d S left_children left_runs Hleft_decor),
          (decorates_iruns_lengths d S right_children right_runs Hright_decor),
          Hleft_length, Hright_length.
        reflexivity. }
      pose proof (list_embed_equal_length_Forall2 _ _ _ _ _
        IHchildren Htree_length) as Htree_pairs.
      assert (Htarget_length : List.length (iruns_targets left_runs) =
          List.length (iruns_targets right_runs)).
      { rewrite Hleft_length, Hright_length. reflexivity. }
      pose proof (list_embed_equal_length_Forall2 _ _ _ _ _
        Htargets Htarget_length) as Htarget_pairs.
      constructor; [exact Htarget|].
      eapply decorated_runs_embed; eauto.
Qed.

Theorem irun_le_wqo : forall d (S : IBVAS d),
    afs (ValidIRun S) IRunLe.
Proof.
  intros d S. apply af_sub_rel_afs.
  pose proof (af_ltree_homeo_embed (irun_label_almost_full d S)) as Htree.
  pose proof (af_product (nvec_le_almost_full d) Htree) as Hsource.
  eapply af_rel_morph with
    (f := fun source target =>
      fst source = irun_target (proj1_sig target) /\
      DecoratesIRun S (snd source) (proj1_sig target))
    (R := fun '(left_target, left_tree) '(right_target, right_tree) =>
      nvec_le left_target right_target /\
      ltree_homeo_embed (IRunLabelLe S) left_tree right_tree)
    (T := fun left right => IRunLe (proj1_sig left) (proj1_sig right)).
  - intros [run Hvalid]. cbn.
    destruct (proj1 (valid_irun_decorated_mut d S) run Hvalid) as [tree Htree'].
    exists (irun_target run, tree). cbn. auto.
  - intros [left_target left_tree] [right_target right_tree]
      [left Hleft_valid] [right Hright_valid]
      Hleft_rep Hright_rep Hrelation.
    cbn in Hleft_rep, Hright_rep, Hrelation |- *.
    destruct Hleft_rep as [Hleft_target Hleft_decor].
    destruct Hright_rep as [Hright_target Hright_decor].
    destruct Hrelation as [Htarget Hembed]. subst left_target right_target.
    split; [exact Htarget|].
    eapply decorated_embedding_irun; eauto.
  - exact Hsource.
Qed.

Theorem almost_full_finite_cover : forall X (R : X -> X -> Prop),
    af R -> exists basis : list X,
      forall x, exists b, List.In b basis /\ R b x.
Proof.
  intros X R Haf.
  destruct (classic (exists basis : list X,
      forall x, exists b, List.In b basis /\ R b x)) as [Hcover|Hno].
  - exact Hcover.
  - exfalso.
    assert (Hescape : forall basis : list X,
        exists x, forall b, List.In b basis -> ~ R b x).
    { intro basis. apply NNPP. intro Hnone.
      apply Hno. exists basis. intro x. apply NNPP. intro Hx.
      apply Hnone. exists x. intros b Hb Hbx.
      apply Hx. exists b. auto. }
    destruct (constructive_indefinite_description _ (Hescape [])) as
      [first Hfirst].
    set (State := (list X * X)%type).
    set (Step := fun current next : State =>
      exists fresh,
        next = (fst current ++ [snd current], fresh) /\
        forall b, List.In b (fst current ++ [snd current]) -> ~ R b fresh).
    assert (Hstep_total : forall current : State,
        {next : State | Step current next}).
    { intros [prefix current].
      destruct (constructive_indefinite_description _
        (Hescape (prefix ++ [current]))) as [fresh Hfresh].
      exists (prefix ++ [current], fresh), fresh. cbn. auto. }
    destruct (@dependent_choice State Step Hstep_total ([], first)) as
      [sequence [Hsequence0 Hsequence]].
    set (bad := fun n => snd (sequence n)).
    assert (Hprevious : forall j i, i < j ->
        List.In (bad i) (fst (sequence j))).
    { intro j. induction j as [|j IH]; intros i Hij; [lia|].
      specialize (Hsequence j). unfold Step in Hsequence.
      destruct Hsequence as [fresh [Hnext Hfresh]]. rewrite Hnext. cbn.
      apply in_app_iff. destruct (Nat.eq_dec i j) as [->|Hneq].
      - right. cbn. auto.
      - left. apply IH. lia. }
    destruct (@af_recursion X R Haf bad) as
      [bound [i [j [[Hij Hjb] Hgood]]]].
    destruct j as [|j]; [lia|].
    specialize (Hsequence j). unfold Step in Hsequence.
    destruct Hsequence as [fresh [Hnext Hfresh]].
    assert (Hbad : bad (S j) = fresh).
    { unfold bad. rewrite Hnext. reflexivity. }
    apply (Hfresh (bad i)).
    + pose proof (Hprevious (S j) i Hij) as Hmember.
      rewrite Hnext in Hmember. exact Hmember.
    + rewrite <- Hbad. exact Hgood.
Qed.

Theorem restricted_wqo_finite_cover : forall X (P : X -> Prop)
    (R : X -> X -> Prop),
    afs P R -> exists basis : list {x : X | P x},
      forall x : {x : X | P x},
        exists b, List.In b basis /\ R (proj1_sig b) (proj1_sig x).
Proof.
  intros X P R Hafs.
  apply almost_full_finite_cover.
  exact (@afs_af_sub_rel X P R Hafs).
Qed.

Theorem irun_le_finite_cover : forall d (S : IBVAS d),
    exists basis : list {run : IRun d | ValidIRun S run},
      forall run : {run : IRun d | ValidIRun S run},
        exists base, List.In base basis /\
          IRunLe (proj1_sig base) (proj1_sig run).
Proof.
  intros d S.
  eapply (@countable_af_finite_cover (IRun d)
    (enumerate_irun S) (ValidIRun S) IRunLe irun_le_dec).
  - exact (enumerate_irun_sound d S).
  - exact (enumerate_irun_complete d S).
  - apply irun_le_wqo.
Qed.

Fixpoint fin_to_idx {n} (index : Fin.t n) : idx n :=
  match index with
  | Fin.F1 => idx_fst
  | Fin.FS tail => idx_nxt (fin_to_idx tail)
  end.

Lemma idx_fin_inverse : forall n (index : Fin.t n),
    idx_to_fin (fin_to_idx index) = index.
Proof. intros n index; induction index; cbn; f_equal; assumption. Qed.

Lemma fin_eq_almost_full : forall n, af (@eq (Fin.t n)).
Proof.
  intro n. eapply af_rel_morph with
    (f := fun source target => idx_to_fin source = target)
    (R := @eq (idx n)) (T := @eq (Fin.t n)).
  - intro target. exists (fin_to_idx target). apply idx_fin_inverse.
  - intros left right left' right' Hleft Hright Heq.
    subst right. congruence.
  - apply af_idx.
Qed.

Lemma root_config_le_almost_full : forall d q, af (@RootConfigLe d q).
Proof.
  intros d q. unfold RootConfigLe.
  pose proof (af_product (fin_eq_almost_full q)
    (nvec_le_almost_full d)) as Hproduct.
  eapply af_mono; [|exact Hproduct].
  intros [ls lc] [rs rc] Hrel. exact Hrel.
Qed.

Definition SRunLabel {d q} (S : SBVAS d q) :=
  (idx (length (initial_configs S)) +
   (idx (length (stateful_rules S)) *
    (SConfig d q * list (SConfig d q))))%type.

Definition SRunNodeLabelLe {d q} (S : SBVAS d q) :
    (idx (length (stateful_rules S)) *
      (SConfig d q * list (SConfig d q))) ->
    (idx (length (stateful_rules S)) *
      (SConfig d q * list (SConfig d q))) -> Prop :=
  fun left right => fst left = fst right /\
    RootConfigLe (fst (snd left)) (fst (snd right)) /\
    list_embed RootConfigLe (snd (snd left)) (snd (snd right)).

Definition SRunLabelLe {d q} (S : SBVAS d q) :
    SRunLabel S -> SRunLabel S -> Prop :=
  fun left right =>
    match left, right with
    | inl left_index, inl right_index => left_index = right_index
    | inr left_node, inr right_node => SRunNodeLabelLe S left_node right_node
    | _, _ => False
    end.

Lemma srun_label_almost_full : forall d q (S : SBVAS d q),
    af (SRunLabelLe S).
Proof.
  intros d q S. unfold SRunLabelLe, SRunNodeLabelLe.
  apply af_sum.
  - apply af_idx.
  - eapply af_mono with (R := fun '(li, (lt, lc)) '(ri, (rt, rc)) =>
        li = ri /\ (RootConfigLe lt rt /\ list_embed RootConfigLe lc rc)).
    + intros [li [lt lc]] [ri [rt rc]]. cbn. tauto.
    + pose proof (root_config_le_almost_full d q) as Hconfig.
      pose proof (af_list_embed Hconfig) as Hlist.
      pose proof (af_product Hconfig Hlist) as Hpair.
      pose proof (af_product (af_idx (length (stateful_rules S))) Hpair)
        as Hnode.
      eapply af_mono; [|exact Hnode].
      intros [li [lt lc]] [ri [rt rc]] Hrel. exact Hrel.
Qed.

Inductive DecoratesSRun {d q} (S : SBVAS d q) :
    ltree (SRunLabel S) -> SRun d q -> Prop :=
| decorates_srun_leaf : forall index,
    DecoratesSRun S (ltree_cons (inl index) [])
      (srun_leaf (nth_idx (initial_configs S) index))
| decorates_srun_node : forall index result children child_trees,
    DecoratesSRuns S child_trees children ->
    List.length (sruns_configs children) =
      List.length (input_states (nth_idx (stateful_rules S) index)) ->
    DecoratesSRun S
      (ltree_cons (inr (index, (result, sruns_configs children))) child_trees)
      (srun_node (nth_idx (stateful_rules S) index) children result)
with DecoratesSRuns {d q} (S : SBVAS d q) :
    list (ltree (SRunLabel S)) -> SRuns d q -> Prop :=
| decorates_sruns_nil : DecoratesSRuns S [] sruns_nil
| decorates_sruns_cons : forall tree trees run runs,
    DecoratesSRun S tree run -> DecoratesSRuns S trees runs ->
    DecoratesSRuns S (tree :: trees) (sruns_cons run runs).

Scheme DecoratesSRun_ind' := Induction for DecoratesSRun Sort Prop
with DecoratesSRuns_ind' := Induction for DecoratesSRuns Sort Prop.
Combined Scheme DecoratesSRun_mutind from DecoratesSRun_ind', DecoratesSRuns_ind'.

Lemma valid_srun_decorated_mut : forall d q (S : SBVAS d q),
  (forall run, ValidSRun S run -> exists tree, DecoratesSRun S tree run) /\
  (forall runs, ValidSRuns S runs -> exists trees, DecoratesSRuns S trees runs).
Proof.
  intros d q S. apply ValidSRun_mutind.
  - intros config Hin. destruct (nth_idx_occurrence _ _ _ Hin) as [index Hidx].
    exists (ltree_cons (inl index) []). rewrite <- Hidx. constructor.
  - intros rule children result Hrule Hchildren IHchildren Hstates Happly Hout.
    destruct IHchildren as [trees Htrees].
    destruct (nth_idx_occurrence _ _ _ Hrule) as [index Hidx].
    exists (ltree_cons (inr (index, (result, sruns_configs children))) trees).
    rewrite <- Hidx. constructor; [exact Htrees|].
    apply Permutation_length in Hstates. rewrite map_length in Hstates.
    rewrite Hidx. exact Hstates.
  - exists []. constructor.
  - intros run runs Hrun IHrun Hruns IHruns.
    destruct IHrun as [tree Htree]. destruct IHruns as [trees Htrees].
    exists (tree :: trees). constructor; assumption.
Qed.

Lemma decorates_sruns_lengths : forall d q (S : SBVAS d q) trees runs,
    DecoratesSRuns S trees runs ->
    List.length trees = List.length (sruns_configs runs).
Proof. intros d q S trees runs H; induction H; cbn; congruence. Qed.

Lemma decorated_stree_member : forall d q (S : SBVAS d q) trees runs tree,
    DecoratesSRuns S trees runs -> List.In tree trees ->
    exists run, SRunsIn run runs /\ DecoratesSRun S tree run.
Proof.
  intros d q S trees runs tree Hdecor. induction Hdecor; cbn.
  - contradiction.
  - intros [<-|Hin].
    + exists run. split; [constructor|exact H].
    + destruct (IHHdecor Hin) as [found [Hfound Htree]].
      exists found. split; [constructor 2; exact Hfound|exact Htree].
Qed.

Lemma decorated_smember_of_run : forall d q (S : SBVAS d q)
    label trees run tree,
    DecoratesSRun S (ltree_cons label trees) run -> List.In tree trees ->
    exists rule runs result child,
      run = srun_node rule runs result /\ SRunsIn child runs /\
      DecoratesSRun S tree child.
Proof.
  intros d q S label trees run tree Hdecor Hin. inversion Hdecor; subst.
  - contradiction.
  - match goal with
    | Hchildren : DecoratesSRuns S trees ?runs |- _ =>
        destruct (decorated_stree_member d q S trees runs tree Hchildren Hin)
          as [child [Hchild Htree]]
    end.
    eexists _, _, _, _. repeat split; eauto.
Qed.

Lemma decorates_sleaf_inv : forall d q (S : SBVAS d q) index trees run,
    DecoratesSRun S (ltree_cons (inl index) trees) run ->
    trees = [] /\ run = srun_leaf (nth_idx (initial_configs S) index).
Proof. intros. inversion H; subst. auto. Qed.

Lemma decorates_snode_inv : forall d q (S : SBVAS d q)
    index result configs trees run,
    DecoratesSRun S (ltree_cons (inr (index, (result, configs))) trees) run ->
    exists runs,
      run = srun_node (nth_idx (stateful_rules S) index) runs result /\
      configs = sruns_configs runs /\ DecoratesSRuns S trees runs /\
      List.length (sruns_configs runs) =
        List.length (input_states (nth_idx (stateful_rules S) index)).
Proof. intros. inversion H; subst. eexists. repeat split; eauto. Qed.

Lemma decorated_sruns_embed : forall d q (S : SBVAS d q)
    left_trees right_trees left_runs right_runs,
    List.Forall2
      (fun left_tree right_tree =>
        forall left_run right_run,
          DecoratesSRun S left_tree left_run ->
          DecoratesSRun S right_tree right_run ->
          OrderedDecorEmbed left_run right_run)
      left_trees right_trees ->
    List.Forall2 RootConfigLe (sruns_configs left_runs) (sruns_configs right_runs) ->
    DecoratesSRuns S left_trees left_runs ->
    DecoratesSRuns S right_trees right_runs ->
    OrderedDecorEmbeds left_runs right_runs.
Proof.
  intros d q S left_trees right_trees left_runs right_runs Htrees.
  revert left_runs right_runs.
  induction Htrees; intros left_runs right_runs Hconfigs Hleft Hright.
  - inversion Hleft; inversion Hright; subst. constructor.
  - inversion Hleft; inversion Hright; subst. inversion Hconfigs; subst.
    constructor; [assumption|eapply H; eauto|eapply IHHtrees; eauto].
Qed.

Theorem decorated_embedding_srun : forall d q (S : SBVAS d q)
    left_tree right_tree,
    ltree_homeo_embed (SRunLabelLe S) left_tree right_tree ->
    forall left right,
      DecoratesSRun S left_tree left -> DecoratesSRun S right_tree right ->
      OrderedDecorEmbed left right.
Proof.
  intros d q S left_tree right_tree Hembed.
  induction Hembed as
    [small child label children Hmember Hembed IH
    |left_label left_children right_label right_children
      Hlabel Hchildren IHchildren];
    intros left right Hleft Hright.
  - destruct (decorated_smember_of_run d q S label children right child
      Hright Hmember) as
      [rule [runs [result [right_child [-> [Hin Hdecor]]]]]].
    eapply ordered_embed_below with (child := right_child); [exact Hin|].
    eapply IH; eauto.
  - destruct left_label as [left_index|[left_index [left_result left_configs]]];
      destruct right_label as [right_index|[right_index [right_result right_configs]]];
      cbn in Hlabel; try contradiction.
    + subst right_index.
      destruct (decorates_sleaf_inv d q S left_index left_children left Hleft)
        as [-> ->].
      destruct (decorates_sleaf_inv d q S left_index right_children right Hright)
        as [-> ->]. constructor.
    + destruct Hlabel as [Hindex [Hroot Hconfigs]].
      cbn in Hindex, Hroot, Hconfigs. subst right_index.
      destruct (decorates_snode_inv d q S left_index left_result left_configs
        left_children left Hleft) as
        [left_runs [-> [Hleft_configs [Hleft_decor Hleft_length]]]].
      destruct (decorates_snode_inv d q S left_index right_result right_configs
        right_children right Hright) as
        [right_runs [-> [Hright_configs [Hright_decor Hright_length]]]].
      subst left_configs right_configs.
      assert (Htree_length : List.length left_children =
          List.length right_children).
      { rewrite (decorates_sruns_lengths d q S left_children left_runs Hleft_decor),
          (decorates_sruns_lengths d q S right_children right_runs Hright_decor),
          Hleft_length, Hright_length. reflexivity. }
      pose proof (list_embed_equal_length_Forall2 _ _ _ _ _
        IHchildren Htree_length) as Htree_pairs.
      assert (Hconfig_length : List.length (sruns_configs left_runs) =
          List.length (sruns_configs right_runs)).
      { rewrite Hleft_length, Hright_length. reflexivity. }
      pose proof (list_embed_equal_length_Forall2 _ _ _ _ _
        Hconfigs Hconfig_length) as Hconfig_pairs.
      constructor. eapply decorated_sruns_embed; eauto.
Qed.

Definition StrongSRunLe {d q} (left right : SRun d q) : Prop :=
  RootConfigLe (root_config left) (root_config right) /\
  OrderedDecorEmbed left right.

Theorem strong_srun_le_wqo : forall d q (S : SBVAS d q),
    afs (ValidSRun S) StrongSRunLe.
Proof.
  intros d q S. apply af_sub_rel_afs.
  pose proof (af_ltree_homeo_embed (srun_label_almost_full d q S)) as Htree.
  pose proof (af_product (root_config_le_almost_full d q) Htree) as Hsource.
  eapply af_rel_morph with
    (f := fun source target =>
      fst source = root_config (proj1_sig target) /\
      DecoratesSRun S (snd source) (proj1_sig target))
    (R := fun '(left_root, left_tree) '(right_root, right_tree) =>
      RootConfigLe left_root right_root /\
      ltree_homeo_embed (SRunLabelLe S) left_tree right_tree)
    (T := fun left right => StrongSRunLe (proj1_sig left) (proj1_sig right)).
  - intros [run Hvalid]. cbn.
    destruct (proj1 (valid_srun_decorated_mut d q S) run Hvalid) as [tree Htree'].
    exists (root_config run, tree). cbn. auto.
  - intros [left_root left_tree] [right_root right_tree]
      [left Hleft_valid] [right Hright_valid]
      Hleft_rep Hright_rep Hrelation.
    cbn in Hleft_rep, Hright_rep, Hrelation |- *.
    destruct Hleft_rep as [Hleft_root Hleft_decor].
    destruct Hright_rep as [Hright_root Hright_decor].
    destruct Hrelation as [Hroot Hembed]. subst left_root right_root.
    split; [exact Hroot|]. eapply decorated_embedding_srun; eauto.
  - exact Hsource.
Qed.

Theorem context_order_wqo : forall d q (S : SBVAS d q),
    afs (ValidSRun S) (ContextOrder S).
Proof.
  intros d q S. eapply afs_mono with
    (P := ValidSRun S) (R := @StrongSRunLe d q).
  - intros run Hvalid. exact Hvalid.
  - intros left right Hleft Hright Hroot.
    destruct Hroot as [Hconfig Hembed].
    eapply ordered_embed_implies_context_insert; eauto.
  - apply strong_srun_le_wqo.
Qed.

Theorem context_order_finite_cover : forall d q (S : SBVAS d q),
    exists basis : list {run : SRun d q | ValidSRun S run},
      forall run : {run : SRun d q | ValidSRun S run},
        exists base, List.In base basis /\
          ContextOrder S (proj1_sig base) (proj1_sig run).
Proof.
  intros d q S.
  destruct (@countable_af_finite_cover (SRun d q)
      (enumerate_srun S) (ValidSRun S) StrongSRunLe strong_srun_le_dec
      (enumerate_srun_sound d q S) (enumerate_srun_complete d q S)
      (strong_srun_le_wqo d q S)) as [basis Hbasis].
  exists basis. intros run.
  destruct (Hbasis run) as [base [Hin [Hroot Hembed]]].
  exists base. split; [exact Hin|].
  eapply ordered_embed_implies_context_insert.
  - exact (proj2_sig base).
  - exact (proj2_sig run).
  - exact Hroot.
  - exact Hembed.
Qed.
