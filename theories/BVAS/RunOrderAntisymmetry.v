From Coq Require Import Lia Vector.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Contexts RunOrder Amalgamation.
From Mell.Order Require Import FiniteBasis.

Fixpoint irun_node_count {d} (run : IRun d) : nat :=
  match run with
  | irun_leaf _ => 1
  | irun_node _ children _ => S (iruns_node_count children)
  end
with iruns_node_count {d} (runs : IRuns d) : nat :=
  match runs with
  | iruns_nil => 0
  | iruns_cons run tail => irun_node_count run + iruns_node_count tail
  end.

Lemma iruns_in_node_count : forall d (run : IRun d) runs,
  IRunsIn run runs -> irun_node_count run <= iruns_node_count runs.
Proof.
  intros d run runs Hin. induction Hin; cbn; lia.
Qed.
Lemma iruns_in_parent_count_strict : forall d (run : IRun d)
    action children target,
  IRunsIn run children ->
  irun_node_count run < irun_node_count (irun_node action children target).
Proof. intros; cbn. pose proof (iruns_in_node_count d run children H); lia. Qed.

Lemma irun_embed_node_count :
  (forall d (left right : IRun d), IRunEmbed left right ->
    irun_node_count left <= irun_node_count right) /\
  (forall d (left right : IRuns d), IRunsEmbed left right ->
    iruns_node_count left <= iruns_node_count right).
Proof.
  assert (Hcounts : forall d,
    (forall left right (embedding : @IRunEmbed d left right),
      irun_node_count left <= irun_node_count right) /\
    (forall left right (embedding : @IRunsEmbed d left right),
      iruns_node_count left <= iruns_node_count right)).
  { intro dimension. refine (IRunEmbed_IRunsEmbed_mutind dimension
      (fun left right _ => irun_node_count left <= irun_node_count right)
      (fun left right _ => iruns_node_count left <= iruns_node_count right)
      _ _ _ _ _).
    - reflexivity.
    - intros action left_children right_children left_target right_target
        Htargets Hchildren IHchildren. cbn. lia.
    - intros small action children target child Hin Hembed IHembed.
      pose proof (iruns_in_parent_count_strict dimension child action children
        target Hin). lia.
    - reflexivity.
    - intros left right lefts rights Htarget Hhead IHhead Htail IHtail.
      cbn. lia. }
  split; intros d left right Hembed.
  - exact (proj1 (Hcounts d) left right Hembed).
  - exact (proj2 (Hcounts d) left right Hembed).
Qed.

Lemma nvec_le_antisymmetric : forall d (left right : NVec d),
  nvec_le left right -> nvec_le right left -> left = right.
Proof.
  intros d left right Hlr Hrl.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  specialize (Hlr index); specialize (Hrl index). lia.
Qed.

Lemma irun_embed_antisymmetric :
  (forall d (left right : IRun d),
    IRunEmbed left right -> IRunEmbed right left -> left = right) /\
  (forall d (left right : IRuns d),
    IRunsEmbed left right -> IRunsEmbed right left -> left = right).
Proof.
  assert (Hboth : forall d,
    (forall left right (embedding : @IRunEmbed d left right),
      IRunEmbed right left -> left = right) /\
    (forall left right (embedding : @IRunsEmbed d left right),
      IRunsEmbed right left -> left = right)).
  { intro dimension. refine (IRunEmbed_IRunsEmbed_mutind dimension
      (fun left right _ => IRunEmbed right left -> left = right)
      (fun left right _ => IRunsEmbed right left -> left = right)
      _ _ _ _ _).
    - intros value Hreverse. inversion Hreverse. reflexivity.
    - intros action left_children right_children left_target right_target
        Htarget Hchildren IHchildren Hreverse.
      inversion Hreverse as
        [|action' right_children' left_children' right_target' left_target'
          Htarget_reverse Hchildren_reverse
         |small action' left_children' left_target' child Hin Hchild]; subst.
      + pose proof (IHchildren Hchildren_reverse) as Hchildren_eq.
        pose proof (nvec_le_antisymmetric dimension left_target right_target
          Htarget Htarget_reverse) as Htarget_eq.
        subst. reflexivity.
      + pose proof (proj1 irun_embed_node_count dimension
          (irun_node action left_children left_target)
          (irun_node action right_children right_target)
          (embed_node action left_children right_children left_target
            right_target Htarget Hchildren)) as Hforward_count.
        pose proof (proj1 irun_embed_node_count dimension
          (irun_node action right_children right_target) child Hchild)
          as Hchild_count.
        pose proof (iruns_in_parent_count_strict dimension child
          action left_children left_target Hin) as Hstrict.
        cbn in *. lia.
    - intros small action children target child Hin Hembed IHembed Hreverse.
      pose proof (proj1 irun_embed_node_count dimension small child Hembed)
        as Hsmall_child.
      pose proof (iruns_in_parent_count_strict dimension child action children
        target Hin) as Hchild_parent.
      pose proof (proj1 irun_embed_node_count dimension
        (irun_node action children target) small Hreverse) as Hparent_small.
      lia.
    - intros Hreverse. inversion Hreverse. reflexivity.
    - intros left right lefts rights Htarget Hhead IHhead Htail IHtail Hreverse.
      inversion Hreverse; subst.
      pose proof (IHhead H4) as Hhead_eq.
      pose proof (IHtail H5) as Htail_eq.
      subst. reflexivity. }
  split; intros d left right Hforward Hreverse.
  - exact (proj1 (Hboth d) left right Hforward Hreverse).
  - exact (proj2 (Hboth d) left right Hforward Hreverse).
Qed.

Theorem irun_le_antisymmetric : forall d (left right : IRun d),
  IRunLe left right -> IRunLe right left -> left = right.
Proof.
  intros d left right [_ Hlr] [_ Hrl].
  now apply (proj1 irun_embed_antisymmetric d left right).
Qed.

Record IRunWPOAmalgamation (d : nat) (system : IBVAS d) : Prop := {
  irun_wpo_refl : forall run : IRun d, IRunLe run run;
  irun_wpo_trans : forall left middle right : IRun d,
    IRunLe left middle -> IRunLe middle right -> IRunLe left right;
  irun_wpo_antisym : forall left right : IRun d,
    IRunLe left right -> IRunLe right left -> left = right;
  irun_wpo_almost_full :
    @KruskalAfProp.af.af.afs (IRun d) (ValidIRun system) (@IRunLe d);
  irun_wpo_exact_amalgamation : forall root left right : IRun d,
    ValidIRun system root -> ValidIRun system left -> ValidIRun system right ->
    IRunLe root left -> IRunLe root right ->
    exists merged,
      ValidIRun system merged /\ IRunLe left merged /\ IRunLe right merged /\
      nvec_add (irun_target root) (irun_target merged) =
        nvec_add (irun_target left) (irun_target right)
}.

Theorem lemma_3_10_irun_wpo_amalgamation : forall d (system : IBVAS d),
  IRunWPOAmalgamation d system.
Proof.
  intros. constructor.
  - apply irun_le_refl.
  - apply irun_le_trans.
  - apply irun_le_antisymmetric.
  - apply irun_le_wqo.
  - apply run_amalgamation.
Qed.
