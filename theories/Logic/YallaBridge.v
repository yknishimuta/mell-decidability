From Coq Require Import List.
Require Yalla.mell_mset.
Require Yalla.ll_fragments.
From Yalla.OLlibs Require Import BOrders fmsetlist_Type Permutation_Type_more.
From Mell.Logic Require Import Syntax Calculus.

Import ListNotations.
Module Y := Yalla.mell_mset.
Module F := Yalla.ll_fragments.

#[local] Existing Instance Y.fmset_formula.

Fixpoint to_yalla (A : formula) : Y.formula :=
  match A with
  | Atom p => Y.var p
  | CoAtom p => Y.covar p
  | One => Y.one
  | Bottom => Y.bot
  | Tensor A B => Y.tens (to_yalla A) (to_yalla B)
  | Par A B => Y.parr (to_yalla A) (to_yalla B)
  | Bang A => Y.oc (to_yalla A)
  | WhyNot A => Y.wn (to_yalla A)
  end.

Fixpoint from_yalla (A : Y.formula) : formula :=
  match A with
  | Y.var p => Atom p
  | Y.covar p => CoAtom p
  | Y.one => One
  | Y.bot => Bottom
  | Y.tens A B => Tensor (from_yalla A) (from_yalla B)
  | Y.parr A B => Par (from_yalla A) (from_yalla B)
  | Y.oc A => Bang (from_yalla A)
  | Y.wn A => WhyNot (from_yalla A)
  end.

Lemma from_to_yalla : forall A, from_yalla (to_yalla A) = A.
Proof. induction A; simpl; congruence. Qed.

Lemma to_from_yalla : forall A, to_yalla (from_yalla A) = A.
Proof. induction A; simpl; congruence. Qed.

Lemma to_yalla_dual : forall A, Y.dual (to_yalla A) = to_yalla (dual A).
Proof. induction A; simpl; congruence. Qed.

Definition yalla_sequent := BOrders.SortedList Y.border_formula.

Definition to_yalla_sequent (Gamma : sequent) : yalla_sequent :=
  @list2fm yalla_sequent Y.formula Y.fmset_formula (map to_yalla Gamma).

Lemma to_yalla_whynot_context : forall Gamma,
    map to_yalla (map WhyNot Gamma) = map Y.wn (map to_yalla Gamma).
Proof.
  induction Gamma; simpl; congruence.
Qed.

Lemma to_yalla_whynot_multiset : forall Gamma,
    @list2fm yalla_sequent Y.formula Y.fmset_formula
      (map to_yalla (map WhyNot Gamma)) =
    @fmmap yalla_sequent Y.formula yalla_sequent Y.formula
      Y.fmset_formula Y.fmset_formula Y.wn
      (@list2fm yalla_sequent Y.formula Y.fmset_formula
        (map to_yalla Gamma)).
Proof.
  intro Gamma.
  rewrite to_yalla_whynot_context.
  apply list2fm_map.
Qed.

Fixpoint derivation_to_yalla {Gamma} (pi : Derivation Gamma) :
    Y.mell (to_yalla_sequent Gamma).
Proof.
  destruct pi; unfold to_yalla_sequent in *; simpl in *.
  - apply Y.ax_r.
  - apply Y.one_r.
  - apply Y.bot_r. exact (derivation_to_yalla _ pi).
  - rewrite map_app, list2fm_app.
    apply Y.tens_r.
    + exact (derivation_to_yalla _ pi1).
    + exact (derivation_to_yalla _ pi2).
  - apply Y.parr_r. exact (derivation_to_yalla _ pi).
  - rewrite to_yalla_whynot_multiset.
    apply Y.oc_r.
    rewrite <- to_yalla_whynot_multiset.
    exact (derivation_to_yalla _ pi).
  - apply Y.de_r. exact (derivation_to_yalla _ pi).
  - apply Y.wk_r. exact (derivation_to_yalla _ pi).
  - apply Y.co_r. exact (derivation_to_yalla _ pi).
  - rewrite <- (@list2fm_perm yalla_sequent Y.formula Y.fmset_formula
      _ _ (Permutation_Type_map to_yalla p)).
    exact (derivation_to_yalla _ pi).
Defined.

Lemma provable_permute : forall Gamma Delta,
    Provable Gamma -> Permutation_Type Gamma Delta -> Provable Delta.
Proof.
  intros Gamma Delta [pi] perm.
  constructor; exact (exchange_rule Gamma Delta pi perm).
Qed.

Lemma mapped_elts_add : forall (A : Y.formula) (m : yalla_sequent),
    Permutation_Type
      (map from_yalla (elts (add A m)))
      (from_yalla A :: map from_yalla (elts m)).
Proof.
  intros A m.
  exact (Permutation_Type_map from_yalla
    (@elts_add yalla_sequent Y.formula Y.fmset_formula A m)).
Qed.

Lemma mapped_elts_sum : forall (m1 m2 : yalla_sequent),
    Permutation_Type
      (map from_yalla (elts (sum m1 m2)))
      (map from_yalla (elts m1) ++ map from_yalla (elts m2)).
Proof.
  intros m1 m2.
  rewrite <- map_app.
  exact (Permutation_Type_map from_yalla
    (@elts_sum yalla_sequent Y.formula Y.fmset_formula m1 m2)).
Qed.

Lemma mapped_elts_fmmap_whynot : forall (m : yalla_sequent),
    Permutation_Type
      (map from_yalla (elts (fmmap Y.wn m)))
      (map WhyNot (map from_yalla (elts m))).
Proof.
  intro m.
  etransitivity.
  - exact (Permutation_Type_map from_yalla
      (@elts_fmmap yalla_sequent Y.formula yalla_sequent Y.formula
        Y.fmset_formula Y.fmset_formula Y.wn m)).
  - induction (elts m); simpl; constructor; auto.
Qed.

Lemma mapped_elts_list2fm : forall l,
    Permutation_Type
      (map from_yalla
        (elts (@list2fm yalla_sequent Y.formula Y.fmset_formula l)))
      (map from_yalla l).
Proof.
  intro l.
  exact (Permutation_Type_map from_yalla
    (@elts_perm yalla_sequent Y.formula Y.fmset_formula l)).
Qed.

Lemma yalla_to_provable : forall m, Y.mell m ->
    Provable (map from_yalla (elts m)).
Proof.
  intros m pi.
  induction pi.
  - apply provable_permute with
      (Gamma := map from_yalla [Y.covar X; Y.var X]).
    + exact (provable_atom_identity X).
    + apply Permutation_Type_sym.
      exact (mapped_elts_list2fm [Y.covar X; Y.var X]).
  - apply provable_permute with (Gamma := [One]).
    + exact provable_one.
    + apply Permutation_Type_sym.
      exact (mapped_elts_list2fm [Y.one]).
  - apply provable_permute with
      (Gamma := Bottom :: map from_yalla (elts m)).
    + destruct IHpi as [dpi]. constructor. apply bottom_rule. exact dpi.
    + apply Permutation_Type_sym. apply mapped_elts_add.
  - apply provable_permute with
      (Gamma := Tensor (from_yalla A) (from_yalla B) ::
        map from_yalla (elts m1) ++ map from_yalla (elts m2)).
    + destruct IHpi1 as [dpi1]. destruct IHpi2 as [dpi2].
      constructor. apply tensor_rule.
      * exact (exchange_rule _ _ dpi1 (mapped_elts_add A m1)).
      * exact (exchange_rule _ _ dpi2 (mapped_elts_add B m2)).
    + eapply Permutation_Type_trans.
      * apply Permutation_Type_cons; [reflexivity |].
        apply Permutation_Type_sym, mapped_elts_sum.
      * apply Permutation_Type_sym, mapped_elts_add.
  - apply provable_permute with
      (Gamma := Par (from_yalla A) (from_yalla B) ::
        map from_yalla (elts m)).
    + destruct IHpi as [dpi]. constructor. apply par_rule.
      exact (exchange_rule _ _ dpi
        (Permutation_Type_trans (mapped_elts_add A (add B m))
          (Permutation_Type_cons (eq_refl _) (mapped_elts_add B m)))).
    + apply Permutation_Type_sym, mapped_elts_add.
  - apply provable_permute with
      (Gamma := Bang (from_yalla A) ::
        map WhyNot (map from_yalla (elts m))).
    + destruct IHpi as [dpi]. constructor. apply promotion_rule.
      apply exchange_rule with
        (Gamma := map from_yalla (elts (add A (fmmap Y.wn m)))).
      * exact dpi.
      * eapply Permutation_Type_trans.
        -- apply mapped_elts_add.
        -- apply Permutation_Type_cons; [reflexivity |].
           apply mapped_elts_fmmap_whynot.
    + apply Permutation_Type_sym.
      eapply Permutation_Type_trans.
      * apply mapped_elts_add.
      * apply Permutation_Type_cons; [reflexivity |].
        apply mapped_elts_fmmap_whynot.
  - apply provable_permute with
      (Gamma := WhyNot (from_yalla A) :: map from_yalla (elts m)).
    + destruct IHpi as [dpi]. constructor. apply dereliction_rule.
      exact (exchange_rule _ _ dpi (mapped_elts_add A m)).
    + apply Permutation_Type_sym, mapped_elts_add.
  - apply provable_permute with
      (Gamma := WhyNot (from_yalla A) :: map from_yalla (elts m)).
    + destruct IHpi as [dpi]. constructor. apply weakening_rule. exact dpi.
    + apply Permutation_Type_sym, mapped_elts_add.
  - apply provable_permute with
      (Gamma := WhyNot (from_yalla A) :: map from_yalla (elts m)).
    + destruct IHpi as [dpi]. constructor. apply contraction_rule.
      apply exchange_rule with
        (Gamma := map from_yalla
          (elts (add (Y.wn A) (add (Y.wn A) m)))).
      * exact dpi.
      * eapply Permutation_Type_trans.
        -- apply mapped_elts_add.
        -- apply Permutation_Type_cons; [reflexivity |].
           apply mapped_elts_add.
    + apply Permutation_Type_sym, mapped_elts_add.
Qed.

Lemma map_from_to_yalla : forall Gamma,
    map from_yalla (map to_yalla Gamma) = Gamma.
Proof.
  induction Gamma; simpl; [reflexivity |].
  rewrite from_to_yalla, IHGamma; reflexivity.
Qed.

Theorem provable_yalla_iff : forall Gamma,
    Provable Gamma <-> Y.mell (to_yalla_sequent Gamma).
Proof.
  intro Gamma; split.
  - intros [pi]. exact (derivation_to_yalla pi).
  - intro pi.
    apply yalla_to_provable in pi.
    apply provable_permute with
      (Gamma := map from_yalla (elts (to_yalla_sequent Gamma))).
    + exact pi.
    + unfold to_yalla_sequent.
      eapply Permutation_Type_trans.
      * exact (mapped_elts_list2fm (map to_yalla Gamma)).
      * rewrite map_from_to_yalla. apply Permutation_Type_refl.
Qed.

Fixpoint cut_derivation_to_yalla {Gamma} (pi : DerivationWithCut Gamma) :
    Y.mell (to_yalla_sequent Gamma).
Proof.
  destruct pi; unfold to_yalla_sequent in *; simpl in *.
  - apply Y.ax_r.
  - apply Y.one_r.
  - apply Y.bot_r. exact (cut_derivation_to_yalla _ pi).
  - rewrite map_app, list2fm_app.
    apply Y.tens_r.
    + exact (cut_derivation_to_yalla _ pi1).
    + exact (cut_derivation_to_yalla _ pi2).
  - apply Y.parr_r. exact (cut_derivation_to_yalla _ pi).
  - rewrite to_yalla_whynot_multiset.
    apply Y.oc_r.
    rewrite <- to_yalla_whynot_multiset.
    exact (cut_derivation_to_yalla _ pi).
  - apply Y.de_r. exact (cut_derivation_to_yalla _ pi).
  - apply Y.wk_r. exact (cut_derivation_to_yalla _ pi).
  - apply Y.co_r. exact (cut_derivation_to_yalla _ pi).
  - rewrite <- (@list2fm_perm yalla_sequent Y.formula Y.fmset_formula
      _ _ (Permutation_Type_map to_yalla p)).
    exact (cut_derivation_to_yalla _ pi).
  - rewrite map_app, list2fm_app.
    apply (Y.cut_r (to_yalla A)).
    + exact (cut_derivation_to_yalla _ pi1).
    + rewrite to_yalla_dual.
      exact (cut_derivation_to_yalla _ pi2).
Defined.

Theorem provable_cut_iff : forall Gamma,
    ProvableWithCut Gamma <-> Provable Gamma.
Proof.
  intro Gamma; split.
  - intros [pi].
    apply provable_yalla_iff.
    exact (cut_derivation_to_yalla pi).
  - apply provable_implies_with_cut.
Qed.

Lemma yalla_add_not_empty : forall (A : Y.formula) (m : yalla_sequent),
    add A m <> empty.
Proof.
  intros A m Heq.
  pose proof (@elts_add yalla_sequent Y.formula Y.fmset_formula A m) as perm.
  rewrite Heq, elts_empty in perm.
  exact (Permutation_Type_nil_cons perm).
Qed.

Lemma yalla_mell_not_empty : forall m, Y.mell m -> m <> empty.
Proof.
  intros m pi.
  destruct pi; apply yalla_add_not_empty.
Qed.

Theorem not_provable_empty : ~ Provable [].
Proof.
  intro provable.
  apply provable_yalla_iff in provable.
  exact (yalla_mell_not_empty _ provable eq_refl).
Qed.

Theorem not_provable_two_ones : ~ Provable [One; One].
Proof.
  intro provable.
  apply provable_yalla_iff in provable.
  destruct (Y.mell2mellfrag _ provable) as [pi].
  assert (F.ll_mix0 [Yalla.formulas.one; Yalla.formulas.one]) as pi_mix0.
  {
    apply (ll_def.stronger_pfrag Y.pfrag_mell F.pfrag_mix0).
    - repeat split; simpl; try reflexivity; intros a; destruct a.
    - eapply ll_def.ex_r.
      + exact pi.
      + unfold to_yalla_sequent in provable.
        simpl in provable.
        exact (Permutation_Type_map Y.mell2ll
          (@elts_perm yalla_sequent Y.formula Y.fmset_formula
            [Y.one; Y.one])).
  }
  exact (F.mix0_not_mix2 pi_mix0).
Qed.

Lemma yalla_fragment_no_cut : ll_def.pcut Y.pfrag_mell = false.
Proof. reflexivity. Qed.

Lemma yalla_fragment_no_mix0 : ll_def.pmix0 Y.pfrag_mell = false.
Proof. reflexivity. Qed.

Lemma yalla_fragment_no_mix2 : ll_def.pmix2 Y.pfrag_mell = false.
Proof. reflexivity. Qed.

Lemma yalla_fragment_full_exchange : ll_def.pperm Y.pfrag_mell = true.
Proof. reflexivity. Qed.
