From Coq Require Import List Arith.PeanoNat.
Require Import Yalla.mell_mset.
Require Import Yalla.nn_prop.
From Yalla.OLlibs Require Import BOrders fmsetlist_Type Permutation_Type_more.
From Mell.Logic Require Import Syntax Calculus YallaBridge.
From Mell.Reduction Require Import ILZRuntime.

Import ListNotations.
Module YM := Yalla.mell_mset.
Module NN := Yalla.nn_prop.
Module IF := Yalla.iformulas.

Definition classical_linear_sequent := classical_linear_sequent_runtime.

Definition ILZGoal := RuntimeILZGoal.

Definition translation_atom := translation_atom_runtime.

Definition translation_parameter := translation_parameter_runtime.

Definition close_ilz_context := close_ilz_context_runtime.

Lemma close_ilz_context_intro : forall context conclusion,
  Yalla.ill_cut.ill_ll context conclusion ->
  Yalla.ill_cut.ill_ll [] (close_ilz_context context conclusion).
Proof.
  induction context as [|A context IH]; intros conclusion pi; simpl.
  - exact pi.
  - apply IH. now apply Yalla.ill_def.lmap_irr.
Defined.

Lemma close_ilz_context_elim : forall context conclusion,
  Yalla.ill_cut.ill_ll [] (close_ilz_context context conclusion) ->
  Yalla.ill_cut.ill_ll context conclusion.
Proof.
  induction context as [|A context IH]; intros conclusion pi; simpl in pi.
  - exact pi.
  - pose proof (IH (IF.ilmap A conclusion) pi) as implication.
    replace (A :: context) with ([A] ++ context ++ []) by
      (simpl; now rewrite app_nil_r).
    eapply Yalla.ill_cut.cut_ll_ir with
      (A := IF.ilmap A conclusion) (l0 := context)
      (l1 := [A]) (l2 := []) (C := conclusion).
    + exact implication.
    + simpl.
      eapply Yalla.ill_def.lmap_ilr with
        (A := A) (B := conclusion) (l0 := [A])
        (l1 := []) (l2 := []) (C := conclusion).
      * apply Yalla.ill_def.ax_exp_ill.
      * apply Yalla.ill_def.ax_exp_ill.
Defined.

Definition translate_mell := translate_mell_runtime.

Definition ILZProvable (goal : ILZGoal) : Prop :=
  inhabited (Yalla.ill_cut.ill_ll (fst goal) (snd goal)).

Lemma mell_to_linear_to_yalla : forall formula,
  mell_to_linear formula = YM.mell2ll (to_yalla formula).
Proof. induction formula; cbn; congruence. Qed.

Lemma mell2ll_insert : forall value values,
  map YM.mell2ll (@insert YM.border_formula value values) =
  @insert Yalla.fmformulas.border_formula (YM.mell2ll value)
    (map YM.mell2ll values).
Proof.
  intros value values. induction values as [|head tail IH]; cbn; [reflexivity|].
  unfold YM.border_formula, Yalla.fmformulas.border_formula. cbn.
  destruct (Nat.leb
    (nattree.nattree2nat
      (Yalla.fmformulas.form2nattree (YM.mell2ll value)))
    (nattree.nattree2nat
      (Yalla.fmformulas.form2nattree (YM.mell2ll head)))); cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma mell2ll_sorted_fold : forall values,
  map YM.mell2ll
    (proj1_sig (fold_right (@fmslist_add YM.border_formula)
      (@fmslist_empty YM.border_formula) values)) =
  proj1_sig (fold_right (@fmslist_add Yalla.fmformulas.border_formula)
    (@fmslist_empty Yalla.fmformulas.border_formula)
    (map YM.mell2ll values)).
Proof.
  induction values as [|head tail IH]; cbn; [reflexivity|].
  rewrite mell2ll_insert. f_equal. exact IH.
Qed.

Lemma classical_linear_sequent_reference : forall Gamma,
  classical_linear_sequent Gamma =
  map YM.mell2ll (elts (to_yalla_sequent Gamma)).
Proof.
  intro Gamma. unfold classical_linear_sequent,
    classical_linear_sequent_runtime, to_yalla_sequent.
  change (proj1_sig
      (fold_right (@fmslist_add Yalla.fmformulas.border_formula)
        (@fmslist_empty Yalla.fmformulas.border_formula)
        (map mell_to_linear Gamma)) =
    map YM.mell2ll
      (proj1_sig (fold_right (@fmslist_add YM.border_formula)
        (@fmslist_empty YM.border_formula) (map to_yalla Gamma)))).
  assert (Hmap : map YM.mell2ll (map to_yalla Gamma) =
      map mell_to_linear Gamma).
  { induction Gamma as [|formula tail IH]; cbn; [reflexivity|].
    f_equal; [symmetry; apply mell_to_linear_to_yalla | exact IH]. }
  symmetry.
  etransitivity.
  - exact (mell2ll_sorted_fold (map to_yalla Gamma)).
  - now rewrite Hmap.
Qed.

Lemma provable_classical_linear_sequent : forall Gamma,
  Provable Gamma ->
  inhabited (Yalla.ll_fragments.ll_ll (classical_linear_sequent Gamma)).
Proof.
  intros Gamma H.
  rewrite classical_linear_sequent_reference.
  apply provable_yalla_iff in H.
  exact (YM.mell2mellfrag _ H).
Qed.

Lemma classical_linear_sequent_provable : forall Gamma,
  inhabited (Yalla.ll_fragments.ll_ll (classical_linear_sequent Gamma)) ->
  Provable Gamma.
Proof.
  intros Gamma [H].
  apply provable_yalla_iff.
  apply YM.mellfrag2mell.
  rewrite <- classical_linear_sequent_reference.
  exact H.
Qed.

Theorem mell_ilz_iff : forall Gamma,
  Provable Gamma <-> ILZProvable (translate_mell Gamma).
Proof.
  intro Gamma; split.
  - intro H.
    unfold ILZProvable, translate_mell; simpl.
    destruct (provable_classical_linear_sequent Gamma H) as [Hll].
    constructor.
    apply close_ilz_context_intro.
    now apply NN.ll_ll_to_ill_trans.
  - intro H.
    unfold ILZProvable, translate_mell in H; simpl in H.
    destruct H as [H].
    apply close_ilz_context_elim in H.
    apply classical_linear_sequent_provable.
    constructor.
    apply NN.llR_bot_to_ll.
    apply NN.ill_trans_to_llR in H.
    unfold translation_parameter, translation_atom in H.
    apply (Yalla.ll_fragments.subs_llR _ Yalla.formulas.bot
      (Yalla.subs.fresh_of_list
        Yalla.nn_prop.a2n Yalla.nn_prop.n2a
        (classical_linear_sequent Gamma))) in H.
    simpl in H.
    rewrite Yalla.subs.repl_at_eq in H.
    rewrite (Yalla.subs.subs_fresh_list
      Yalla.nn_prop.a2n Yalla.nn_prop.n2a
      Yalla.nn_prop.n2n_a) in H.
    exact H.
    apply Yalla.nn_def.a2a_i.
Qed.

Lemma translate_mell_fragment : forall Gamma,
  fst (translate_mell Gamma) = [].
Proof. reflexivity. Qed.

Definition iformula_eq_dec := runtime_iformula_eq_dec.

Definition raw_ilz_subformulas := raw_runtime_ilz_subformulas.

Definition ilz_goal_formulas := runtime_ilz_goal_formulas.

Definition ilz_subformulas := runtime_ilz_subformulas.

Lemma raw_ilz_subformulas_sound : forall A B,
  In B (raw_ilz_subformulas A) -> IF.isubform B A.
Proof.
  induction A; intros B Hin; simpl in Hin.
  - destruct Hin as [<- | []]. constructor.
  - destruct Hin as [<- | []]. constructor.
  - destruct Hin as [<- | Hin]; [constructor|].
    apply in_app_iff in Hin as [Hin|Hin].
    + apply IF.isub_tens_l. now apply IHA1.
    + apply IF.isub_tens_r. now apply IHA2.
  - destruct Hin as [<- | Hin]; [constructor|].
    apply in_app_iff in Hin as [Hin|Hin].
    + apply IF.isub_lpam_l. now apply IHA1.
    + apply IF.isub_lpam_r. now apply IHA2.
  - destruct Hin as [<- | [<- | Hin]].
    + constructor.
    + apply IF.isub_gen_N.
    + apply IF.isub_gen. now apply IHA.
  - destruct Hin as [<- | Hin]; [constructor|].
    apply in_app_iff in Hin as [Hin|Hin].
    + apply IF.isub_lmap_l. now apply IHA1.
    + apply IF.isub_lmap_r. now apply IHA2.
  - destruct Hin as [<- | [<- | Hin]].
    + constructor.
    + apply IF.isub_neg_N.
    + apply IF.isub_neg. now apply IHA.
  - destruct Hin as [<- | []]. constructor.
  - destruct Hin as [<- | Hin]; [constructor|].
    apply in_app_iff in Hin as [Hin|Hin].
    + apply IF.isub_with_l. now apply IHA1.
    + apply IF.isub_with_r. now apply IHA2.
  - destruct Hin as [<- | []]. constructor.
  - destruct Hin as [<- | Hin]; [constructor|].
    apply in_app_iff in Hin as [Hin|Hin].
    + apply IF.isub_plus_l. now apply IHA1.
    + apply IF.isub_plus_r. now apply IHA2.
  - destruct Hin as [<- | Hin]; [constructor|].
    apply IF.isub_oc. now apply IHA.
Qed.

Lemma raw_ilz_subformulas_complete : forall A B,
  IF.isubform B A -> In B (raw_ilz_subformulas A).
Proof.
  intros A B H; induction H.
  - destruct A; simpl; auto.
  - simpl. right. apply in_app_iff. auto.
  - simpl. right. apply in_app_iff. auto.
  - simpl. right. apply in_app_iff. auto.
  - simpl. right. apply in_app_iff. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. right. apply in_app_iff. auto.
  - simpl. right. apply in_app_iff. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. right. apply in_app_iff. auto.
  - simpl. right. apply in_app_iff. auto.
  - simpl. right. apply in_app_iff. auto.
  - simpl. right. apply in_app_iff. auto.
  - simpl. auto.
Qed.

Theorem ilz_subformulas_sound : forall goal A,
  In A (ilz_subformulas goal) ->
  exists B, In B (ilz_goal_formulas goal) /\ IF.isubform A B.
Proof.
  intros goal A Hin.
  unfold ilz_subformulas, runtime_ilz_subformulas in Hin.
  rewrite nodup_In in Hin.
  apply in_flat_map in Hin as [B [HB HA]].
  exists B; split; auto using raw_ilz_subformulas_sound.
Qed.

Theorem ilz_subformulas_complete : forall goal A B,
  In B (ilz_goal_formulas goal) -> IF.isubform A B ->
  In A (ilz_subformulas goal).
Proof.
  intros goal A B HB HA.
  unfold ilz_subformulas, runtime_ilz_subformulas.
  rewrite nodup_In.
  apply in_flat_map.
  exists B; split; auto using raw_ilz_subformulas_complete.
Qed.

Theorem ilz_subformulas_nodup : forall goal,
  NoDup (ilz_subformulas goal).
Proof. intro goal; apply NoDup_nodup. Qed.
