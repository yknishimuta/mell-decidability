From Coq Require Import List ZArith Lia Bool.
From Yalla.OLlibs Require Import Permutation_Type.
From Mell.Logic Require Import Syntax Calculus.

Import ListNotations.
Open Scope Z_scope.

Fixpoint multiplicative_formula (formula : formula) : bool :=
  match formula with
  | Atom _ | CoAtom _ | One | Bottom => true
  | Tensor left_formula right_formula =>
      multiplicative_formula left_formula && multiplicative_formula right_formula
  | Par left_formula right_formula =>
      multiplicative_formula left_formula && multiplicative_formula right_formula
  | Bang _ | WhyNot _ => false
  end.

Definition multiplicative_sequent (Gamma : sequent) : bool :=
  List.forallb multiplicative_formula Gamma.

Fixpoint formula_weight (formula : formula) : Z :=
  match formula with
  | Atom _ => 0
  | CoAtom _ => 1
  | One => 1
  | Bottom => 0
  | Tensor left_formula right_formula =>
      formula_weight left_formula + formula_weight right_formula - 1
  | Par left_formula right_formula =>
      formula_weight left_formula + formula_weight right_formula
  | Bang body | WhyNot body => formula_weight body
  end.

Fixpoint sequent_weight (Gamma : sequent) : Z :=
  match Gamma with
  | [] => 0
  | formula :: Gamma' => formula_weight formula + sequent_weight Gamma'
  end.

Lemma multiplicative_formula_spec : forall formula,
  multiplicative_formula formula = true <->
  match formula with
  | Bang _ | WhyNot _ => False
  | Tensor left_formula right_formula =>
      multiplicative_formula left_formula = true /\
      multiplicative_formula right_formula = true
  | Par left_formula right_formula =>
      multiplicative_formula left_formula = true /\
      multiplicative_formula right_formula = true
  | _ => True
  end.
Proof.
  intros formula; destruct formula; cbn; try tauto.
  - apply Bool.andb_true_iff.
  - apply Bool.andb_true_iff.
  - split; [discriminate|contradiction].
  - split; [discriminate|contradiction].
Qed.

Lemma multiplicative_sequent_spec : forall Gamma,
  multiplicative_sequent Gamma = true <->
  List.Forall (fun formula => multiplicative_formula formula = true) Gamma.
Proof.
  intro Gamma. unfold multiplicative_sequent.
  rewrite forallb_forall, List.Forall_forall. reflexivity.
Qed.

Lemma sequent_weight_app : forall left right,
  sequent_weight (left ++ right) = sequent_weight left + sequent_weight right.
Proof.
  intros left; induction left as [|head tail IH]; intro right; cbn.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma sequent_weight_permutation_type : forall left right,
  Permutation_Type left right -> sequent_weight left = sequent_weight right.
Proof.
  intros left right Hperm. induction Hperm; cbn; lia.
Qed.

Lemma forall_permutation_type : forall (P : formula -> Prop) left right,
  Permutation_Type left right -> List.Forall P right -> List.Forall P left.
Proof.
  intros P left right Hperm. induction Hperm; intro Hforall.
  - constructor.
  - inversion Hforall; subst. constructor; auto.
  - inversion Hforall as [|? ? Hx Htail]; subst.
    inversion Htail as [|? ? Hy Hrest]; subst.
    repeat constructor; assumption.
  - apply IHHperm1. now apply IHHperm2.
Qed.

Theorem multiplicative_derivation_weight : forall Gamma,
  Derivation Gamma ->
  List.Forall (fun formula => multiplicative_formula formula = true) Gamma ->
  sequent_weight Gamma = 1.
Proof.
  intros Gamma derivation. induction derivation; intro Hmultiplicative.
  - reflexivity.
  - reflexivity.
  - pose proof (Forall_inv_tail Hmultiplicative) as Htail.
    cbn. specialize (IHderivation Htail). lia.
  - inversion Hmultiplicative as [|? ? Htensor Hcontexts]; subst.
    apply multiplicative_formula_spec in Htensor.
    destruct Htensor as [HA HB].
    apply List.Forall_app in Hcontexts.
    destruct Hcontexts as [HGamma HDelta].
    specialize (IHderivation1 (Forall_cons A HA HGamma)).
    specialize (IHderivation2 (Forall_cons B HB HDelta)).
    cbn in IHderivation1, IHderivation2 |- *.
    rewrite sequent_weight_app. lia.
  - inversion Hmultiplicative as [|? ? Hpar Hcontext]; subst.
    apply multiplicative_formula_spec in Hpar.
    destruct Hpar as [HA HB].
    specialize (IHderivation (Forall_cons A HA (Forall_cons B HB Hcontext))).
    cbn in IHderivation |- *. lia.
  - inversion Hmultiplicative; discriminate.
  - inversion Hmultiplicative; discriminate.
  - inversion Hmultiplicative; discriminate.
  - inversion Hmultiplicative; discriminate.
  - rewrite <- (sequent_weight_permutation_type Gamma Delta p).
    apply IHderivation.
    eapply forall_permutation_type; eauto.
Qed.

Definition multiplicative_weight_refutes (Gamma : sequent) : bool :=
  multiplicative_sequent Gamma && negb (Z.eqb (sequent_weight Gamma) 1).

Theorem multiplicative_weight_refutes_sound : forall Gamma,
  multiplicative_weight_refutes Gamma = true -> ~ Provable Gamma.
Proof.
  intros Gamma Hrefutes [derivation].
  unfold multiplicative_weight_refutes in Hrefutes.
  apply Bool.andb_true_iff in Hrefutes.
  destruct Hrefutes as [Hmultiplicative Hweight].
  apply Bool.negb_true_iff, Z.eqb_neq in Hweight.
  apply Hweight. eapply multiplicative_derivation_weight; [exact derivation|].
  now apply multiplicative_sequent_spec.
Qed.
