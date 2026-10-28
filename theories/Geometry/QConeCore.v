From Coq Require Import Fin Lia List QArith QArith.Qabs Qring Vector VectorSpec ZArith.
From Mell.Geometry Require Import MathCompBridge RationalDefinability.

Import ListNotations.
Open Scope Q_scope.

Definition QVecEq {d} : QVec d -> QVec d -> Prop := @qvec_eq d.

Lemma qvec_eq_zero : forall d, QVecEq (qvec_zero d) (qvec_zero d).
Proof. intros d index; reflexivity. Qed.

Lemma qvec_eq_add : forall d (x x' y y' : QVec d),
    QVecEq x x' -> QVecEq y y' ->
    QVecEq (qvec_add x y) (qvec_add x' y').
Proof.
  intros d x x' y y' Hx Hy index. unfold qvec_add.
  now apply Qplus_comp.
Qed.

Lemma qvec_eq_scale : forall d coefficient coefficient'
    (x x' : QVec d),
    coefficient == coefficient' -> QVecEq x x' ->
    QVecEq (qvec_scale coefficient x) (qvec_scale coefficient' x').
Proof.
  intros d coefficient coefficient' x x' Hcoefficient Hx index.
  unfold qvec_scale. now apply Qmult_comp.
Qed.

Inductive QConeCombination {d} (generators : list (QVec d)) :
    QVec d -> Prop :=
| qcone_combination_zero : QConeCombination generators (qvec_zero d)
| qcone_combination_add : forall coefficient generator tail,
    0 <= coefficient ->
    List.In generator generators ->
    QConeCombination generators tail ->
    QConeCombination generators
      (qvec_add (qvec_scale coefficient generator) tail).

Definition qcone_generated {d} (generators : list (QVec d))
    (point : QVec d) : Prop :=
  exists generated,
    QConeCombination generators generated /\ QVecEq point generated.

Lemma qcone_generated_qvec_ext : forall d (generators : list (QVec d))
    left right,
    QVecEq left right ->
    (qcone_generated generators left <-> qcone_generated generators right).
Proof.
  intros d generators left right Heq. split.
  - intros [generated [Hgenerated Hpoint]]. exists generated. split.
    + exact Hgenerated.
    + eapply qvec_eq_trans; [apply qvec_eq_sym; exact Heq|exact Hpoint].
  - intros [generated [Hgenerated Hpoint]]. exists generated. split.
    + exact Hgenerated.
    + eapply qvec_eq_trans; [exact Heq|exact Hpoint].
Qed.

Definition SameSet {A : Type} (left right : A -> Prop) : Prop :=
  forall value, left value <-> right value.

Record IsCone {d} (set : QSet d) : Prop := {
  cone_contains_zero : set (qvec_zero d);
  cone_closed_add : forall left right,
    set left -> set right -> set (qvec_add left right);
  cone_closed_scale : forall coefficient value,
    0 <= coefficient -> set value -> set (qvec_scale coefficient value)
}.

Definition QClosure {d} (set : QSet d) (point : QVec d) : Prop :=
  forall delta : Q, 0 < delta ->
    exists approximant,
      set approximant /\
      forall index, Qabs (point index - approximant index) < delta.

Definition TopologicallyClosed {d} (set : QSet d) : Prop :=
  forall point, QClosure set point -> set point.

Lemma qcone_generated_zero : forall d (generators : list (QVec d)),
    qcone_generated generators (qvec_zero d).
Proof.
  intros d generators. exists (qvec_zero d). split.
  - constructor.
  - apply qvec_eq_refl.
Qed.

Lemma qcone_generated_generator : forall d (generators : list (QVec d))
    (generator : QVec d),
    List.In generator generators -> qcone_generated generators generator.
Proof.
  intros d generators generator Hin.
  exists (qvec_add (qvec_scale 1 generator) (qvec_zero d)). split.
  - constructor; [unfold Qle; cbn; lia|exact Hin|constructor].
  - intro index. unfold qvec_add, qvec_scale, qvec_zero.
    setoid_rewrite Qmult_1_l. symmetry. apply Qplus_0_r.
Qed.

Lemma qcone_combination_scale : forall d (generators : list (QVec d))
    (value : QVec d) coefficient,
    QConeCombination generators value -> 0 <= coefficient ->
    exists scaled, QConeCombination generators scaled /\
      QVecEq scaled (qvec_scale coefficient value).
Proof.
  intros d generators value coefficient Hvalue Hcoefficient.
  induction Hvalue.
  - exists (qvec_zero d). split; [constructor|].
    intro index. unfold qvec_scale, qvec_zero. ring.
  - destruct IHHvalue as [scaled [Hscaled Hscaled_eq]].
    exists (qvec_add (qvec_scale (coefficient * coefficient0) generator)
      scaled). split.
    + constructor.
      * apply Qmult_le_0_compat; assumption.
      * exact H0.
      * exact Hscaled.
    + intro index. unfold qvec_scale, qvec_add in *.
      specialize (Hscaled_eq index). setoid_rewrite Hscaled_eq. ring.
Qed.

Lemma qcone_combination_plus : forall d (generators : list (QVec d))
    (left right : QVec d),
    QConeCombination generators left ->
    QConeCombination generators right ->
    exists sum, QConeCombination generators sum /\
      QVecEq sum (qvec_add left right).
Proof.
  intros d generators left right Hleft Hright.
  induction Hleft.
  - exists right. split; [exact Hright|]. intro index.
    unfold qvec_add, qvec_zero. symmetry. apply Qplus_0_l.
  - destruct IHHleft as [sum [Hsum Heq]].
    exists (qvec_add (qvec_scale coefficient generator) sum). split.
    + constructor; assumption.
    + intro index. unfold qvec_add in *. specialize (Heq index).
      setoid_rewrite Heq. apply Qplus_assoc.
Qed.

Lemma qcone_generated_add : forall d (generators : list (QVec d))
    (left right : QVec d),
    qcone_generated generators left ->
    qcone_generated generators right ->
    qcone_generated generators (qvec_add left right).
Proof.
  intros d generators left right
    [left' [Hleft Hleft_eq]] [right' [Hright Hright_eq]].
  destruct (qcone_combination_plus d generators left' right' Hleft Hright)
    as [sum [Hsum Hsum_eq]].
  exists sum. split; [exact Hsum|].
  eapply (@qvec_eq_trans d _ (qvec_add left' right') _).
  - apply qvec_eq_add; [exact Hleft_eq|exact Hright_eq].
  - apply qvec_eq_sym. exact Hsum_eq.
Qed.

Lemma qcone_generated_scale : forall d (generators : list (QVec d))
    coefficient (value : QVec d),
    0 <= coefficient ->
    qcone_generated generators value ->
    qcone_generated generators (qvec_scale coefficient value).
Proof.
  intros d generators coefficient value Hcoefficient
    [generated [Hgenerated Heq]].
  destruct (qcone_combination_scale d generators generated coefficient
    Hgenerated Hcoefficient) as [scaled [Hscaled Hscaled_eq]].
  exists scaled. split; [exact Hscaled|].
  eapply (@qvec_eq_trans d _ (qvec_scale coefficient generated) _).
  - apply qvec_eq_scale; [reflexivity|exact Heq].
  - apply qvec_eq_sym. exact Hscaled_eq.
Qed.

Lemma qcone_generated_is_cone : forall d (generators : list (QVec d)),
    IsCone (@qcone_generated d generators).
Proof.
  intros. constructor.
  - apply qcone_generated_zero.
  - apply qcone_generated_add.
  - apply qcone_generated_scale.
Qed.

Definition QEnvironmentEq (left right : QEnvironment) : Prop :=
  forall variable, left variable == right variable.

Lemma qterm_semantics_qeq : forall term left right,
    QEnvironmentEq left right ->
    qterm_semantics left term == qterm_semantics right term.
Proof.
  intro term. induction term; intros left right Hagree; cbn.
  - apply Hagree.
  - reflexivity.
  - apply Qplus_comp; auto.
  - apply Qopp_comp; auto.
  - apply Qmult_comp; [reflexivity|auto].
Qed.

Lemma qformula_semantics_qeq : forall formula left right,
    QEnvironmentEq left right ->
    (qformula_semantics left formula <-> qformula_semantics right formula).
Proof.
  intro formula. induction formula; intros left right Hagree; cbn; try tauto.
  - pose proof (qterm_semantics_qeq q left right Hagree) as Hl.
    pose proof (qterm_semantics_qeq q0 left right Hagree) as Hr.
    split; intro H.
    + transitivity (qterm_semantics left q); [symmetry; exact Hl|].
      transitivity (qterm_semantics left q0); [exact H|exact Hr].
    + transitivity (qterm_semantics right q); [exact Hl|].
      transitivity (qterm_semantics right q0); [exact H|symmetry; exact Hr].
  - setoid_rewrite (qterm_semantics_qeq q left right Hagree).
    setoid_rewrite (qterm_semantics_qeq q0 left right Hagree). reflexivity.
  - setoid_rewrite (qterm_semantics_qeq q left right Hagree).
    setoid_rewrite (qterm_semantics_qeq q0 left right Hagree). reflexivity.
  - rewrite (IHformula1 left right Hagree),
      (IHformula2 left right Hagree). reflexivity.
  - rewrite (IHformula1 left right Hagree),
      (IHformula2 left right Hagree). reflexivity.
  - rewrite (IHformula left right Hagree). reflexivity.
  - split; intros [value Hvalue]; exists value.
    + assert (Hextend : QEnvironmentEq (qenvironment_extend left value)
          (qenvironment_extend right value)).
      { intros [|variable]; cbn; [reflexivity|apply Hagree]. }
      now apply (proj1 (IHformula _ _ Hextend)).
    + assert (Hextend : QEnvironmentEq (qenvironment_extend left value)
          (qenvironment_extend right value)).
      { intros [|variable]; cbn; [reflexivity|apply Hagree]. }
      now apply (proj2 (IHformula _ _ Hextend)).
  - split; intros Hall value.
    + assert (Hextend : QEnvironmentEq (qenvironment_extend left value)
          (qenvironment_extend right value)).
      { intros [|variable]; cbn; [reflexivity|apply Hagree]. }
      apply (proj1 (IHformula _ _ Hextend)). apply Hall.
    + assert (Hextend : QEnvironmentEq (qenvironment_extend left value)
          (qenvironment_extend right value)).
      { intros [|variable]; cbn; [reflexivity|apply Hagree]. }
      apply (proj2 (IHformula _ _ Hextend)). apply Hall.
Qed.

Lemma qvec_environment_qeq : forall d (left right : QVec d),
    QVecEq left right ->
    QEnvironmentEq (qvec_environment left) (qvec_environment right).
Proof.
  intros d left right Heq variable.
  destruct (lt_dec variable d) as [Hinside|Houtside].
  - pose (index := Fin.of_nat_lt Hinside).
    replace variable with (proj1_sig (Fin.to_nat index)).
    2: { unfold index. now rewrite Fin.to_nat_of_nat. }
    rewrite !qvec_environment_inside. apply Heq.
  - replace variable with (d + (variable - d))%nat by lia.
    unfold qvec_environment. rewrite !qvec_bind_environment_outside.
    reflexivity.
Qed.

Lemma qdefinable_qvec_extensional : forall d (set : QSet d),
    QDefinable set -> forall left right,
      QVecEq left right -> (set left <-> set right).
Proof.
  intros d set [formula [Hclosed Hformula]] left right Heq.
  rewrite (Hformula left), (Hformula right).
  apply qformula_semantics_qeq. now apply qvec_environment_qeq.
Qed.
