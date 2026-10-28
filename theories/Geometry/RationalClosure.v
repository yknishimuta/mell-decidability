From Coq Require Import Bool Fin Field Lia List QArith QArith.Qabs Qfield
  Qring Vector VectorSpec.
From Mell.Geometry Require Import MathCompBridge QConeCore
  RationalDefinability.

Open Scope Q_scope.

Definition qclosure_environment {d} (point : QVec d) (delta : Q)
    (approximant : QVec d) : QEnvironment :=
  qvec_bind_environment d approximant
    (qenvironment_extend (qvec_environment point) delta).

Fixpoint qneighborhood_formula (count dimension : nat) : QFormula :=
  match count with
  | O => QFTop
  | S count' =>
      QFAnd
        (QFLt
          (QTAdd (QTVar (dimension + 1 + count'))
            (QTOpp (QTVar dimension)))
          (QTVar count'))
        (QFAnd
          (QFLt
            (QTVar count')
            (QTAdd (QTVar (dimension + 1 + count'))
              (QTVar dimension)))
          (qneighborhood_formula count' dimension))
  end.

Definition qclosure_formula (dimension : nat) (body : QFormula) : QFormula :=
  QFForall
    (QFOr
      (QFLe (QTVar 0) (QTConst 0))
      (qexists_many dimension
        (QFAnd body (qneighborhood_formula dimension dimension)))).

Lemma qneighborhood_formula_closed : forall count dimension,
    (count <= dimension)%nat ->
    qformula_closed (dimension + S dimension)
      (qneighborhood_formula count dimension) = true.
Proof.
  intros count. induction count as [|count IH]; intros dimension Hcount; cbn.
  - reflexivity.
  - repeat rewrite andb_true_iff. repeat split; apply Nat.ltb_lt || apply IH;
      lia.
Qed.

Lemma qclosure_formula_closed : forall dimension body,
    qformula_closed dimension body = true ->
    qformula_closed dimension (qclosure_formula dimension body) = true.
Proof.
  intros dimension body Hbody. unfold qclosure_formula. cbn.
  rewrite qexists_many_closed. cbn. apply andb_true_iff. split.
  - eapply qformula_closed_weaken; [|exact Hbody]. lia.
  - apply qneighborhood_formula_closed. lia.
Qed.

Lemma qvec_bind_environment_prefix_agree : forall d (value : QVec d)
    environment variable,
    (variable < d)%nat ->
    qvec_bind_environment d value environment variable =
      qvec_environment value variable.
Proof.
  intros d. induction d as [|d IH]; intros value environment variable Hvariable.
  - lia.
  - destruct variable as [|variable].
    + reflexivity.
    + cbn. apply IH. lia.
Qed.

Lemma fin_of_nat_lt_value : forall (d variable : nat)
    (Hvariable : (variable < d)%nat),
    proj1_sig (Fin.to_nat (Fin.of_nat_lt Hvariable)) = variable.
Proof.
  intros d variable. revert d.
  induction variable as [|variable IH]; intros [|d] Hvariable; try lia.
  - reflexivity.
  - cbn.
    remember (proj2 (Nat.succ_lt_mono variable d) Hvariable) as Htail.
    destruct (Fin.to_nat (Fin.of_nat_lt Htail)) as [coordinate Hcoordinate]
      eqn:Hto_nat. cbn. f_equal.
    pose proof (IH d Htail) as Hinduction.
    rewrite Hto_nat in Hinduction. exact Hinduction.
Qed.

Lemma qclosure_environment_approximant : forall d (point approximant : QVec d)
    delta variable,
    (variable < d)%nat ->
    qclosure_environment point delta approximant variable =
      qvec_environment approximant variable.
Proof.
  intros d point approximant delta variable Hvariable.
  apply qvec_bind_environment_prefix_agree. exact Hvariable.
Qed.

Lemma qclosure_environment_delta : forall d (point approximant : QVec d)
    delta,
    qclosure_environment point delta approximant d = delta.
Proof.
  intros. unfold qclosure_environment.
  pose proof (qvec_bind_environment_outside d approximant
    (qenvironment_extend (qvec_environment point) delta) 0) as Houtside.
  rewrite Nat.add_0_r in Houtside. exact Houtside.
Qed.

Lemma qclosure_environment_point : forall d (point approximant : QVec d)
    delta variable,
    qclosure_environment point delta approximant (d + 1 + variable)%nat =
      qvec_environment point variable.
Proof.
  intros. unfold qclosure_environment.
  replace (d + 1 + variable)%nat with (d + S variable)%nat by lia.
  rewrite qvec_bind_environment_outside. reflexivity.
Qed.

Lemma qneighborhood_formula_correct_nat : forall count d
    (point approximant : QVec d) delta,
    (count <= d)%nat ->
    (qformula_semantics (qclosure_environment point delta approximant)
      (qneighborhood_formula count d) <->
     forall variable, (variable < count)%nat ->
       Qabs (qvec_environment point variable -
         qvec_environment approximant variable) < delta).
Proof.
  intros count. induction count as [|count IH]; intros d point approximant
      delta Hcount; cbn.
  - split.
    + intros _ variable Hvariable. lia.
    + intros _. exact I.
  - assert (Hcoordinate : (count < d)%nat) by lia.
    rewrite qclosure_environment_point,
      qclosure_environment_delta,
      qclosure_environment_approximant by exact Hcoordinate.
    rewrite (IH d point approximant delta) by lia.
    split.
    + intros [Hlower [Hupper Htail]] variable Hvariable.
      destruct (Nat.eq_dec variable count) as [->|Hneq].
      * apply (proj2 (Qabs_diff_Qlt_condition _ _ _)). now split.
      * apply Htail. lia.
    + intro Hall.
      pose proof (Hall count (Nat.lt_succ_diag_r count)) as Hhead.
      apply (proj1 (Qabs_diff_Qlt_condition _ _ _)) in Hhead.
      destruct Hhead as [Hlower Hupper]. split; [exact Hlower|]. split.
      * exact Hupper.
      * intros variable Hvariable. apply Hall. lia.
Qed.

Lemma qneighborhood_formula_correct : forall d (point approximant : QVec d)
    delta,
    (qformula_semantics (qclosure_environment point delta approximant)
      (qneighborhood_formula d d) <->
     forall index,
       Qabs (point index - approximant index) < delta).
Proof.
  intros d point approximant delta.
  rewrite qneighborhood_formula_correct_nat by lia. split.
  - intros Hall index.
    specialize (Hall (proj1_sig (Fin.to_nat index))
      (proj2_sig (Fin.to_nat index))).
    now rewrite !qvec_environment_inside in Hall.
  - intros Hall variable Hvariable.
    pose (index := Fin.of_nat_lt Hvariable).
    specialize (Hall index). unfold index in Hall.
    replace variable with (proj1_sig (Fin.to_nat (Fin.of_nat_lt Hvariable))).
    2: { apply fin_of_nat_lt_value. }
    now rewrite !qvec_environment_inside.
Qed.

Lemma qclosure_formula_correct : forall d (set : QSet d) body,
    qformula_closed d body = true ->
    (forall value,
      set value <-> qformula_semantics (qvec_environment value) body) ->
    forall point,
      QClosure set point <->
      qformula_semantics (qvec_environment point)
        (qclosure_formula d body).
Proof.
  intros d set body Hclosed Hbody point. unfold qclosure_formula. cbn. split.
  - intros Hclosure delta.
    destruct (Qlt_le_dec 0 delta) as [Hpositive|Hnonpositive].
    + right. destruct (Hclosure delta Hpositive) as
          [approximant [Hset Hnear]].
      apply (qexists_many_intro d
        (QFAnd body (qneighborhood_formula d d))
        (qenvironment_extend (qvec_environment point) delta) approximant).
      cbn. split.
      * apply (proj1 (qformula_semantics_agree d body
          (qvec_environment approximant)
          (qclosure_environment point delta approximant)
          Hclosed
          (fun variable Hvariable =>
            eq_sym (qvec_bind_environment_prefix_agree d approximant _
              variable Hvariable)))).
        apply (proj1 (Hbody approximant)). exact Hset.
      * apply (proj2 (qneighborhood_formula_correct d point approximant delta)).
        exact Hnear.
    + left. exact Hnonpositive.
  - intros Hformula delta Hpositive.
    specialize (Hformula delta). destruct Hformula as [Hnonpositive|Hexists].
    + exfalso. exact (Qlt_not_le _ _ Hpositive Hnonpositive).
    + apply qexists_many_elim in Hexists.
      destruct Hexists as [approximant [Hbody_semantics Hnear]].
      exists approximant. split.
      * apply (proj2 (Hbody approximant)).
        apply (proj2 (qformula_semantics_agree d body
          (qvec_environment approximant)
          (qclosure_environment point delta approximant)
          Hclosed
          (fun variable Hvariable =>
            eq_sym (qvec_bind_environment_prefix_agree d approximant _
              variable Hvariable)))).
        exact Hbody_semantics.
      * apply (proj1 (qneighborhood_formula_correct d point approximant delta)).
        exact Hnear.
Qed.

Theorem qclosure_qdefinable : forall d (set : QSet d),
    QDefinable set -> QDefinable (QClosure set).
Proof.
  intros d set [body [Hclosed Hbody]].
  exists (qclosure_formula d body). split.
  - now apply qclosure_formula_closed.
  - now apply qclosure_formula_correct.
Qed.

Lemma qclosure_qvec_extensional : forall d (set : QSet d) left right,
    QVecEq left right ->
    (QClosure set left <-> QClosure set right).
Proof.
  intros d set left right Heq. split.
  - intros Hclosure delta Hdelta.
    destruct (Hclosure delta Hdelta) as [approximant [Hset Hnear]].
    exists approximant. split; [exact Hset|]. intro index.
    setoid_rewrite <- (Heq index). apply Hnear.
  - intros Hclosure delta Hdelta.
    destruct (Hclosure delta Hdelta) as [approximant [Hset Hnear]].
    exists approximant. split; [exact Hset|]. intro index.
    setoid_rewrite (Heq index). apply Hnear.
Qed.

Lemma qclosure_extensive : forall d (set : QSet d) point,
    set point -> QClosure set point.
Proof.
  intros d set point Hpoint delta Hdelta. exists point. split; [exact Hpoint|].
  intro index. setoid_replace (point index - point index) with 0 by ring.
  setoid_replace (Qabs 0) with 0 by (apply Qabs_pos; apply Qle_refl).
  exact Hdelta.
Qed.

Lemma qclosure_monotone : forall d (left right : QSet d),
    (forall value, left value -> right value) ->
    forall point, QClosure left point -> QClosure right point.
Proof.
  intros d left right Hsubset point Hclosure delta Hdelta.
  destruct (Hclosure delta Hdelta) as [approximant [Hleft Hnear]].
  exists approximant. auto.
Qed.

Lemma qhalf_positive : forall delta : Q, 0 < delta -> 0 < delta / 2.
Proof.
  intros delta Hdelta. apply Qmult_lt_0_compat; [exact Hdelta|].
  reflexivity.
Qed.

Lemma qnear_add : forall left right left' right' delta : Q,
    Qabs (left - left') < delta / 2 ->
    Qabs (right - right') < delta / 2 ->
    Qabs ((left + right) - (left' + right')) < delta.
Proof.
  intros left right left' right' delta Hleft Hright.
  setoid_replace ((left + right) - (left' + right'))
    with ((left - left') + (right - right')) by ring.
  eapply Qle_lt_trans; [apply Qabs_triangle|].
  eapply Qlt_le_trans with (y := delta / 2 + delta / 2).
  - apply Qplus_lt_compat; assumption.
  - setoid_replace (delta / 2 + delta / 2) with delta by field.
    apply Qle_refl.
Qed.

Lemma qnear_scale : forall coefficient left right delta : Q,
    0 < coefficient ->
    Qabs (left - right) < delta / coefficient ->
    Qabs (coefficient * left - coefficient * right) < delta.
Proof.
  intros coefficient left right delta Hcoefficient Hnear.
  setoid_replace (coefficient * left - coefficient * right)
    with (coefficient * (left - right)) by ring.
  setoid_rewrite Qabs_Qmult.
  setoid_rewrite (Qabs_pos coefficient (Qlt_le_weak _ _ Hcoefficient)).
  assert (Hscaled : coefficient * Qabs (left - right) <
      coefficient * (delta / coefficient)).
  { setoid_replace (coefficient * Qabs (left - right))
      with (Qabs (left - right) * coefficient) by ring.
    setoid_replace (coefficient * (delta / coefficient))
      with ((delta / coefficient) * coefficient) by ring.
    now apply Qmult_lt_compat_r. }
  setoid_replace (coefficient * (delta / coefficient)) with delta in Hscaled.
  - exact Hscaled.
  - field. intro Hzero. apply (Qlt_not_eq _ _ Hcoefficient).
    symmetry. exact Hzero.
Qed.

Lemma qclosure_zero : forall d (set : QSet d),
    IsCone set -> QClosure set (qvec_zero d).
Proof.
  intros d set Hcone. apply qclosure_extensive.
  exact (cone_contains_zero set Hcone).
Qed.

Lemma qclosure_add : forall d (set : QSet d),
    IsCone set -> forall left right,
    QClosure set left -> QClosure set right ->
    QClosure set (qvec_add left right).
Proof.
  intros d set Hcone left right Hleft Hright delta Hdelta.
  destruct (Hleft (delta / 2) (qhalf_positive delta Hdelta)) as
    [left' [Hleft' Hleft_near]].
  destruct (Hright (delta / 2) (qhalf_positive delta Hdelta)) as
    [right' [Hright' Hright_near]].
  exists (qvec_add left' right'). split.
  - now apply (cone_closed_add set Hcone).
  - intro index. unfold qvec_add.
    now apply qnear_add.
Qed.

Lemma qclosure_scale : forall d (set : QSet d),
    IsCone set -> forall coefficient value,
    0 <= coefficient -> QClosure set value ->
    QClosure set (qvec_scale coefficient value).
Proof.
  intros d set Hcone coefficient value Hcoefficient Hvalue.
  destruct (Qle_lt_or_eq _ _ Hcoefficient) as [Hpositive|Hzero].
  - intros delta Hdelta.
    assert (Hscaled_delta : 0 < delta / coefficient).
    { apply Qmult_lt_0_compat; [exact Hdelta|].
      apply Qinv_lt_0_compat. exact Hpositive. }
    destruct (Hvalue (delta / coefficient) Hscaled_delta) as
      [approximant [Hset Hnear]].
    exists (qvec_scale coefficient approximant). split.
    + now apply (cone_closed_scale set Hcone).
    + intro index. unfold qvec_scale. now apply qnear_scale.
  - assert (Hcoefficient_zero : coefficient == 0) by
      (symmetry; exact Hzero).
    assert (Heq : QVecEq (qvec_zero d) (qvec_scale coefficient value)).
    { intro index. unfold qvec_zero, qvec_scale.
      setoid_rewrite Hcoefficient_zero. symmetry. apply Qmult_0_l. }
    apply (proj1 (qclosure_qvec_extensional d set
      (qvec_zero d) (qvec_scale coefficient value) Heq)).
    now apply qclosure_zero.
Qed.

Theorem qclosure_is_cone : forall d (set : QSet d),
    IsCone set -> IsCone (QClosure set).
Proof.
  intros d set Hcone. constructor.
  - now apply qclosure_zero.
  - now apply qclosure_add.
  - now apply qclosure_scale.
Qed.

Lemma qnear_trans : forall left middle right delta : Q,
    Qabs (left - middle) < delta / 2 ->
    Qabs (middle - right) < delta / 2 ->
    Qabs (left - right) < delta.
Proof.
  intros left middle right delta Hleft Hright.
  setoid_replace (left - right)
    with ((left - middle) + (middle - right)) by ring.
  eapply Qle_lt_trans; [apply Qabs_triangle|].
  eapply Qlt_le_trans with (y := delta / 2 + delta / 2).
  - apply Qplus_lt_compat; assumption.
  - setoid_replace (delta / 2 + delta / 2) with delta by field.
    apply Qle_refl.
Qed.

Lemma qclosure_idempotent : forall d (set : QSet d) point,
    QClosure (QClosure set) point -> QClosure set point.
Proof.
  intros d set point Houter delta Hdelta.
  destruct (Houter (delta / 2) (qhalf_positive delta Hdelta)) as
    [middle [Hmiddle Hpoint_middle]].
  destruct (Hmiddle (delta / 2) (qhalf_positive delta Hdelta)) as
    [approximant [Hset Hmiddle_approximant]].
  exists approximant. split; [exact Hset|]. intro index.
  eapply qnear_trans; [apply Hpoint_middle|apply Hmiddle_approximant].
Qed.

Theorem qclosure_topologically_closed : forall d (set : QSet d),
    TopologicallyClosed (QClosure set).
Proof.
  intros d set point Hclosure. now apply qclosure_idempotent.
Qed.
