From Coq Require Import Bool Fin Lia List QArith.
From Mell.Geometry Require Import MathCompBridge.

Open Scope Q_scope.

Definition QSet (d : nat) := QVec d -> Prop.
Definition QEnvironment := nat -> Q.

Inductive QTerm : Type :=
| QTVar : nat -> QTerm
| QTConst : Q -> QTerm
| QTAdd : QTerm -> QTerm -> QTerm
| QTOpp : QTerm -> QTerm
| QTScale : Q -> QTerm -> QTerm.

Inductive QFormula : Type :=
| QFTop : QFormula
| QFBot : QFormula
| QFEq : QTerm -> QTerm -> QFormula
| QFLt : QTerm -> QTerm -> QFormula
| QFLe : QTerm -> QTerm -> QFormula
| QFAnd : QFormula -> QFormula -> QFormula
| QFOr : QFormula -> QFormula -> QFormula
| QFNot : QFormula -> QFormula
| QFExists : QFormula -> QFormula
| QFForall : QFormula -> QFormula.

Definition qenvironment_extend
    (environment : QEnvironment) (value : Q) : QEnvironment :=
  fun variable =>
    match variable with
    | O => value
    | S variable' => environment variable'
    end.

Fixpoint qterm_semantics (environment : QEnvironment) (term : QTerm) : Q :=
  match term with
  | QTVar variable => environment variable
  | QTConst constant => constant
  | QTAdd lhs rhs =>
      qterm_semantics environment lhs + qterm_semantics environment rhs
  | QTOpp value => - qterm_semantics environment value
  | QTScale coefficient value =>
      coefficient * qterm_semantics environment value
  end.

Fixpoint qformula_semantics
    (environment : QEnvironment) (formula : QFormula) : Prop :=
  match formula with
  | QFTop => True
  | QFBot => False
  | QFEq lhs rhs =>
      qterm_semantics environment lhs == qterm_semantics environment rhs
  | QFLt lhs rhs =>
      qterm_semantics environment lhs < qterm_semantics environment rhs
  | QFLe lhs rhs =>
      qterm_semantics environment lhs <= qterm_semantics environment rhs
  | QFAnd lhs rhs =>
      qformula_semantics environment lhs /\ qformula_semantics environment rhs
  | QFOr lhs rhs =>
      qformula_semantics environment lhs \/ qformula_semantics environment rhs
  | QFNot body => ~ qformula_semantics environment body
  | QFExists body =>
      exists value : Q,
        qformula_semantics (qenvironment_extend environment value) body
  | QFForall body =>
      forall value : Q,
        qformula_semantics (qenvironment_extend environment value) body
  end.

Fixpoint qterm_closed (bound : nat) (term : QTerm) : bool :=
  match term with
  | QTVar variable => Nat.ltb variable bound
  | QTConst _ => true
  | QTAdd lhs rhs => qterm_closed bound lhs && qterm_closed bound rhs
  | QTOpp value => qterm_closed bound value
  | QTScale _ value => qterm_closed bound value
  end.

Fixpoint qformula_closed (bound : nat) (formula : QFormula) : bool :=
  match formula with
  | QFTop | QFBot => true
  | QFEq lhs rhs | QFLt lhs rhs | QFLe lhs rhs =>
      qterm_closed bound lhs && qterm_closed bound rhs
  | QFAnd lhs rhs | QFOr lhs rhs =>
      qformula_closed bound lhs && qformula_closed bound rhs
  | QFNot body => qformula_closed bound body
  | QFExists body | QFForall body => qformula_closed (S bound) body
  end.

Fixpoint qvec_bind_environment (d : nat) : QVec d -> QEnvironment -> QEnvironment :=
  match d return QVec d -> QEnvironment -> QEnvironment with
  | O => fun _ environment => environment
  | S d' => fun value environment =>
      qenvironment_extend
        (qvec_bind_environment d' (fun index => value (Fin.FS index)) environment)
        (value Fin.F1)
  end.

Definition qzero_environment : QEnvironment := fun _ => 0.

Definition qvec_environment {d} (value : QVec d) : QEnvironment :=
  qvec_bind_environment d value qzero_environment.

Lemma qvec_bind_environment_inside : forall d (value : QVec d)
    environment (index : Fin.t d),
    qvec_bind_environment d value environment (proj1_sig (Fin.to_nat index)) =
    value index.
Proof.
  intros d. induction d as [|d IH]; intros value environment index.
  - exact (Fin.case0 (fun index =>
      qvec_bind_environment 0 value environment
        (proj1_sig (Fin.to_nat index)) = value index) index).
  - refine (Fin.caseS' index
      (fun index => qvec_bind_environment (S d) value environment
        (proj1_sig (Fin.to_nat index)) = value index) _ _).
    + reflexivity.
    + intro tail_index.
      destruct (Fin.to_nat tail_index) as [coordinate Hcoordinate]
        eqn:Hto_nat.
      assert (Hsuccessor :
        proj1_sig (Fin.to_nat (Fin.FS tail_index)) = S coordinate).
      { cbn. rewrite Hto_nat. reflexivity. }
      rewrite Hsuccessor. cbn.
      pose proof (IH (fun index => value (Fin.FS index))
        environment tail_index) as Hinduction.
      rewrite Hto_nat in Hinduction. exact Hinduction.
Qed.

Lemma qvec_bind_environment_outside : forall d (value : QVec d)
    environment variable,
    qvec_bind_environment d value environment (d + variable)%nat =
    environment variable.
Proof.
  intros d. induction d as [|d IH]; intros value environment variable.
  - reflexivity.
  - cbn. apply IH.
Qed.

Lemma qvec_environment_inside : forall d (value : QVec d) (index : Fin.t d),
    qvec_environment value (proj1_sig (Fin.to_nat index)) = value index.
Proof. intros. apply qvec_bind_environment_inside. Qed.

Definition qenvironment_agree (bound : nat)
    (left right : QEnvironment) : Prop :=
  forall variable, (variable < bound)%nat -> left variable = right variable.

Lemma qvec_bind_environment_agree : forall d (value : QVec d) environment,
    qenvironment_agree d (qvec_environment value)
      (qvec_bind_environment d value environment).
Proof.
  intros d value environment variable Hvariable.
  destruct (lt_dec variable d) as [Hinside|Houtside]; [|lia].
  pose (index := Fin.of_nat_lt Hinside).
  replace variable with (proj1_sig (Fin.to_nat index)).
  2: { unfold index. rewrite Fin.to_nat_of_nat. reflexivity. }
  rewrite qvec_environment_inside, qvec_bind_environment_inside. reflexivity.
Qed.

Lemma qterm_semantics_agree : forall bound term left right,
    qterm_closed bound term = true ->
    qenvironment_agree bound left right ->
    qterm_semantics left term = qterm_semantics right term.
Proof.
  intros bound term. revert bound.
  induction term; intros bound left right Hclosed Hagree; cbn in *.
  - apply Nat.ltb_lt in Hclosed. apply Hagree. exact Hclosed.
  - reflexivity.
  - apply andb_true_iff in Hclosed as [Hleft Hright].
    rewrite (IHterm1 bound left right Hleft Hagree),
      (IHterm2 bound left right Hright Hagree). reflexivity.
  - rewrite (IHterm bound left right Hclosed Hagree). reflexivity.
  - rewrite (IHterm bound left right Hclosed Hagree). reflexivity.
Qed.

Lemma qformula_semantics_agree : forall bound formula left right,
    qformula_closed bound formula = true ->
    qenvironment_agree bound left right ->
    (qformula_semantics left formula <-> qformula_semantics right formula).
Proof.
  intros bound formula. revert bound.
  induction formula; intros bound left right Hclosed Hagree; cbn in *;
    try tauto.
  - apply andb_true_iff in Hclosed as [Hl Hr].
    rewrite (qterm_semantics_agree bound q left right Hl Hagree),
      (qterm_semantics_agree bound q0 left right Hr Hagree). reflexivity.
  - apply andb_true_iff in Hclosed as [Hl Hr].
    rewrite (qterm_semantics_agree bound q left right Hl Hagree),
      (qterm_semantics_agree bound q0 left right Hr Hagree). reflexivity.
  - apply andb_true_iff in Hclosed as [Hl Hr].
    rewrite (qterm_semantics_agree bound q left right Hl Hagree),
      (qterm_semantics_agree bound q0 left right Hr Hagree). reflexivity.
  - apply andb_true_iff in Hclosed as [Hl Hr].
    rewrite (IHformula1 bound left right Hl Hagree),
      (IHformula2 bound left right Hr Hagree). tauto.
  - apply andb_true_iff in Hclosed as [Hl Hr].
    rewrite (IHformula1 bound left right Hl Hagree),
      (IHformula2 bound left right Hr Hagree). tauto.
  - rewrite (IHformula bound left right Hclosed Hagree). tauto.
  - split; intros [value Hvalue]; exists value.
    + assert (Hextend : qenvironment_agree (S bound)
          (qenvironment_extend left value) (qenvironment_extend right value)).
      { intros [|variable] Hvariable; cbn; [reflexivity|].
        apply Hagree. lia. }
      apply (proj1 (IHformula (S bound) _ _ Hclosed Hextend)). exact Hvalue.
    + assert (Hextend : qenvironment_agree (S bound)
          (qenvironment_extend left value) (qenvironment_extend right value)).
      { intros [|variable] Hvariable; cbn; [reflexivity|].
        apply Hagree. lia. }
      apply (proj2 (IHformula (S bound) _ _ Hclosed Hextend)). exact Hvalue.
  - split; intros Hall value.
    + assert (Hextend : qenvironment_agree (S bound)
          (qenvironment_extend left value) (qenvironment_extend right value)).
      { intros [|variable] Hvariable; cbn; [reflexivity|].
        apply Hagree. lia. }
      apply (proj1 (IHformula (S bound) _ _ Hclosed Hextend)). apply Hall.
    + assert (Hextend : qenvironment_agree (S bound)
          (qenvironment_extend left value) (qenvironment_extend right value)).
      { intros [|variable] Hvariable; cbn; [reflexivity|].
        apply Hagree. lia. }
      apply (proj2 (IHformula (S bound) _ _ Hclosed Hextend)). apply Hall.
Qed.

Lemma qterm_closed_weaken : forall term small large,
    (small <= large)%nat -> qterm_closed small term = true ->
    qterm_closed large term = true.
Proof.
  intro term. induction term; intros small large Hle Hclosed; cbn in *; auto.
  - apply Nat.ltb_lt. apply Nat.ltb_lt in Hclosed. lia.
  - apply andb_true_iff in Hclosed as [Hl Hr]. apply andb_true_iff. split;
      [apply IHterm1 with small|apply IHterm2 with small]; assumption.
  - eapply IHterm; eauto.
  - eapply IHterm; eauto.
Qed.

Lemma qformula_closed_weaken : forall formula small large,
    (small <= large)%nat -> qformula_closed small formula = true ->
    qformula_closed large formula = true.
Proof.
  intro formula. induction formula; intros small large Hle Hclosed; cbn in *; auto;
    try (apply andb_true_iff in Hclosed as [Hl Hr]; apply andb_true_iff; split;
      [eapply qterm_closed_weaken|eapply qterm_closed_weaken]; eauto);
    try (apply andb_true_iff in Hclosed as [Hl Hr]; apply andb_true_iff; split;
      [eapply IHformula1|eapply IHformula2]; eauto).
  - eapply IHformula; eauto.
  - apply (IHformula (S small) (S large)); [lia|exact Hclosed].
  - apply (IHformula (S small) (S large)); [lia|exact Hclosed].
Qed.

Definition QDefinable {d} (set : QSet d) : Prop :=
  exists formula : QFormula,
    qformula_closed d formula = true /\
    forall value, set value <-> qformula_semantics (qvec_environment value) formula.

Fixpoint qexists_many (count : nat) (body : QFormula) : QFormula :=
  match count with
  | O => body
  | S count' => qexists_many count' (QFExists body)
  end.

Lemma qexists_many_closed : forall count free body,
    qformula_closed free (qexists_many count body) =
    qformula_closed (count + free)%nat body.
Proof.
  intros count. induction count as [|count IH]; intros free body; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Definition qvec_cons {d} (head : Q) (tail : QVec d) : QVec (S d) :=
  fun index => Fin.caseS' index (fun _ => Q) head tail.

Lemma qexists_many_intro : forall d body environment (value : QVec d),
    qformula_semantics (qvec_bind_environment d value environment) body ->
    qformula_semantics environment (qexists_many d body).
Proof.
  intros d. induction d as [|d IH]; intros body environment value Hbody.
  - exact Hbody.
  - cbn. apply (IH (QFExists body)
      environment (fun index => value (Fin.FS index))).
    exists (value Fin.F1). exact Hbody.
Qed.

Lemma qexists_many_elim : forall d body environment,
    qformula_semantics environment (qexists_many d body) ->
    exists value : QVec d,
      qformula_semantics (qvec_bind_environment d value environment) body.
Proof.
  intros d. induction d as [|d IH]; intros body environment Hbody.
  - exists (fun index => Fin.case0 (fun _ => Q) index). exact Hbody.
  - cbn in Hbody. apply IH in Hbody.
    destruct Hbody as [tail [head Hbody]].
    exists (qvec_cons head tail). exact Hbody.
Qed.

Fixpoint qprojection_constraints (d e total : nat)
    (coordinates : Fin.t e -> Fin.t total)
    (selection : Fin.t e -> Fin.t d) : QFormula :=
  match e as count return
      (Fin.t count -> Fin.t total) -> (Fin.t count -> Fin.t d) -> QFormula with
  | O => fun _ _ => QFTop
  | S count => fun coordinates selection =>
      QFAnd
        (QFEq
          (QTVar (d + proj1_sig (Fin.to_nat (coordinates Fin.F1)))%nat)
          (QTVar (proj1_sig (Fin.to_nat (selection Fin.F1)))))
        (qprojection_constraints d count total
          (fun index => coordinates (Fin.FS index))
          (fun index => selection (Fin.FS index)))
  end coordinates selection.

Lemma qprojection_constraints_closed : forall d e total coordinates selection,
    qformula_closed (d + total)%nat
      (qprojection_constraints d e total coordinates selection) = true.
Proof.
  intros d e. induction e as [|e IH]; intros total coordinates selection; cbn.
  - reflexivity.
  - repeat rewrite andb_true_iff. repeat split.
    + apply Nat.ltb_lt.
      pose proof (proj2_sig (Fin.to_nat (coordinates Fin.F1))) as Hcoordinate.
      exact (proj1 (Nat.add_lt_mono_l _ _ d) Hcoordinate).
    + apply Nat.ltb_lt.
      pose proof (proj2_sig (Fin.to_nat (selection Fin.F1))) as Hselection.
      exact (Nat.lt_le_trans _ _ _ Hselection (Nat.le_add_r d total)).
    + apply IH.
Qed.

Lemma qprojection_constraints_correct : forall d e total
    (coordinates : Fin.t e -> Fin.t total)
    (selection : Fin.t e -> Fin.t d) (source : QVec d) (target : QVec total),
    qformula_semantics
      (qvec_bind_environment d source (qvec_environment target))
      (qprojection_constraints d e total coordinates selection) <->
    forall index, target (coordinates index) == source (selection index).
Proof.
  intros d e. induction e as [|e IH];
    intros total coordinates selection source target; cbn.
  - split; [intros _ index; exact (Fin.case0 (fun _ => _) index)|intro; exact I].
  - rewrite qvec_bind_environment_outside,
      qvec_environment_inside, qvec_bind_environment_inside.
    rewrite IH. split.
    + intros [Hhead Htail] index.
      refine (Fin.caseS' index (fun index =>
        target (coordinates index) == source (selection index)) _ _).
      * exact Hhead.
      * exact Htail.
    + intro Hall. split; [apply (Hall Fin.F1)|].
      intro index. apply (Hall (Fin.FS index)).
Qed.

Definition qprojection_formula {d e}
    (selection : Fin.t e -> Fin.t d) (body : QFormula) : QFormula :=
  qexists_many d
    (QFAnd body
      (qprojection_constraints d e e (fun index => index) selection)).

Theorem qdefinable_projection :
  forall d e (f : Fin.t e -> Fin.t d) (X : QSet d),
    QDefinable X ->
    QDefinable (fun y => exists x, X x /\
      forall i, y i == x (f i)).
Proof.
  intros d e f X [body [Hclosed Hbody]].
  exists (qprojection_formula f body). split.
  - unfold qprojection_formula. rewrite qexists_many_closed. cbn.
    apply andb_true_iff. split.
    + eapply qformula_closed_weaken; [apply Nat.le_add_r|exact Hclosed].
    + apply qprojection_constraints_closed.
  - intro target. unfold qprojection_formula. split.
    + intros [source [HX Hcoordinates]].
      apply (qexists_many_intro d
        (QFAnd body
          (qprojection_constraints d e e (fun index => index) f))
        (qvec_environment target) source). cbn. split.
      * apply (proj1 (qformula_semantics_agree d body
          (qvec_environment source)
          (qvec_bind_environment d source (qvec_environment target))
          Hclosed (qvec_bind_environment_agree d source _))).
        apply (proj1 (Hbody source)). exact HX.
      * apply (proj2 (qprojection_constraints_correct d e e
          (fun index => index) f source target)). exact Hcoordinates.
    + intro Hprojected. apply qexists_many_elim in Hprojected.
      destruct Hprojected as [source [Hsource Hcoordinates]].
      exists source. split.
      * apply (proj2 (Hbody source)).
        apply (proj2 (qformula_semantics_agree d body
          (qvec_environment source)
          (qvec_bind_environment d source (qvec_environment target))
          Hclosed (qvec_bind_environment_agree d source _))). exact Hsource.
      * apply (proj1 (qprojection_constraints_correct d e e
          (fun index => index) f source target)). exact Hcoordinates.
Qed.

Theorem qdefinable_intersection :
  forall d (X Y : QSet d),
    QDefinable X -> QDefinable Y ->
    QDefinable (fun x => X x /\ Y x).
Proof.
  intros d X Y [left [Hleft_closed Hleft]] [right [Hright_closed Hright]].
  exists (QFAnd left right). split.
  - cbn. apply andb_true_iff. auto.
  - intro value. cbn. rewrite <- Hleft, <- Hright. reflexivity.
Qed.
