From Coq Require Import List QArith Qring Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization LatticeGordanH
  LatticeGordanInterface LatticeGordanPullback MathCompBridge Periodic QConeCore.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Definition QSpan {d} (generators : list (ZVec d)) (value : QVec d) : Prop :=
  exists coefficients : Vector.t Q (length generators),
    QVecEq value (qgroup_combination generators coefficients).

Definition VecOf {d} (set : ZSet d) (value : QVec d) : Prop :=
  exists generators : list (ZVec d),
    List.Forall set generators /\ QSpan generators value.

Definition qvec_opp {d} (value : QVec d) : QVec d :=
  qvec_scale (-1) value.

Lemma qgroup_combination_zero_q : forall d
    (generators : list (ZVec d)),
    QVecEq
      (qgroup_combination generators
        (Vector.const 0 (length generators)))
      (qvec_zero d).
Proof.
  intros d generators. induction generators as [|generator generators IH].
  - apply qvec_eq_refl.
  - intro index. cbn. unfold qvec_add, qvec_scale, qvec_zero.
    transitivity
      (qgroup_combination generators
        (Vector.const 0 (length generators)) index).
    + ring.
    + apply IH.
Qed.

Lemma qspan_qvec_ext : forall d (generators : list (ZVec d)) left right,
    QVecEq left right -> (QSpan generators left <-> QSpan generators right).
Proof.
  intros d generators left right Heq. split.
  - intros [coefficients Hleft]. exists coefficients.
    eapply qvec_eq_trans; [apply qvec_eq_sym; exact Heq|exact Hleft].
  - intros [coefficients Hright]. exists coefficients.
    eapply qvec_eq_trans; [exact Heq|exact Hright].
Qed.

Lemma qspan_zero : forall d (generators : list (ZVec d)),
    QSpan generators (qvec_zero d).
Proof.
  intros d generators. exists (Vector.const 0 (length generators)).
  apply qvec_eq_sym, qgroup_combination_zero_q.
Qed.

Lemma qspan_nil_iff : forall d (value : QVec d),
    QSpan ([] : list (ZVec d)) value <-> QVecEq value (qvec_zero d).
Proof.
  intros d value. split.
  - intros [coefficients Hvalue].
    refine (Vector.case0 (fun coefficients =>
      QVecEq value (qgroup_combination [] coefficients) ->
      QVecEq value (qvec_zero d)) _ coefficients Hvalue).
    intro Hnil. exact Hnil.
  - intro Hvalue. exists (@Vector.nil Q). exact Hvalue.
Qed.

Lemma qspan_add : forall d (generators : list (ZVec d)) left right,
    QSpan generators left -> QSpan generators right ->
    QSpan generators (qvec_add left right).
Proof.
  intros d generators left right
    [left_coefficients Hleft] [right_coefficients Hright].
  exists (Vector.map2 Qplus left_coefficients right_coefficients).
  eapply qvec_eq_trans with (y := qvec_add
    (qgroup_combination generators left_coefficients)
    (qgroup_combination generators right_coefficients)).
  - apply qvec_eq_add; [exact Hleft|exact Hright].
  - apply qvec_eq_sym, qgroup_combination_add_q.
Qed.

Lemma qspan_scale : forall d (generators : list (ZVec d))
    coefficient value,
    QSpan generators value ->
    QSpan generators (qvec_scale coefficient value).
Proof.
  intros d generators coefficient value [coefficients Hvalue].
  exists (Vector.map (Qmult coefficient) coefficients).
  eapply qvec_eq_trans with (y := qvec_scale coefficient
    (qgroup_combination generators coefficients)).
  - apply qvec_eq_scale; [reflexivity|exact Hvalue].
  - apply qvec_eq_sym, qgroup_combination_scale_q.
Qed.

Lemma qspan_opp : forall d (generators : list (ZVec d)) value,
    QSpan generators value -> QSpan generators (qvec_opp value).
Proof. intros; now apply qspan_scale. Qed.

Lemma zvec_to_qvec_zero : forall d,
    QVecEq (zvec_to_qvec (zvec_zero d)) (qvec_zero d).
Proof.
  intros d index. unfold zvec_to_qvec, zvec_zero, qvec_zero.
  rewrite const_nth. reflexivity.
Qed.

Lemma zvec_to_qvec_zsmul : forall d coefficient (value : ZVec d),
    QVecEq (zvec_to_qvec (zvec_zsmul coefficient value))
      (qvec_scale (inject_Z coefficient) (zvec_to_qvec value)).
Proof.
  intros d coefficient value index.
  unfold zvec_to_qvec, qvec_scale. rewrite zvec_zsmul_nth, inject_Z_mult.
  reflexivity.
Qed.

Lemma zvec_to_qvec_sub : forall d (left right : ZVec d),
    QVecEq (zvec_to_qvec (zvec_sub left right))
      (qvec_add (zvec_to_qvec left) (qvec_opp (zvec_to_qvec right))).
Proof.
  intros d left right index.
  unfold zvec_to_qvec, zvec_sub, qvec_add, qvec_opp, qvec_scale.
  rewrite (nth_map2 Z.sub left right index index index eq_refl eq_refl),
    <- inject_Z_opp, <- inject_Z_plus. reflexivity.
Qed.

Lemma zgroup_generated_in_qspan : forall d
    (generators : list (ZVec d)) value,
    ZGroupGenerated generators value ->
    QSpan generators (zvec_to_qvec value).
Proof.
  intros d generators value [coefficients Hcoefficients].
  exists (Vector.map inject_Z coefficients).
  eapply qvec_eq_trans.
  - rewrite <- Hcoefficients. apply qvec_eq_refl.
  - apply qvec_eq_sym, qgroup_combination_inject.
Qed.

Lemma qspan_member : forall d (generators : list (ZVec d)) value,
    List.In value generators ->
    QSpan generators (zvec_to_qvec value).
Proof.
  intros d generators value Hin. apply zgroup_generated_in_qspan.
  apply zvec_generated_in_zgroup_generated, generated_generator. exact Hin.
Qed.

Lemma qspan_cons : forall d head (generators : list (ZVec d)) value,
    QSpan generators value -> QSpan (head :: generators) value.
Proof.
  intros d head generators value [coefficients Hvalue].
  exists (@Vector.cons Q 0 _ coefficients). intro index.
  specialize (Hvalue index). cbn. unfold qvec_add, qvec_scale.
  setoid_rewrite Hvalue. ring.
Qed.

Lemma qspan_sub_zvec : forall d (generators : list (ZVec d)) left right,
    QSpan generators (zvec_to_qvec left) ->
    QSpan generators (zvec_to_qvec right) ->
    QSpan generators (zvec_to_qvec (zvec_sub left right)).
Proof.
  intros d generators left right Hleft Hright.
  apply (proj2 (qspan_qvec_ext d generators _ _
    (zvec_to_qvec_sub d left right))).
  apply qspan_add; [exact Hleft|now apply qspan_opp].
Qed.

Lemma qgroup_combination_in_qspan : forall d
    (source target : list (ZVec d)) coefficients,
    (forall generator, List.In generator source ->
      QSpan target (zvec_to_qvec generator)) ->
    QSpan target (qgroup_combination source coefficients).
Proof.
  intros d source. induction source as [|generator source IH];
    intros target coefficients Hall.
  - refine (Vector.case0 (fun coefficients => _) _ coefficients).
    apply qspan_zero.
  - refine (Vector.caseS' coefficients (fun coefficients => _) _).
    intros coefficient tail. cbn.
    apply qspan_add.
    + apply qspan_scale. apply Hall. now left.
    + apply IH. intros value Hin. apply Hall. now right.
Qed.

Lemma zgroup_generated_in_qspan_over : forall d
    (source target : list (ZVec d)) value,
    (forall generator, List.In generator source ->
      QSpan target (zvec_to_qvec generator)) ->
    ZGroupGenerated source value ->
    QSpan target (zvec_to_qvec value).
Proof.
  intros d source target value Hall [coefficients Hcoefficients].
  subst value.
  apply (proj1 (qspan_qvec_ext d target _ _
    (qgroup_combination_inject d source coefficients))).
  apply qgroup_combination_in_qspan. exact Hall.
Qed.

Lemma difference_generators_spanning_sources : forall d (set : ZSet d)
    (generators : list (ZVec d)),
    (forall generator, List.In generator generators ->
      Difference set generator) ->
    exists sources : list (ZVec d),
      List.Forall set sources /\
      forall generator, List.In generator generators ->
        QSpan sources (zvec_to_qvec generator).
Proof.
  intros d set generators. induction generators as [|generator generators IH].
  - intros _. exists []. split; [constructor|contradiction].
  - intros Hall.
    destruct (Hall generator (or_introl eq_refl)) as
      [left [right [Hleft [Hright Hgenerator]]]].
    destruct (IH (fun value Hin => Hall value (or_intror Hin))) as
      [sources [Hsources Hspan]].
    exists (left :: right :: sources). split.
    + repeat constructor; assumption.
    + intros value [Heq|Hin].
      * subst value. rewrite Hgenerator.
        apply qspan_sub_zvec; apply qspan_member; simpl; auto.
      * apply qspan_cons, qspan_cons, Hspan. exact Hin.
Qed.

Lemma periodic_member_in_difference : forall d (set : ZSet d),
    Periodic set -> forall value, set value -> Difference set value.
Proof.
  intros d set [Hzero Hadd] value Hvalue.
  exists value, (zvec_zero d). repeat split; try assumption.
  apply zvec_ext. intro index. unfold zvec_sub, zvec_zero.
  rewrite (nth_map2 Z.sub _ _ index index index eq_refl eq_refl),
    const_nth. ring.
Qed.

Theorem finite_p_spanning : forall d (set : ZSet d),
    Periodic set ->
    exists generators : list (ZVec d),
      List.Forall set generators /\
      forall value : QVec d,
        VecOf set value <-> QSpan generators value.
Proof.
  intros d set Hperiodic.
  destruct (difference_group_finitely_generated d set Hperiodic) as
    [difference_generators Hdifference].
  assert (Hall_difference : forall generator,
      List.In generator difference_generators -> Difference set generator).
  { intros generator Hin. apply (proj2 (Hdifference generator)).
    apply zvec_generated_in_zgroup_generated, generated_generator. exact Hin. }
  destruct (difference_generators_spanning_sources d set
    difference_generators Hall_difference) as
    [generators [Hgenerators Hspan_difference]].
  exists generators. split; [exact Hgenerators|]. intro value. split.
  - intros [sources [Hsources [coefficients Hvalue]]].
    apply (proj2 (qspan_qvec_ext d generators _ _ Hvalue)).
    apply qgroup_combination_in_qspan.
    intros source Hin.
    assert (Hsource : set source).
    { exact (proj1 (List.Forall_forall set sources) Hsources source Hin). }
    apply zgroup_generated_in_qspan_over with
      (source := difference_generators).
    + exact Hspan_difference.
    + apply (proj1 (Hdifference source)).
      now apply periodic_member_in_difference.
  - intro Hvalue. exists generators. split; assumption.
Qed.
