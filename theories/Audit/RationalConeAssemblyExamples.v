From Coq Require Import Fin Lia List QArith QArith.Qabs Qring.
From Mell.Geometry Require Import MathCompBridge RationalDefinability
  QConeCore RationalHToV RationalQEOne RationalConeAssembly.

Import ListNotations.
Open Scope Q_scope.

Check rational_closed_cone_finitely_generated.

Definition assembly_all {d} : QSet d := fun _ => True.

Lemma assembly_all_definable : forall d, @QDefinable d assembly_all.
Proof.
  intro d. exists QFTop. split; [reflexivity|]. intro value. cbn. tauto.
Qed.

Lemma assembly_all_cone : forall d, @IsCone d assembly_all.
Proof.
  intro d. constructor.
  - exact I.
  - intros. exact I.
  - intros. exact I.
Qed.

Lemma assembly_all_closed : forall d, @TopologicallyClosed d assembly_all.
Proof. intros d point _. exact I. Qed.

Example assembly_dimension_zero :
  exists generators : list (QVec 0),
    SameSet assembly_all (qcone_generated generators).
Proof.
  apply rational_closed_cone_finitely_generated.
  - apply assembly_all_definable.
  - apply assembly_all_cone.
  - apply assembly_all_closed.
Qed.

Example assembly_full_space :
  exists generators : list (QVec 2),
    SameSet assembly_all (qcone_generated generators).
Proof.
  apply rational_closed_cone_finitely_generated.
  - apply assembly_all_definable.
  - apply assembly_all_cone.
  - apply assembly_all_closed.
Qed.

Definition first_coordinate : Fin.t 1 := Fin.F1.

Definition zero_cone : QSet 1 :=
  fun value => value first_coordinate == 0.

Lemma zero_cone_definable : QDefinable zero_cone.
Proof.
  exists (QFEq (QTVar 0) (QTConst 0)). split; [reflexivity|].
  intro value. cbn.
  change (value first_coordinate == 0 <->
    qvec_environment value (proj1_sig (Fin.to_nat first_coordinate)) == 0).
  rewrite qvec_environment_inside. reflexivity.
Qed.

Lemma zero_cone_cone : IsCone zero_cone.
Proof.
  constructor.
  - reflexivity.
  - intros left right Hleft Hright. unfold zero_cone, qvec_add in *.
    setoid_rewrite Hleft. setoid_rewrite Hright. ring.
  - intros coefficient value Hcoefficient Hvalue.
    unfold zero_cone, qvec_scale in *. setoid_rewrite Hvalue. ring.
Qed.

Lemma zero_cone_closed : TopologicallyClosed zero_cone.
Proof.
  intros point Hclosure. unfold zero_cone.
  destruct (Qlt_le_dec (point first_coordinate) 0) as [Hnegative|Hnonnegative].
  - exfalso. destruct (Hclosure (- point first_coordinate)) as
      [approximant [Hzero Hnear]].
    + pose proof (Qopp_lt_compat _ _ Hnegative) as Hpositive.
      setoid_replace (-0) with 0 in Hpositive by ring. exact Hpositive.
    + specialize (Hnear first_coordinate).
      unfold zero_cone in Hzero.
      apply (proj1 (Qabs_diff_Qlt_condition _ _ _)) in Hnear.
      destruct Hnear as [_ Hupper].
      setoid_replace (point first_coordinate + - point first_coordinate)
        with 0 in Hupper by ring.
      setoid_rewrite Hzero in Hupper. exact (Qlt_irrefl 0 Hupper).
  - destruct (Qlt_le_dec 0 (point first_coordinate)) as [Hpositive|Hnonpositive].
    + exfalso. destruct (Hclosure (point first_coordinate)) as
        [approximant [Hzero Hnear]]; [exact Hpositive|].
      specialize (Hnear first_coordinate).
      unfold zero_cone in Hzero.
      apply (proj1 (Qabs_diff_Qlt_condition _ _ _)) in Hnear.
      destruct Hnear as [Hlower _].
      setoid_replace (point first_coordinate - point first_coordinate)
        with 0 in Hlower by ring.
      setoid_rewrite Hzero in Hlower. exact (Qlt_irrefl 0 Hlower).
    + apply Qle_antisym; assumption.
Qed.

Example assembly_zero_cone :
  exists generators : list (QVec 1),
    SameSet zero_cone (qcone_generated generators).
Proof.
  apply rational_closed_cone_finitely_generated.
  - apply zero_cone_definable.
  - apply zero_cone_cone.
  - apply zero_cone_closed.
Qed.

Definition second_coordinate : Fin.t 2 := Fin.FS Fin.F1.

Definition upper_halfspace : QSet 2 :=
  fun value => 0 <= value second_coordinate.

Lemma upper_halfspace_definable : QDefinable upper_halfspace.
Proof.
  exists (QFLe (QTConst 0) (QTVar 1)). split; [reflexivity|].
  intro value. cbn.
  change (0 <= value second_coordinate <->
    0 <= qvec_environment value
      (proj1_sig (Fin.to_nat second_coordinate))).
  rewrite qvec_environment_inside. reflexivity.
Qed.

Lemma upper_halfspace_cone : IsCone upper_halfspace.
Proof.
  constructor.
  - unfold upper_halfspace, qvec_zero. apply Qle_refl.
  - intros left right Hleft Hright. unfold upper_halfspace, qvec_add in *.
    pose proof (Qplus_le_compat 0 (left second_coordinate) 0
      (right second_coordinate) Hleft Hright) as Hsum.
    setoid_replace (0 + 0) with 0 in Hsum by ring. exact Hsum.
  - intros coefficient value Hcoefficient Hvalue.
    unfold upper_halfspace, qvec_scale in *.
    apply Qmult_le_0_compat; assumption.
Qed.

Lemma upper_halfspace_closed : TopologicallyClosed upper_halfspace.
Proof.
  intros point Hclosure. unfold upper_halfspace.
  destruct (Qlt_le_dec (point second_coordinate) 0) as [Hnegative|Hnonnegative].
  - exfalso.
    destruct (Hclosure (- point second_coordinate)) as
      [approximant [Happroximant Hnear]].
    + pose proof (Qopp_lt_compat _ _ Hnegative) as Hpositive.
      setoid_replace (-0) with 0 in Hpositive by ring. exact Hpositive.
    + specialize (Hnear second_coordinate).
      apply (proj1 (Qabs_diff_Qlt_condition _ _ _)) in Hnear.
      destruct Hnear as [_ Hupper].
      setoid_replace
        (point second_coordinate + - point second_coordinate)
        with 0 in Hupper by ring.
      exact (Qlt_not_le _ _ Hupper Happroximant).
  - exact Hnonnegative.
Qed.

Example assembly_lineality_halfspace :
  exists generators : list (QVec 2),
    SameSet upper_halfspace (qcone_generated generators).
Proof.
  apply rational_closed_cone_finitely_generated.
  - apply upper_halfspace_definable.
  - apply upper_halfspace_cone.
  - apply upper_halfspace_closed.
Qed.

Definition qpair (left right : Q) : QVec 2 :=
  qvec_cons left (qvec_cons right (qvec_zero 0)).

Definition nonclosed_quadrant_cone : QSet 2 := fun value =>
  (value Fin.F1 == 0 /\ value second_coordinate == 0) \/
  (0 < value Fin.F1 /\ 0 < value second_coordinate).

Lemma nonclosed_quadrant_is_cone : IsCone nonclosed_quadrant_cone.
Proof.
  constructor.
  - left. split; reflexivity.
  - intros left right Hleft Hright. unfold nonclosed_quadrant_cone in *.
    unfold qvec_add. destruct Hleft as [[Hlx Hly]|[Hlx Hly]];
      destruct Hright as [[Hrx Hry]|[Hrx Hry]].
    + left. split.
      * setoid_rewrite Hlx. setoid_rewrite Hrx. ring.
      * setoid_rewrite Hly. setoid_rewrite Hry. ring.
    + right. split.
      * setoid_rewrite Hlx. setoid_replace (0 + right Fin.F1)
          with (right Fin.F1) by ring. exact Hrx.
      * setoid_rewrite Hly. setoid_replace (0 + right second_coordinate)
          with (right second_coordinate) by ring. exact Hry.
    + right. split.
      * setoid_rewrite Hrx. setoid_replace (left Fin.F1 + 0)
          with (left Fin.F1) by ring. exact Hlx.
      * setoid_rewrite Hry. setoid_replace (left second_coordinate + 0)
          with (left second_coordinate) by ring. exact Hly.
    + right. split.
      * pose proof (Qplus_lt_compat 0 (left Fin.F1) 0 (right Fin.F1)
          Hlx Hrx) as Hsum.
        setoid_replace (0 + 0) with 0 in Hsum by ring. exact Hsum.
      * pose proof (Qplus_lt_compat 0 (left second_coordinate) 0
          (right second_coordinate) Hly Hry) as Hsum.
        setoid_replace (0 + 0) with 0 in Hsum by ring. exact Hsum.
  - intros coefficient value Hcoefficient Hvalue.
    unfold nonclosed_quadrant_cone in *. unfold qvec_scale.
    destruct Hvalue as [[Hx Hy]|[Hx Hy]].
    + left. split.
      * setoid_rewrite Hx. ring.
      * setoid_rewrite Hy. ring.
    + destruct (Qeq_dec coefficient 0) as [Hzero|Hnonzero].
      * left. split; setoid_rewrite Hzero; ring.
      * right. assert (Hpositive : 0 < coefficient).
        { apply (proj2 (Qlt_leneq 0 coefficient)). split.
          - exact Hcoefficient.
          - intro Hreverse. apply Hnonzero. now symmetry. }
        split; apply Qmult_lt_0_compat; assumption.
Qed.

Lemma nonclosed_quadrant_not_closed :
  ~ TopologicallyClosed nonclosed_quadrant_cone.
Proof.
  intro Hclosed.
  assert (Hclosure : QClosure nonclosed_quadrant_cone (qpair 1 0)).
  { intros delta Hdelta. exists (qpair 1 (delta / 2)). split.
    - right. split.
      + change (0 < 1). unfold Qlt; cbn; lia.
      + change (0 < delta / 2). apply Qmult_lt_0_compat; [exact Hdelta|].
        unfold Qlt; cbn; lia.
    - intro index. refine (Fin.caseS' index (fun index =>
        Qabs (qpair 1 0 index - qpair 1 (delta / 2) index) < delta) _ _).
      + cbn [qpair qvec_cons]. setoid_replace (1 - 1) with 0 by ring.
        exact Hdelta.
      + intro tail_index. refine (Fin.caseS' tail_index (fun tail_index =>
          Qabs (qpair 1 0 (Fin.FS tail_index) -
            qpair 1 (delta / 2) (Fin.FS tail_index)) < delta) _ _).
        * cbn [qpair qvec_cons].
          setoid_replace (0 - delta / 2) with (- (delta / 2)) by ring.
          setoid_rewrite Qabs_opp.
          setoid_rewrite (Qabs_pos (delta / 2)
            (Qlt_le_weak _ _ (Qmult_lt_0_compat delta (/2) Hdelta
              ltac:(unfold Qlt; cbn; lia)))).
          assert (Htwo : (0 : Q) < 2) by (unfold Qlt; cbn; lia).
          apply (proj1 (Qmult_lt_r (delta / 2) delta 2 Htwo)).
          setoid_replace ((delta / 2) * 2) with delta by
            (field; discriminate).
          setoid_replace (delta * 2) with (delta + delta) by ring.
          pose proof (proj2 (Qplus_lt_r 0 delta delta) Hdelta) as Hsum.
          setoid_replace (delta + 0) with delta in Hsum by ring. exact Hsum.
        * intro impossible. inversion impossible. }
  specialize (Hclosed (qpair 1 0) Hclosure).
  unfold nonclosed_quadrant_cone in Hclosed.
  destruct Hclosed as [[Hone _]|[_ Hzero]].
  - change (1 == 0) in Hone. discriminate.
  - change (0 < 0) in Hzero. exact (Qlt_irrefl 0 Hzero).
Qed.

Definition impossible_strict_cell : QAffineConjunction :=
  [QALt (QTConst 0) (QTConst 0)].

Example impossible_strict_cell_is_empty :
  ~ exists value : QVec 1,
      qconjunction_semantics (qvec_environment value) impossible_strict_cell.
Proof.
  intros [value Hvalue]. inversion Hvalue; subst. cbn in H1.
  exact (Qlt_irrefl 0 H1).
Qed.

Example empty_cell_homogenization_has_nonzero_projection :
  let value := qvec_cons 1 (qvec_zero 0) in
  HConicalConstraints (homogenized_cell_matrix 1 impossible_strict_cell)
    (qvec_cons 0 value) /\
  ~ zero_cone value.
Proof.
  cbn. split.
  - apply (proj2 (cell_homogenization_correct 1 impossible_strict_cell 0
      (qvec_cons 1 (qvec_zero 0)))). split.
    + apply Qle_refl.
    + constructor; [cbn; apply Qle_refl|constructor].
  - unfold zero_cone. cbn. discriminate.
Qed.

Definition redundant_cell : QAffineConjunction :=
  [QALe (QTConst 0) (QTVar 0);
   QALe (QTConst 0) (QTVar 0)].

Example redundant_cell_contains_zero_at_time_one :
  HConicalConstraints (homogenized_cell_matrix 1 redundant_cell)
    (qvec_cons 1 (qvec_zero 1)).
Proof.
  apply homogenized_cell_contains_one.
  constructor; [cbn; apply Qle_refl|].
  constructor; [cbn; apply Qle_refl|constructor].
Qed.

Definition duplicated_cells : list QAffineConjunction :=
  [redundant_cell; redundant_cell].

Example duplicated_cells_still_have_finite_generators :
  exists generators : list (QVec 1),
    (forall generator, List.In generator generators -> assembly_all generator) /\
    (forall cell, List.In cell duplicated_cells -> forall value,
      qconjunction_semantics (qvec_environment value) cell ->
      qcone_generated generators value).
Proof.
  apply finite_cells_generators.
  - apply assembly_all_cone.
  - apply assembly_all_closed.
  - intros cell [<-|[<-|[]]] value Hvalue; exact I.
Qed.

Set Printing Implicit.
Check @cell_homogenization_correct.
Check @normalized_cell_term_correct.
Check @weak_cell_with_witness_normalizes.
Check @homogenized_cell_contains_one.
Check @homogenized_cell_projection_closed.
Check @qcone_generated_tail.
Check @nonempty_cell_finitely_generated_in_cone.
Check @finite_cells_generators.
Check @rational_closed_cone_finitely_generated.
Print Assumptions cell_homogenization_correct.
Print Assumptions weak_cell_with_witness_normalizes.
Print Assumptions homogenized_cell_projection_closed.
Print Assumptions nonempty_cell_finitely_generated_in_cone.
Print Assumptions finite_cells_generators.
Print Assumptions rational_closed_cone_finitely_generated.
