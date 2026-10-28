From Coq Require Import Fin Lia List Lra QArith Qring Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore RationalHToV
  LatticeGordanH LatticeGordanV.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

(** The integer map determined by a finite list of group generators and its
    rational extension.  The names make the two coefficient domains explicit. *)
Definition F_Z {d} (generators : list (ZVec d))
    (coefficients : ZVec (length generators)) : ZVec d :=
  zgroup_combination generators coefficients.

Definition F_Q {d} (generators : list (ZVec d))
    (coefficients : QVec (length generators)) : QVec d :=
  qgroup_combination generators (qvec_to_vector _ coefficients).

Lemma zgroup_combination_zscale : forall d
    (generators : list (ZVec d)) coefficient
    (value : Vector.t Z (length generators)),
    zgroup_combination generators (Vector.map (Z.mul coefficient) value) =
      zvec_zsmul coefficient (zgroup_combination generators value).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficient value.
  - refine (Vector.case0 (fun value => _) _ value).
    apply Vector.eq_nth_iff. intros index other <-.
    unfold zvec_zsmul, zvec_zero.
    cbn [zgroup_combination].
    rewrite (nth_map _ _ index index eq_refl). unfold zvec_zero.
    rewrite !const_nth. ring.
  - refine (Vector.caseS' value (fun value => _) _).
    intros head tail. apply Vector.eq_nth_iff. intros index other <-.
    cbn [zgroup_combination Vector.map]. unfold zvec_add.
    cbn.
    rewrite !(nth_map2 _ _ _ index index index eq_refl eq_refl),
      !zvec_zsmul_nth.
    replace (Vector.nth
      (zgroup_combination generators (Vector.map (Z.mul coefficient) tail))
      index) with
      (Vector.nth
        (zvec_zsmul coefficient (zgroup_combination generators tail)) index).
    2: { symmetry. exact (f_equal (fun vector => Vector.nth vector index)
          (IH coefficient tail)). }
    rewrite zvec_zsmul_nth,
      (nth_map2 _ _ _ index index index eq_refl eq_refl),
      zvec_zsmul_nth. ring.
Qed.
Lemma qgroup_combination_add_q : forall d (generators : list (ZVec d))
    (left right : Vector.t Q (length generators)),
    QVecEq
      (qgroup_combination generators (Vector.map2 Qplus left right))
      (qvec_add (qgroup_combination generators left)
        (qgroup_combination generators right)).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros left right.
  - refine (Vector.case0 (fun left => _) _ left).
    refine (Vector.case0 (fun right => _) _ right).
    apply qvec_eq_refl.
  - refine (Vector.caseS' left (fun left => _) _).
    intros left_head left_tail.
    refine (Vector.caseS' right (fun right => _) _).
    intros right_head right_tail index. cbn.
    unfold qvec_add, qvec_scale. specialize (IH left_tail right_tail index).
    setoid_rewrite IH. unfold qvec_add. ring.
Qed.

Lemma qgroup_combination_scale_q : forall d (generators : list (ZVec d))
    coefficient (value : Vector.t Q (length generators)),
    QVecEq
      (qgroup_combination generators (Vector.map (Qmult coefficient) value))
      (qvec_scale coefficient (qgroup_combination generators value)).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficient value.
  - refine (Vector.case0 (fun value => _) _ value). intro index.
    cbn [qgroup_combination]. unfold qvec_scale, qvec_zero. ring.
  - refine (Vector.caseS' value (fun value => _) _).
    intros head tail index. cbn. unfold qvec_add, qvec_scale.
    specialize (IH coefficient tail index). setoid_rewrite IH.
    unfold qvec_scale. ring.
Qed.

Lemma F_Z_add : forall d (generators : list (ZVec d)) left right,
    F_Z generators (zvec_add left right) =
      zvec_add (F_Z generators left) (F_Z generators right).
Proof.
  intros d generators left right. unfold F_Z, zvec_add.
  apply zgroup_combination_add.
Qed.

Lemma F_Z_scale : forall d (generators : list (ZVec d)) coefficient value,
    F_Z generators (Vector.map (Z.mul coefficient) value) =
      zvec_zsmul coefficient (F_Z generators value).
Proof. intros. apply zgroup_combination_zscale. Qed.

Lemma F_Q_of_Z : forall d (generators : list (ZVec d)) coefficients,
    QVecEq (F_Q generators (zvec_to_qvec coefficients))
      (zvec_to_qvec (F_Z generators coefficients)).
Proof.
  intros d generators coefficients. unfold F_Q, F_Z.
  assert (Hcoefficients : qvec_to_vector (length generators)
      (zvec_to_qvec coefficients) = Vector.map inject_Z coefficients).
  { apply Vector.eq_nth_iff. intros index other <-.
    rewrite qvec_to_vector_nth. unfold zvec_to_qvec.
    symmetry. apply (nth_map _ _ index index eq_refl). }
  rewrite Hcoefficients. apply qgroup_combination_inject.
Qed.

Lemma F_Q_add : forall d (generators : list (ZVec d)) left right,
    QVecEq (F_Q generators (qvec_add left right))
      (qvec_add (F_Q generators left) (F_Q generators right)).
Proof.
  intros d generators left right. unfold F_Q.
  assert (Hcoefficients : qvec_to_vector (length generators)
      (qvec_add left right) = Vector.map2 Qplus
        (qvec_to_vector (length generators) left)
        (qvec_to_vector (length generators) right)).
  { apply Vector.eq_nth_iff. intros index other <-.
    rewrite qvec_to_vector_nth,
      (nth_map2 _ _ _ index index index eq_refl eq_refl),
      !qvec_to_vector_nth. reflexivity. }
  rewrite Hcoefficients. apply qgroup_combination_add_q.
Qed.

Lemma F_Q_scale : forall d (generators : list (ZVec d)) coefficient value,
    QVecEq (F_Q generators (qvec_scale coefficient value))
      (qvec_scale coefficient (F_Q generators value)).
Proof.
  intros d generators coefficient value. unfold F_Q.
  assert (Hcoefficients : qvec_to_vector (length generators)
      (qvec_scale coefficient value) = Vector.map (Qmult coefficient)
        (qvec_to_vector (length generators) value)).
  { apply Vector.eq_nth_iff. intros index other <-.
    rewrite qvec_to_vector_nth,
      (nth_map _ _ index index eq_refl), qvec_to_vector_nth.
    reflexivity. }
  rewrite Hcoefficients. apply qgroup_combination_scale_q.
Qed.

Lemma F_Q_zero : forall d (generators : list (ZVec d)),
    QVecEq (F_Q generators (qvec_zero (length generators))) (qvec_zero d).
Proof.
  intros d generators.
  pose proof (F_Q_scale d generators 0 (qvec_zero (length generators))) as H.
  intro index. specialize (H index). unfold qvec_scale, qvec_zero in H |- *.
  eapply Qeq_trans; [exact H|]. ring.
Qed.

Lemma F_Q_linear_combination : forall d (groups : list (ZVec d))
    (vectors : list (QVec (length groups))) coefficients,
    QVecEq (F_Q groups (qlinear_combination vectors coefficients))
      (qlinear_combination (List.map (F_Q groups) vectors) coefficients).
Proof.
  intros d groups vectors. induction vectors as [|vector vectors IH];
    intros coefficients; destruct coefficients as [|coefficient coefficients].
  - apply F_Q_zero.
  - apply F_Q_zero.
  - apply F_Q_zero.
  - cbn [qlinear_combination].
    eapply qvec_eq_trans; [apply F_Q_add|].
    apply qvec_eq_add; [apply F_Q_scale|apply IH].
Qed.

Fixpoint qv_combination {d} (generators : list (QVec d)) :
    Vector.t Q (length generators) -> QVec d :=
  match generators as generators0 return
      Vector.t Q (length generators0) -> QVec d with
  | [] => fun _ => qvec_zero d
  | generator :: generators' => fun coefficients =>
      qvec_add
        (qvec_scale (Vector.hd coefficients) generator)
        (qv_combination generators' (Vector.tl coefficients))
  end.

Lemma qv_combination_to_list : forall d (generators : list (QVec d))
    (coefficients : Vector.t Q (length generators)),
    QVecEq (qv_combination generators coefficients)
      (qlinear_combination generators (Vector.to_list coefficients)).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intro coefficients.
  - refine (Vector.case0 (fun coefficients => _) _ coefficients).
    apply qvec_eq_refl.
  - refine (Vector.caseS' coefficients (fun coefficients => _) _).
    intros head tail index. cbn. unfold qvec_add.
    specialize (IH tail index). setoid_rewrite IH. reflexivity.
Qed.

Lemma vector_nonnegative_to_list : forall n (values : Vector.t Q n),
    (forall index, 0 <= Vector.nth values index) ->
    List.Forall (fun q => 0 <= q) (Vector.to_list values).
Proof.
  intros n values. induction values as [|head n tail IH]; intro H.
  - constructor.
  - constructor.
    + exact (H Fin.F1).
    + apply IH. intro index. exact (H (Fin.FS index)).
Qed.

Fixpoint list_coefficients (n : nat) (values : list Q) : Vector.t Q n :=
  match n with
  | O => @Vector.nil Q
  | S n' => @Vector.cons Q (List.hd 0 values) n'
      (list_coefficients n' (List.tl values))
  end.

Lemma list_coefficients_nonnegative : forall values n,
    length values = n ->
    List.Forall (fun q => 0 <= q) values ->
    forall index, 0 <= Vector.nth (list_coefficients n values) index.
Proof.
  intros values. induction values as [|head tail IH]; intros n Hlength Hall.
  - destruct n; [intro index; inversion index|discriminate].
  - destruct n; [discriminate|]. injection Hlength as Hlength.
    inversion Hall as [|? ? Hhead Htail]; subst.
    intro index. refine (Fin.caseS' index (fun index => _) _ _).
    + exact Hhead.
    + intro tail_index. eapply IH; eauto.
Qed.

Lemma list_coefficients_combination : forall d
    (generators : list (QVec d)) coefficients,
    length coefficients = length generators ->
    QVecEq (qlinear_combination generators coefficients)
      (qv_combination generators
        (list_coefficients (length generators) coefficients)).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength.
  - destruct coefficients; [apply qvec_eq_refl|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength. intro index. cbn.
    unfold qvec_add. specialize (IH coefficients Hlength index).
    setoid_rewrite IH. reflexivity.
Qed.

Lemma qcone_generated_vector_coefficients : forall d
    (generators : list (QVec d)) point,
    qcone_generated generators point <->
    exists coefficients : Vector.t Q (length generators),
      (forall index, 0 <= Vector.nth coefficients index) /\
      QVecEq point (qv_combination generators coefficients).
Proof.
  intros d generators point. split.
  - intro Hcone.
    apply qcone_generated_aligned_coefficients in Hcone as
      [coefficients [Hlength [Hnonnegative Heq]]].
    exists (list_coefficients (length generators) coefficients). split.
    + now apply list_coefficients_nonnegative with (values := coefficients).
    + eapply qvec_eq_trans; [exact Heq|].
      apply list_coefficients_combination. exact Hlength.
  - intros [coefficients [Hnonnegative Heq]].
    apply qcone_generated_aligned_coefficients.
    exists (Vector.to_list coefficients). repeat split.
    + apply VectorSpec.length_to_list.
    + now apply vector_nonnegative_to_list.
    + eapply qvec_eq_trans; [exact Heq|].
      apply qv_combination_to_list.
Qed.

Definition qvec_of_vector {n} (value : Vector.t Q n) : QVec n :=
  fun index => Vector.nth value index.

Lemma qvec_to_vector_of_vector : forall n (value : Vector.t Q n),
    qvec_to_vector n (qvec_of_vector value) = value.
Proof.
  intros n value. apply Vector.eq_nth_iff. intros index other <-.
  rewrite qvec_to_vector_nth. reflexivity.
Qed.

Definition qvec_join {n m} (left : QVec n) (right : QVec m) : QVec (n + m) :=
  qvec_of_vector (Vector.append (qvec_to_vector n left)
    (qvec_to_vector m right)).

Definition qvec_left {n m} (value : QVec (n + m)) : QVec n :=
  qvec_of_vector (fst (Vector.splitat n (qvec_to_vector (n + m) value))).

Definition qvec_right {n m} (value : QVec (n + m)) : QVec m :=
  qvec_of_vector (snd (Vector.splitat n (qvec_to_vector (n + m) value))).

Lemma qvec_join_left : forall n m (left : QVec n) (right : QVec m),
    QVecEq (qvec_left (qvec_join left right)) left.
Proof.
  intros n m left right index. unfold qvec_left, qvec_join.
  assert (Hvec : qvec_to_vector (n + m)
      (qvec_of_vector (Vector.append (qvec_to_vector n left)
        (qvec_to_vector m right))) =
      Vector.append (qvec_to_vector n left) (qvec_to_vector m right)).
  { apply Vector.eq_nth_iff. intros i other <-.
    rewrite qvec_to_vector_nth. reflexivity. }
  rewrite Hvec, VectorSpec.splitat_append. cbn. unfold qvec_of_vector.
  rewrite qvec_to_vector_nth. reflexivity.
Qed.

Lemma qvec_join_right : forall n m (left : QVec n) (right : QVec m),
    QVecEq (qvec_right (qvec_join left right)) right.
Proof.
  intros n m left right index. unfold qvec_right, qvec_join.
  assert (Hvec : qvec_to_vector (n + m)
      (qvec_of_vector (Vector.append (qvec_to_vector n left)
        (qvec_to_vector m right))) =
      Vector.append (qvec_to_vector n left) (qvec_to_vector m right)).
  { apply Vector.eq_nth_iff. intros i other <-.
    rewrite qvec_to_vector_nth. reflexivity. }
  rewrite Hvec, VectorSpec.splitat_append. cbn. unfold qvec_of_vector.
  rewrite qvec_to_vector_nth. reflexivity.
Qed.

Lemma qvec_join_split : forall n m (value : QVec (n + m)),
    QVecEq value (qvec_join (qvec_left value) (qvec_right value)).
Proof.
  intros n m value index. unfold qvec_join, qvec_left, qvec_right.
  destruct (Vector.splitat n (qvec_to_vector (n + m) value)) as [left right]
    eqn:Hsplit.
  pose proof Hsplit as Hfull. apply VectorSpec.append_splitat in Hfull.
  rewrite !qvec_to_vector_of_vector. unfold qvec_of_vector. cbn.
  rewrite <- Hfull, qvec_to_vector_nth.
  reflexivity.
Qed.

Fixpoint zcoordinate_vector {d} (generators : list (ZVec d))
    (coordinate : Fin.t d) : Vector.t Q (length generators) :=
  match generators with
  | [] => @Vector.nil Q
  | generator :: generators' =>
      @Vector.cons Q (inject_Z (Vector.nth generator coordinate)) _
        (zcoordinate_vector generators' coordinate)
  end.

Fixpoint qcoordinate_vector {d} (generators : list (QVec d))
    (coordinate : Fin.t d) : Vector.t Q (length generators) :=
  match generators with
  | [] => @Vector.nil Q
  | generator :: generators' =>
      @Vector.cons Q (generator coordinate) _
        (qcoordinate_vector generators' coordinate)
  end.

Definition qopp_vector {n} (value : Vector.t Q n) : Vector.t Q n :=
  Vector.map Qopp value.

Fixpoint qunit_vector {n : nat} (selected : Fin.t n) : Vector.t Q n :=
  match selected in Fin.t n0 return Vector.t Q n0 with
  | @Fin.F1 n' => @Vector.cons Q 1 n' (Vector.const 0 n')
  | @Fin.FS n' selected' =>
      @Vector.cons Q 0 n' (qunit_vector selected')
  end.

Definition qzero_coefficients (n : nat) : Vector.t Q n := Vector.const 0 n.

Definition pullback_lambda_row {d} (groups : list (ZVec d))
    (cones : list (QVec d)) (index : Fin.t (length cones)) :
    Vector.t Q (length groups + length cones) :=
  Vector.append (qzero_coefficients (length groups))
    (qunit_vector index).

Definition pullback_equality_row {d} (groups : list (ZVec d))
    (cones : list (QVec d)) (coordinate : Fin.t d) :
    Vector.t Q (length groups + length cones) :=
  Vector.append (zcoordinate_vector groups coordinate)
    (qopp_vector (qcoordinate_vector cones coordinate)).

Definition pullback_matrix {d} (groups : list (ZVec d))
    (cones : list (QVec d)) :
    QMatrix (length cones + (d + d)) (length groups + length cones) :=
  Vector.append
    (vector_of_finfun _ _ (pullback_lambda_row groups cones))
    (Vector.append
      (vector_of_finfun _ _ (pullback_equality_row groups cones))
      (vector_of_finfun _ _ (fun coordinate =>
        qopp_vector (pullback_equality_row groups cones coordinate)))).

Lemma qvec_to_vector_join : forall n m (left : QVec n) (right : QVec m),
    qvec_to_vector (n + m) (qvec_join left right) =
      Vector.append (qvec_to_vector n left) (qvec_to_vector m right).
Proof. intros. apply qvec_to_vector_of_vector. Qed.

Lemma qdot_append : forall n m (left_row : Vector.t Q n)
    (right_row : Vector.t Q m) left_value right_value,
    qdot (Vector.append left_row right_row)
      (Vector.append left_value right_value) ==
    qdot left_row left_value + qdot right_row right_value.
Proof.
  intros n m left_row. induction left_row as [|head n tail IH];
    intros right_row left_value right_value.
  - refine (Vector.case0 (fun left_value => _) _ left_value). cbn. ring.
  - refine (Vector.caseS' left_value (fun left_value => _) _).
    intros value_head value_tail.
    change (head * value_head +
      qdot (Vector.append tail right_row)
        (Vector.append value_tail right_value) ==
      (head * value_head + qdot tail value_tail) +
        qdot right_row right_value).
    specialize (IH right_row value_tail right_value).
    transitivity (head * value_head +
      (qdot tail value_tail + qdot right_row right_value)).
    + apply Qplus_comp; [reflexivity|exact IH].
    + ring.
Qed.

Lemma qrow_apply_join : forall n m (left_row : Vector.t Q n)
    (right_row : Vector.t Q m) left_value right_value,
    qrow_apply (Vector.append left_row right_row)
      (qvec_join left_value right_value) ==
    qdot left_row (qvec_to_vector n left_value) +
      qdot right_row (qvec_to_vector m right_value).
Proof.
  intros. unfold qrow_apply. rewrite qvec_to_vector_join.
  apply qdot_append.
Qed.

Lemma qdot_zcoordinate : forall d (groups : list (ZVec d)) coordinate
    coefficients,
    qdot (zcoordinate_vector groups coordinate) coefficients ==
      qgroup_combination groups coefficients coordinate.
Proof.
  intros d groups. induction groups as [|generator groups IH];
    intros coordinate coefficients.
  - refine (Vector.case0 (fun coefficients => _) _ coefficients).
    reflexivity.
  - refine (Vector.caseS' coefficients (fun coefficients => _) _).
    intros head tail.
    change (inject_Z (Vector.nth generator coordinate) * head +
      qdot (zcoordinate_vector groups coordinate) tail ==
      head * inject_Z (Vector.nth generator coordinate) +
        qgroup_combination groups tail coordinate).
    transitivity (head * inject_Z (Vector.nth generator coordinate) +
      qdot (zcoordinate_vector groups coordinate) tail).
    + apply Qplus_comp; [ring|reflexivity].
    + apply Qplus_comp; [reflexivity|].
      apply IH.
Qed.

Lemma qdot_qcoordinate : forall d (cones : list (QVec d)) coordinate
    coefficients,
    qdot (qcoordinate_vector cones coordinate) coefficients ==
      qv_combination cones coefficients coordinate.
Proof.
  intros d cones. induction cones as [|generator cones IH];
    intros coordinate coefficients.
  - refine (Vector.case0 (fun coefficients => _) _ coefficients).
    reflexivity.
  - refine (Vector.caseS' coefficients (fun coefficients => _) _).
    intros head tail.
    change (generator coordinate * head +
      qdot (qcoordinate_vector cones coordinate) tail ==
      head * generator coordinate + qv_combination cones tail coordinate).
    transitivity (head * generator coordinate +
      qdot (qcoordinate_vector cones coordinate) tail).
    + apply Qplus_comp; [ring|reflexivity].
    + apply Qplus_comp; [reflexivity|apply IH].
Qed.

Lemma qdot_opp_left : forall n (row value : Vector.t Q n),
    qdot (qopp_vector row) value == - qdot row value.
Proof.
  intros n row. induction row as [|head n tail IH]; intro value.
  - refine (Vector.case0 (fun value => _) _ value). reflexivity.
  - refine (Vector.caseS' value (fun value => _) _).
    intros value_head value_tail.
    change ((- head) * value_head + qdot (qopp_vector tail) value_tail ==
      - (head * value_head + qdot tail value_tail)).
    specialize (IH value_tail).
    transitivity ((- head) * value_head + (- qdot tail value_tail)).
    + apply Qplus_comp; [reflexivity|exact IH].
    + ring.
Qed.

Lemma qdot_zero_left_local : forall n (value : Vector.t Q n),
    qdot (qzero_coefficients n) value == 0.
Proof.
  intros n value. induction value as [|head n tail IH].
  - reflexivity.
  - change (0 * head + qdot (qzero_coefficients n) tail == 0).
    transitivity (0 * head + 0).
    + apply Qplus_comp; [reflexivity|exact IH].
    + ring.
Qed.

Lemma qdot_unit : forall n (selected : Fin.t n) (value : Vector.t Q n),
    qdot (qunit_vector selected) value == Vector.nth value selected.
Proof.
  intros n selected. induction selected as [n|n selected IH]; intro value.
  - refine (Vector.caseS' value (fun value => _) _).
    intros head tail.
    change (1 * head + qdot (qzero_coefficients n) tail == head).
    transitivity (1 * head + 0).
    + apply Qplus_comp; [reflexivity|apply qdot_zero_left_local].
    + ring.
  - refine (Vector.caseS' value (fun value => _) _).
    intros head tail.
    change (0 * head + qdot (qunit_vector selected) tail ==
      Vector.nth tail selected).
    transitivity (0 * head + Vector.nth tail selected).
    + apply Qplus_comp; [reflexivity|apply IH].
    + ring.
Qed.

Lemma qrow_lambda_correct : forall d (groups : list (ZVec d))
    (cones : list (QVec d)) index z lambda,
    qrow_apply (pullback_lambda_row groups cones index)
      (qvec_join z lambda) == lambda index.
Proof.
  intros. unfold pullback_lambda_row. setoid_rewrite qrow_apply_join.
  setoid_rewrite qdot_zero_left_local. setoid_rewrite qdot_unit.
  rewrite qvec_to_vector_nth. ring.
Qed.

Lemma qrow_equality_correct : forall d (groups : list (ZVec d))
    (cones : list (QVec d)) coordinate z lambda,
    qrow_apply (pullback_equality_row groups cones coordinate)
      (qvec_join z lambda) ==
      F_Q groups z coordinate - qv_combination cones
        (qvec_to_vector (length cones) lambda) coordinate.
Proof.
  intros. unfold pullback_equality_row. setoid_rewrite qrow_apply_join.
  setoid_rewrite qdot_zcoordinate. setoid_rewrite qdot_opp_left.
  setoid_rewrite qdot_qcoordinate. unfold F_Q, Qminus. reflexivity.
Qed.

Lemma qrow_opp_apply : forall n (row : Vector.t Q n) value,
    qrow_apply (qopp_vector row) value == - qrow_apply row value.
Proof.
  intros. unfold qrow_apply. apply qdot_opp_left.
Qed.

Lemma pullback_matrix_constraints : forall d (groups : list (ZVec d))
    (cones : list (QVec d)) z lambda,
    HConicalConstraints (pullback_matrix groups cones) (qvec_join z lambda) <->
    (forall index, 0 <= lambda index) /\
    QVecEq (F_Q groups z)
      (qv_combination cones (qvec_to_vector (length cones) lambda)).
Proof.
  intros d groups cones z lambda. split.
  - intro H. split.
    + intro index. specialize (H (Fin.L (d + d) index)).
      unfold pullback_matrix in H.
      rewrite VectorSpec.nth_append_L, vector_of_finfun_nth in H.
      setoid_rewrite qrow_lambda_correct in H. exact H.
    + intro coordinate.
      pose proof (H (Fin.R (length cones) (Fin.L d coordinate))) as Hpos.
      pose proof (H (Fin.R (length cones) (Fin.R d coordinate))) as Hneg.
      unfold pullback_matrix in Hpos, Hneg.
      rewrite VectorSpec.nth_append_R, VectorSpec.nth_append_L,
        vector_of_finfun_nth in Hpos.
      rewrite VectorSpec.nth_append_R, VectorSpec.nth_append_R,
        vector_of_finfun_nth in Hneg.
      setoid_rewrite qrow_equality_correct in Hpos.
      setoid_rewrite qrow_opp_apply in Hneg.
      setoid_rewrite qrow_equality_correct in Hneg.
      apply Qle_antisym.
      * apply (proj2 (Qle_minus_iff _ _)).
        setoid_replace
          (qv_combination cones (qvec_to_vector (length cones) lambda)
             coordinate + - F_Q groups z coordinate)
          with (- (F_Q groups z coordinate -
            qv_combination cones (qvec_to_vector (length cones) lambda)
              coordinate)) by (unfold Qminus; ring).
        exact Hneg.
      * apply (proj2 (Qle_minus_iff _ _)). exact Hpos.
  - intros [Hlambda Hequality] row.
    refine (Fin.case_L_R' (fun current => 0 <= qrow_apply
      (Vector.nth (pullback_matrix groups cones) current)
      (qvec_join z lambda)) row _ _).
    + intro index. unfold pullback_matrix.
      rewrite VectorSpec.nth_append_L, vector_of_finfun_nth.
      setoid_rewrite qrow_lambda_correct. apply Hlambda.
    + intro equality_index.
      refine (Fin.case_L_R' (fun current => 0 <= qrow_apply
        (Vector.nth (pullback_matrix groups cones)
          (Fin.R (length cones) current))
        (qvec_join z lambda)) equality_index _ _).
      * intro coordinate. unfold pullback_matrix.
        rewrite VectorSpec.nth_append_R, VectorSpec.nth_append_L,
          vector_of_finfun_nth.
        setoid_rewrite qrow_equality_correct.
        specialize (Hequality coordinate). unfold Qminus.
        setoid_rewrite Hequality.
        setoid_replace
          (qv_combination cones (qvec_to_vector (length cones) lambda)
             coordinate +
           - qv_combination cones (qvec_to_vector (length cones) lambda)
             coordinate) with 0 by ring.
        apply Qle_refl.
      * intro coordinate. unfold pullback_matrix.
        rewrite VectorSpec.nth_append_R, VectorSpec.nth_append_R,
          vector_of_finfun_nth.
        setoid_rewrite qrow_opp_apply.
        setoid_rewrite qrow_equality_correct.
        specialize (Hequality coordinate). unfold Qminus.
        setoid_rewrite Hequality.
        setoid_replace
          (- (qv_combination cones (qvec_to_vector (length cones) lambda)
               coordinate +
             - qv_combination cones (qvec_to_vector (length cones) lambda)
               coordinate)) with 0 by ring.
        apply Qle_refl.
Qed.

(* Projection is linear, so projected H-generators generate exactly the
   projection of the H-cone. *)
Lemma qvec_left_nth : forall n m (value : QVec (n + m)) (index : Fin.t n),
    qvec_left value index == value (Fin.L m index).
Proof.
  intros n m value index. unfold qvec_left, qvec_of_vector.
  destruct (Vector.splitat n (qvec_to_vector (n + m) value)) as [left right]
    eqn:Hsplit.
  pose proof Hsplit as Hfull. apply VectorSpec.append_splitat in Hfull.
  pose proof (qvec_to_vector_nth (n + m) value (Fin.L m index)) as Hnth.
  rewrite Hfull, VectorSpec.nth_append_L in Hnth. cbn.
  rewrite Hnth. reflexivity.
Qed.

Lemma qvec_right_nth : forall n m (value : QVec (n + m)) (index : Fin.t m),
    qvec_right value index == value (Fin.R n index).
Proof.
  intros n m value index. unfold qvec_right, qvec_of_vector.
  destruct (Vector.splitat n (qvec_to_vector (n + m) value)) as [left right]
    eqn:Hsplit.
  pose proof Hsplit as Hfull. apply VectorSpec.append_splitat in Hfull.
  pose proof (qvec_to_vector_nth (n + m) value (Fin.R n index)) as Hnth.
  rewrite Hfull, VectorSpec.nth_append_R in Hnth. cbn.
  rewrite Hnth. reflexivity.
Qed.

Lemma qvec_left_add : forall n m (left right : QVec (n + m)),
    QVecEq (qvec_left (qvec_add left right))
      (qvec_add (qvec_left left) (qvec_left right)).
Proof.
  intros n m left right index.
  eapply Qeq_trans; [apply qvec_left_nth|]. unfold qvec_add.
  apply Qplus_comp; symmetry; apply qvec_left_nth.
Qed.

Lemma qvec_left_scale : forall n m coefficient (value : QVec (n + m)),
    QVecEq (qvec_left (qvec_scale coefficient value))
      (qvec_scale coefficient (qvec_left value)).
Proof.
  intros n m coefficient value index.
  eapply Qeq_trans; [apply qvec_left_nth|]. unfold qvec_scale.
  apply Qmult_comp; [reflexivity|symmetry; apply qvec_left_nth].
Qed.

Lemma F_Q_qvec_ext : forall d (groups : list (ZVec d)) left right,
    QVecEq left right -> QVecEq (F_Q groups left) (F_Q groups right).
Proof.
  intros d groups. induction groups as [|generator groups IH];
    intros left right Heq.
  - intro index. unfold F_Q, qgroup_combination, qvec_zero. reflexivity.
  - change (QVec (S (length groups))) in left.
    change (QVec (S (length groups))) in right.
    intro index. cbn [F_Q qgroup_combination qvec_to_vector].
    unfold qvec_add, qvec_scale. apply Qplus_comp.
    + apply Qmult_comp; [apply Heq|reflexivity].
    + apply IH. intro coefficient. apply Heq.
Qed.

Lemma qlinear_combination_map_left : forall n m
    (generators : list (QVec (n + m))) (coefficients : list Q),
    QVecEq
      (qlinear_combination (List.map (@qvec_left n m) generators) coefficients)
      (qvec_left (qlinear_combination generators coefficients)).
Proof.
  intros n m generators. induction generators as [|generator generators IH];
    intros coefficients; destruct coefficients as [|head tail].
  - intro index. cbn [qlinear_combination]. symmetry. apply qvec_left_nth.
  - intro index. cbn [qlinear_combination]. symmetry. apply qvec_left_nth.
  - intro index. cbn [qlinear_combination]. symmetry. apply qvec_left_nth.
  - cbn [qlinear_combination].
    eapply qvec_eq_trans.
    + apply qvec_eq_add.
      * apply qvec_eq_scale; [reflexivity|apply qvec_eq_refl].
      * apply IH.
    + apply qvec_eq_sym.
      eapply qvec_eq_trans; [apply qvec_left_add|].
      apply qvec_eq_add; [apply qvec_left_scale|apply qvec_eq_refl].
Qed.

Lemma qvec_left_ext : forall n m (left right : QVec (n + m)),
    QVecEq left right -> QVecEq (qvec_left left) (qvec_left right).
Proof.
  intros n m left right Heq index.
  eapply Qeq_trans; [apply qvec_left_nth|].
  eapply Qeq_trans; [apply Heq|]. symmetry. apply qvec_left_nth.
Qed.

Lemma qcone_project_left : forall n m
    (generators : list (QVec (n + m))) point,
    qcone_generated (List.map (@qvec_left n m) generators) point <->
    exists lifted,
      qcone_generated generators lifted /\
      QVecEq point (qvec_left lifted).
Proof.
  intros n m generators point. split.
  - intro Hprojected.
    apply qcone_generated_aligned_coefficients in Hprojected as
      [coefficients [Hlength [Hnonnegative Hpoint]]].
    rewrite length_map in Hlength.
    exists (qlinear_combination generators coefficients). split.
    + apply qcone_generated_aligned_coefficients.
      exists coefficients. split; [exact Hlength|]. split.
      * exact Hnonnegative.
      * apply qvec_eq_refl.
    + eapply qvec_eq_trans; [exact Hpoint|].
      apply qlinear_combination_map_left.
  - intros [lifted [Hlifted Hpoint]].
    apply qcone_generated_aligned_coefficients in Hlifted as
      [coefficients [Hlength [Hnonnegative Hlifted]]].
    apply qcone_generated_aligned_coefficients.
    exists coefficients. split.
    + rewrite length_map. exact Hlength.
    + split; [exact Hnonnegative|].
      eapply qvec_eq_trans; [exact Hpoint|].
      eapply qvec_eq_trans.
      * apply qvec_left_ext. exact Hlifted.
      * apply qvec_eq_sym, qlinear_combination_map_left.
Qed.

Theorem vcone_pullback_finitely_generated : forall d
    (groups : list (ZVec d)) (cones : list (QVec d)),
    exists generators : list (QVec (length groups)),
      forall z : QVec (length groups),
        qcone_generated generators z <->
        qcone_generated cones (F_Q groups z).
Proof.
  intros d groups cones.
  destruct (rational_hcone_finitely_generated
    (length cones + (d + d)) (length groups + length cones)
    (pullback_matrix groups cones)) as [lifted_generators Hlifted].
  exists (List.map (@qvec_left (length groups) (length cones))
    lifted_generators). intro z. split.
  - intro Hprojected.
    apply qcone_project_left in Hprojected as
      [lifted [Hlifted_cone Hz]].
    assert (Hconstraints : HConicalConstraints (pullback_matrix groups cones)
        lifted).
    { apply (proj2 (Hlifted lifted)). exact Hlifted_cone. }
    assert (Hjoined : HConicalConstraints (pullback_matrix groups cones)
        (qvec_join (qvec_left lifted) (qvec_right lifted))).
    { apply (proj1 (hconstraints_qvec_ext _ _ _ lifted
        (qvec_join (qvec_left lifted) (qvec_right lifted))
        (qvec_join_split _ _ lifted))). exact Hconstraints. }
    pose proof (proj1 (pullback_matrix_constraints d groups cones
      (qvec_left lifted) (qvec_right lifted)) Hjoined) as
      [Hnonnegative Hequality].
    assert (Hcone_left : qcone_generated cones (F_Q groups (qvec_left lifted))).
    { apply qcone_generated_vector_coefficients.
      exists (qvec_to_vector (length cones) (qvec_right lifted)).
      split.
      - intro index. rewrite qvec_to_vector_nth. apply Hnonnegative.
      - exact Hequality. }
    apply (proj1 (qcone_generated_qvec_ext d cones
      (F_Q groups (qvec_left lifted)) (F_Q groups z)
      (F_Q_qvec_ext d groups _ _ (qvec_eq_sym _ _ _ Hz)))).
    exact Hcone_left.
  - intro Hcone.
    apply qcone_generated_vector_coefficients in Hcone as
      [coefficients [Hnonnegative Hequality]].
    set (lambda := qvec_of_vector coefficients).
    assert (Hconstraints : HConicalConstraints (pullback_matrix groups cones)
        (qvec_join z lambda)).
    { apply (proj2 (pullback_matrix_constraints d groups cones z lambda)).
      split.
      - intro index. unfold lambda, qvec_of_vector. apply Hnonnegative.
      - eapply qvec_eq_trans; [exact Hequality|].
        apply qvec_eq_sym. intro index.
        unfold lambda. rewrite qvec_to_vector_of_vector. reflexivity. }
    assert (Hcone_lifted : qcone_generated lifted_generators
        (qvec_join z lambda)).
    { apply (proj1 (Hlifted (qvec_join z lambda))). exact Hconstraints. }
    apply qcone_project_left.
    exists (qvec_join z lambda). split; [exact Hcone_lifted|].
    apply qvec_eq_sym, qvec_join_left.
Qed.
