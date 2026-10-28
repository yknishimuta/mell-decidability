From Coq Require Import Classical_Prop Fin Lia List QArith QArith.Qabs
  Qfield Qring Vector VectorSpec.
From Mell.Geometry Require Import MathCompBridge RationalDefinability
  QConeCore RationalHToV RationalQEOne RationalQENormalForm.

Import ListNotations.
Open Scope Q_scope.

Definition qvec_cons {d} (head : Q) (tail : QVec d) : QVec (S d) :=
  fun index => Fin.caseS' index (fun _ => Q) head tail.

Definition qvec_head {d} (value : QVec (S d)) : Q := value Fin.F1.
Definition qvec_tail {d} (value : QVec (S d)) : QVec d :=
  fun index => value (Fin.FS index).

Lemma qvec_cons_head_tail : forall d (value : QVec (S d)),
    QVecEq value (qvec_cons (qvec_head value) (qvec_tail value)).
Proof.
  intros d value index. refine (Fin.caseS' index (fun index =>
    value index == qvec_cons (qvec_head value) (qvec_tail value) index) _ _).
  - reflexivity.
  - intro tail_index. reflexivity.
Qed.

Lemma qvec_cons_add : forall d t u (x y : QVec d),
    QVecEq (qvec_cons (t + u) (qvec_add x y))
      (qvec_add (qvec_cons t x) (qvec_cons u y)).
Proof.
  intros d t u x y index. refine (Fin.caseS' index (fun index =>
    qvec_cons (t + u) (qvec_add x y) index ==
      qvec_add (qvec_cons t x) (qvec_cons u y) index) _ _);
    [reflexivity|intro tail_index; reflexivity].
Qed.

Lemma qvec_cons_scale : forall d coefficient t (x : QVec d),
    QVecEq (qvec_cons (coefficient * t) (qvec_scale coefficient x))
      (qvec_scale coefficient (qvec_cons t x)).
Proof.
  intros d coefficient t x index. refine (Fin.caseS' index (fun index =>
    qvec_cons (coefficient * t) (qvec_scale coefficient x) index ==
      qvec_scale coefficient (qvec_cons t x) index) _ _);
    [reflexivity|intro tail_index; reflexivity].
Qed.

Fixpoint qzero_vector (d : nat) : Vector.t Q d :=
  match d with
  | O => @Vector.nil Q
  | S d' => @Vector.cons Q 0 d' (qzero_vector d')
  end.

Fixpoint qvariable_row (d variable : nat) : Vector.t Q (S d) :=
  match d with
  | O => @Vector.cons Q 0 0 (@Vector.nil Q)
  | S d' =>
      match variable with
      | O => @Vector.cons Q 0 (S d')
          (@Vector.cons Q 1 d' (qzero_vector d'))
      | S variable' => @Vector.cons Q 0 (S d')
          (qvariable_row d' variable')
      end
  end.

Definition qconstant_row (d : nat) (constant : Q) : Vector.t Q (S d) :=
  @Vector.cons Q constant d (qzero_vector d).

Definition qrow_plus {d} (left right : Vector.t Q d) : Vector.t Q d :=
  Vector.map2 Qplus left right.

Definition qrow_opp {d} (value : Vector.t Q d) : Vector.t Q d :=
  Vector.map Qopp value.

Definition qrow_scale {d} (coefficient : Q)
    (value : Vector.t Q d) : Vector.t Q d :=
  Vector.map (Qmult coefficient) value.

Fixpoint qterm_homogeneous_row (d : nat) (term : QTerm) : Vector.t Q (S d) :=
  match term with
  | QTVar variable => qvariable_row d variable
  | QTConst constant => qconstant_row d constant
  | QTAdd lhs rhs => qrow_plus (qterm_homogeneous_row d lhs)
      (qterm_homogeneous_row d rhs)
  | QTOpp value => qrow_opp (qterm_homogeneous_row d value)
  | QTScale coefficient value =>
      qrow_scale coefficient (qterm_homogeneous_row d value)
  end.

Fixpoint qterm_homogeneous_semantics (d : nat) (t : Q)
    (x : QVec d) (term : QTerm) : Q :=
  match term with
  | QTVar variable => qvec_environment x variable
  | QTConst constant => t * constant
  | QTAdd lhs rhs => qterm_homogeneous_semantics d t x lhs +
      qterm_homogeneous_semantics d t x rhs
  | QTOpp value => - qterm_homogeneous_semantics d t x value
  | QTScale coefficient value =>
      coefficient * qterm_homogeneous_semantics d t x value
  end.

Lemma qvec_to_vector_cons : forall d t (x : QVec d),
    qvec_to_vector (S d) (qvec_cons t x) =
      @Vector.cons Q t d (qvec_to_vector d x).
Proof. reflexivity. Qed.

Lemma qdot_zero_left : forall d (right : Vector.t Q d),
    qdot (qzero_vector d) right == 0.
Proof.
  intros d. induction d as [|d IH]; intro right.
  - refine (Vector.case0 (fun right => qdot (qzero_vector 0) right == 0)
      _ right). reflexivity.
  - refine (Vector.caseS' right (fun right =>
      qdot (qzero_vector (S d)) right == 0) _).
    intros head tail. cbn. setoid_rewrite IH. ring.
Qed.

Lemma qvariable_row_correct : forall d variable t (x : QVec d),
    qrow_apply (qvariable_row d variable) (qvec_cons t x) ==
      qvec_environment x variable.
Proof.
  intros d. induction d as [|d IH]; intros variable t x.
  - destruct variable; unfold qrow_apply; rewrite qvec_to_vector_cons;
    cbn [qvariable_row qdot qvec_environment qvec_bind_environment
      qzero_environment]; reflexivity.
  - destruct variable as [|variable].
    + change (qrow_apply (qvariable_row (S d) 0) (qvec_cons t x) ==
        qvec_environment x (proj1_sig (Fin.to_nat (@Fin.F1 d)))).
      rewrite qvec_environment_inside.
      unfold qrow_apply. rewrite qvec_to_vector_cons.
      cbn [qvariable_row qdot qvec_environment qvec_bind_environment
        qzero_environment qvec_to_vector].
      setoid_rewrite qdot_zero_left.
      change (0 * t + (1 * x Fin.F1 + 0) == x Fin.F1).
      ring.
    + unfold qrow_apply in *. rewrite qvec_to_vector_cons. cbn [qvariable_row qdot].
      change (0 * t +
        qrow_apply (qvariable_row d variable)
          (qvec_cons (x Fin.F1) (fun index => x (Fin.FS index))) ==
        qvec_environment (fun index => x (Fin.FS index)) variable).
      setoid_replace (0 * t +
        qrow_apply (qvariable_row d variable)
          (qvec_cons (x Fin.F1) (fun index => x (Fin.FS index))))
        with (qrow_apply (qvariable_row d variable)
          (qvec_cons (x Fin.F1) (fun index => x (Fin.FS index)))) by ring.
      apply IH.
Qed.

Lemma qconstant_row_correct : forall d constant t (x : QVec d),
    qrow_apply (qconstant_row d constant) (qvec_cons t x) == t * constant.
Proof.
  intros d constant t x. unfold qrow_apply, qconstant_row.
  rewrite qvec_to_vector_cons. cbn [qdot].
  change (constant * t + qdot (qzero_vector d) (qvec_to_vector d x) ==
    t * constant).
  setoid_rewrite qdot_zero_left. ring.
Qed.

Lemma qdot_add_left : forall d (left right value : Vector.t Q d),
    qdot (Vector.map2 Qplus left right) value ==
      qdot left value + qdot right value.
Proof.
  intros d left. induction left as [|head d tail IH]; intro right.
  - refine (Vector.case0 (fun right => forall value,
      qdot (Vector.map2 Qplus (@Vector.nil Q) right) value ==
        qdot (@Vector.nil Q) value + qdot right value) _ right).
    intro value.
    refine (Vector.case0 (fun value => _ ) _ value). reflexivity.
  - refine (Vector.caseS' right (fun right => forall value,
      qdot (Vector.map2 Qplus (@Vector.cons Q head d tail) right) value ==
        qdot (@Vector.cons Q head d tail) value + qdot right value) _).
    intros right_head right_tail value.
    refine (Vector.caseS' value (fun value => _ ) _).
    intros value_head value_tail. cbn [Vector.map2 qdot].
    apply (Qeq_trans _ ((head + right_head) * value_head +
      (qdot tail value_tail + qdot right_tail value_tail)) _).
    + apply Qplus_comp; [reflexivity|apply IH].
    + change ((head + right_head) * value_head +
        (qdot tail value_tail + qdot right_tail value_tail) ==
        (head * value_head + qdot tail value_tail) +
          (right_head * value_head + qdot right_tail value_tail)).
      ring.
Qed.

Lemma qdot_opp_left : forall d (left value : Vector.t Q d),
    qdot (Vector.map Qopp left) value == - qdot left value.
Proof.
  intros d left. induction left as [|head d tail IH]; intro value.
  - refine (Vector.case0 (fun value => _ ) _ value). reflexivity.
  - refine (Vector.caseS' value (fun value => _ ) _).
    intros value_head value_tail. cbn [Vector.map qdot].
    apply (Qeq_trans _ ((- head) * value_head + (- qdot tail value_tail)) _).
    + apply Qplus_comp; [reflexivity|apply IH].
    + change ((- head) * value_head + (- qdot tail value_tail) ==
        - (head * value_head + qdot tail value_tail)).
      ring.
Qed.

Theorem qterm_homogeneous_row_correct : forall d term t (x : QVec d),
    qrow_apply (qterm_homogeneous_row d term) (qvec_cons t x) ==
      qterm_homogeneous_semantics d t x term.
Proof.
  intros d term. induction term; intros t x; cbn.
  - apply qvariable_row_correct.
  - apply qconstant_row_correct.
  - unfold qrow_plus, qrow_apply. rewrite qdot_add_left.
    fold (qrow_apply (qterm_homogeneous_row d term1) (qvec_cons t x)).
    fold (qrow_apply (qterm_homogeneous_row d term2) (qvec_cons t x)).
    now setoid_rewrite IHterm1; setoid_rewrite IHterm2.
  - unfold qrow_opp, qrow_apply. rewrite qdot_opp_left.
    fold (qrow_apply (qterm_homogeneous_row d term) (qvec_cons t x)).
    now setoid_rewrite IHterm.
  - unfold qrow_scale, qrow_apply. rewrite qdot_scale_left.
    fold (qrow_apply (qterm_homogeneous_row d term) (qvec_cons t x)).
    now setoid_rewrite IHterm.
Qed.

Lemma qterm_homogeneous_at_one : forall d term (x : QVec d),
    qterm_homogeneous_semantics d 1 x term ==
      qterm_semantics (qvec_environment x) term.
Proof.
  intros d term. induction term; intro x; cbn; try reflexivity.
  - ring.
  - now setoid_rewrite IHterm1; setoid_rewrite IHterm2.
  - now setoid_rewrite IHterm.
  - now setoid_rewrite IHterm.
Qed.

Lemma qvec_environment_dim0 : forall (x : QVec 0) variable,
    qvec_environment x variable = 0.
Proof. reflexivity. Qed.

Lemma qvec_environment_add_scale : forall d (x witness : QVec d)
    epsilon variable,
    qvec_environment (qvec_add x (qvec_scale epsilon witness)) variable ==
      qvec_environment x variable + epsilon * qvec_environment witness variable.
Proof.
  intros d. induction d as [|d IH]; intros x witness epsilon variable.
  - rewrite !qvec_environment_dim0. ring.
  - destruct variable as [|variable].
    + change
        (qvec_environment (qvec_add x (qvec_scale epsilon witness))
          (proj1_sig (Fin.to_nat (@Fin.F1 d))) ==
         qvec_environment x (proj1_sig (Fin.to_nat (@Fin.F1 d))) +
           epsilon * qvec_environment witness
             (proj1_sig (Fin.to_nat (@Fin.F1 d)))).
      rewrite !qvec_environment_inside. reflexivity.
    + change
        (qvec_environment
          (qvec_add (fun index => x (Fin.FS index))
            (qvec_scale epsilon (fun index => witness (Fin.FS index)))) variable ==
         qvec_environment (fun index => x (Fin.FS index)) variable +
           epsilon * qvec_environment
             (fun index => witness (Fin.FS index)) variable).
      apply IH.
Qed.

Lemma qvec_environment_scale : forall d coefficient (x : QVec d) variable,
    qvec_environment (qvec_scale coefficient x) variable ==
      coefficient * qvec_environment x variable.
Proof.
  intros d. induction d as [|d IH]; intros coefficient x variable.
  - rewrite !qvec_environment_dim0. ring.
  - destruct variable as [|variable].
    + change
        (qvec_environment (qvec_scale coefficient x)
          (proj1_sig (Fin.to_nat (@Fin.F1 d))) ==
         coefficient * qvec_environment x
           (proj1_sig (Fin.to_nat (@Fin.F1 d)))).
      rewrite !qvec_environment_inside. reflexivity.
    + change
        (qvec_environment
          (qvec_scale coefficient (fun index => x (Fin.FS index))) variable ==
         coefficient * qvec_environment
           (fun index => x (Fin.FS index)) variable).
      apply IH.
Qed.

Lemma qterm_homogeneous_add_scaled : forall d term t epsilon
    (x witness : QVec d),
    qterm_homogeneous_semantics d (t + epsilon)
      (qvec_add x (qvec_scale epsilon witness)) term ==
    qterm_homogeneous_semantics d t x term +
      epsilon * qterm_semantics (qvec_environment witness) term.
Proof.
  intros d term. induction term; intros t epsilon x witness; cbn.
  - apply qvec_environment_add_scale.
  - ring.
  - setoid_rewrite IHterm1. setoid_rewrite IHterm2. ring.
  - setoid_rewrite IHterm. ring.
  - setoid_rewrite IHterm. ring.
Qed.

Lemma qterm_homogeneous_divide : forall d term denominator (x : QVec d),
    ~ denominator == 0 ->
    qterm_semantics
      (qvec_environment (qvec_scale (/ denominator) x)) term ==
      / denominator * qterm_homogeneous_semantics d denominator x term.
Proof.
  intros d term. induction term; intros denominator x Hnonzero; cbn.
  - apply qvec_environment_scale.
  - field. exact Hnonzero.
  - pose proof (IHterm1 denominator x Hnonzero) as Hleft.
    pose proof (IHterm2 denominator x Hnonzero) as Hright.
    setoid_rewrite Hleft. setoid_rewrite Hright. ring.
  - pose proof (IHterm denominator x Hnonzero) as Hvalue.
    setoid_rewrite Hvalue. ring.
  - pose proof (IHterm denominator x Hnonzero) as Hvalue.
    setoid_rewrite Hvalue. ring.
Qed.

Definition qinequality_row d (lhs rhs : QTerm) : Vector.t Q (S d) :=
  qrow_plus (qterm_homogeneous_row d rhs)
    (qrow_opp (qterm_homogeneous_row d lhs)).

Lemma qinequality_row_correct : forall d lhs rhs t (x : QVec d),
    qrow_apply (qinequality_row d lhs rhs) (qvec_cons t x) ==
      qterm_homogeneous_semantics d t x rhs -
      qterm_homogeneous_semantics d t x lhs.
Proof.
  intros. unfold qinequality_row, qrow_plus, qrow_opp, qrow_apply.
  rewrite qdot_add_left, qdot_opp_left.
  fold (qrow_apply (qterm_homogeneous_row d rhs) (qvec_cons t x)).
  fold (qrow_apply (qterm_homogeneous_row d lhs) (qvec_cons t x)).
  setoid_rewrite qterm_homogeneous_row_correct.
  ring.
Qed.

Fixpoint qcell_homogenized_rows (d : nat) (cell : QAffineConjunction) : nat :=
  match cell with
  | [] => 1%nat
  | QAEq _ _ :: tail => S (S (qcell_homogenized_rows d tail))
  | _ :: tail => S (qcell_homogenized_rows d tail)
  end.

Definition qtime_nonnegative_row d : Vector.t Q (S d) :=
  @Vector.cons Q 1 d (qzero_vector d).

Fixpoint homogenized_cell_matrix d (cell : QAffineConjunction) :
    QMatrix (qcell_homogenized_rows d cell) (S d) :=
  match cell with
  | [] => @Vector.cons (Vector.t Q (S d)) (qtime_nonnegative_row d) 0
      (@Vector.nil (Vector.t Q (S d)))
  | QAEq lhs rhs :: tail =>
      @Vector.cons (Vector.t Q (S d)) (qinequality_row d lhs rhs)
        (S (qcell_homogenized_rows d tail))
        (@Vector.cons (Vector.t Q (S d)) (qinequality_row d rhs lhs)
          (qcell_homogenized_rows d tail)
          (homogenized_cell_matrix d tail))
  | QALe lhs rhs :: tail =>
      @Vector.cons (Vector.t Q (S d)) (qinequality_row d lhs rhs)
        (qcell_homogenized_rows d tail) (homogenized_cell_matrix d tail)
  | QALt lhs rhs :: tail =>
      @Vector.cons (Vector.t Q (S d)) (qinequality_row d lhs rhs)
        (qcell_homogenized_rows d tail) (homogenized_cell_matrix d tail)
  end.

Definition weak_homogenized_atom d t (x : QVec d) atom : Prop :=
  match atom with
  | QAEq lhs rhs =>
      qterm_homogeneous_semantics d t x lhs ==
        qterm_homogeneous_semantics d t x rhs
  | QALe lhs rhs | QALt lhs rhs =>
      qterm_homogeneous_semantics d t x lhs <=
        qterm_homogeneous_semantics d t x rhs
  end.

Definition weak_homogenized_cell d t (x : QVec d)
    (cell : QAffineConjunction) : Prop :=
  List.Forall (weak_homogenized_atom d t x) cell.

Lemma qtime_nonnegative_row_correct : forall d t (x : QVec d),
    qrow_apply (qtime_nonnegative_row d) (qvec_cons t x) == t.
Proof.
  intros. unfold qrow_apply, qtime_nonnegative_row.
  rewrite qvec_to_vector_cons. cbn [qdot].
  change (1 * t + qdot (qzero_vector d) (qvec_to_vector d x) == t).
  setoid_rewrite qdot_zero_left. ring.
Qed.

Theorem cell_homogenization_correct : forall d cell t (x : QVec d),
    HConicalConstraints (homogenized_cell_matrix d cell) (qvec_cons t x) <->
      0 <= t /\ weak_homogenized_cell d t x cell.
Proof.
  intros d cell. induction cell as [|atom tail IH]; intros t x.
  - split.
    + intro H. split.
      * specialize (H Fin.F1). cbn in H.
        setoid_rewrite qtime_nonnegative_row_correct in H. exact H.
      * constructor.
    + intros [Ht _] row. refine (Fin.caseS' row (fun row =>
        0 <= qrow_apply
          (Vector.nth (homogenized_cell_matrix d []) row)
          (qvec_cons t x)) _ _).
      * cbn. setoid_rewrite qtime_nonnegative_row_correct. exact Ht.
      * intro impossible. inversion impossible.
  - destruct atom as [lhs rhs|lhs rhs|lhs rhs]; cbn [weak_homogenized_cell].
    + split.
      * intro H. assert (Hlr := H Fin.F1).
        assert (Hrl := H (Fin.FS Fin.F1)). cbn in Hlr, Hrl.
        setoid_rewrite qinequality_row_correct in Hlr.
        setoid_rewrite qinequality_row_correct in Hrl.
        unfold Qminus in Hlr, Hrl.
        assert (Heq : qterm_homogeneous_semantics d t x lhs ==
            qterm_homogeneous_semantics d t x rhs).
        { apply Qle_antisym.
          - apply (proj2 (Qle_minus_iff
              (qterm_homogeneous_semantics d t x lhs)
              (qterm_homogeneous_semantics d t x rhs))). exact Hlr.
          - apply (proj2 (Qle_minus_iff
              (qterm_homogeneous_semantics d t x rhs)
              (qterm_homogeneous_semantics d t x lhs))). exact Hrl. }
        assert (Htail_matrix : HConicalConstraints
            (homogenized_cell_matrix d tail) (qvec_cons t x)).
        { intro row. exact (H (Fin.FS (Fin.FS row))). }
        destruct (proj1 (IH t x) Htail_matrix) as [Ht Htail].
        split; [exact Ht|]. constructor; assumption.
      * intros [Ht Hbody] row. inversion Hbody as [|? ? Heq Htail]; subst.
        refine (Fin.caseS' row (fun row => _) _ _).
        -- change (0 <= qrow_apply (qinequality_row d lhs rhs)
              (qvec_cons t x)).
           setoid_rewrite qinequality_row_correct.
           unfold Qminus. apply (proj1 (Qle_minus_iff _ _)).
           apply (proj2 (Qle_lteq _ _)). right. exact Heq.
        -- intro row'. refine (Fin.caseS' row' (fun row' => _) _ _).
           ++ change (0 <= qrow_apply (qinequality_row d rhs lhs)
                (qvec_cons t x)).
              setoid_rewrite qinequality_row_correct.
              unfold Qminus. apply (proj1 (Qle_minus_iff _ _)).
              apply (proj2 (Qle_lteq _ _)). right. now symmetry.
           ++ intro tail_row. apply (proj2 (IH t x) (conj Ht Htail) tail_row).
    + split.
      * intro H.
        assert (Hatom_raw := H Fin.F1). cbn in Hatom_raw.
        setoid_rewrite qinequality_row_correct in Hatom_raw.
        unfold Qminus in Hatom_raw.
        assert (Hatom : qterm_homogeneous_semantics d t x lhs <=
            qterm_homogeneous_semantics d t x rhs).
        { apply (proj2 (Qle_minus_iff _ _)). exact Hatom_raw. }
        assert (Htail_matrix : HConicalConstraints
            (homogenized_cell_matrix d tail) (qvec_cons t x)).
        { intro row. exact (H (Fin.FS row)). }
        destruct (proj1 (IH t x) Htail_matrix) as [Ht Htail].
        split; [exact Ht|]. constructor; assumption.
      * intros [Ht Hbody] row. inversion Hbody as [|? ? Hatom Htail]; subst.
        refine (Fin.caseS' row (fun row => _) _ _).
        -- change (0 <= qrow_apply (qinequality_row d lhs rhs)
              (qvec_cons t x)).
           setoid_rewrite qinequality_row_correct.
           unfold Qminus.
           apply (proj1 (Qle_minus_iff _ _)). exact Hatom.
        -- intro tail_row. apply (proj2 (IH t x) (conj Ht Htail) tail_row).
    + split.
      * intro H.
        assert (Hatom_raw := H Fin.F1). cbn in Hatom_raw.
        setoid_rewrite qinequality_row_correct in Hatom_raw.
        unfold Qminus in Hatom_raw.
        assert (Hatom : qterm_homogeneous_semantics d t x lhs <=
            qterm_homogeneous_semantics d t x rhs).
        { apply (proj2 (Qle_minus_iff _ _)). exact Hatom_raw. }
        assert (Htail_matrix : HConicalConstraints
            (homogenized_cell_matrix d tail) (qvec_cons t x)).
        { intro row. exact (H (Fin.FS row)). }
        destruct (proj1 (IH t x) Htail_matrix) as [Ht Htail].
        split; [exact Ht|]. constructor; assumption.
      * intros [Ht Hbody] row. inversion Hbody as [|? ? Hatom Htail]; subst.
        refine (Fin.caseS' row (fun row => _) _ _).
        -- change (0 <= qrow_apply (qinequality_row d lhs rhs)
              (qvec_cons t x)).
           setoid_rewrite qinequality_row_correct.
           unfold Qminus.
           apply (proj1 (Qle_minus_iff _ _)). exact Hatom.
        -- intro tail_row. apply (proj2 (IH t x) (conj Ht Htail) tail_row).
Qed.

Definition normalized_cell_point {d} (t epsilon : Q)
    (x witness : QVec d) : QVec d :=
  qvec_scale (/ (t + epsilon))
    (qvec_add x (qvec_scale epsilon witness)).

Lemma normalized_cell_term_correct : forall d term t epsilon
    (x witness : QVec d),
    0 < t + epsilon ->
    qterm_semantics
      (qvec_environment (normalized_cell_point t epsilon x witness)) term ==
    / (t + epsilon) *
      (qterm_homogeneous_semantics d t x term +
        epsilon * qterm_semantics (qvec_environment witness) term).
Proof.
  intros d term t epsilon x witness Hpositive.
  unfold normalized_cell_point.
  assert (Hnonzero : ~ t + epsilon == 0).
  { intro Heq. setoid_rewrite Heq in Hpositive. exact (Qlt_irrefl 0 Hpositive). }
  apply (Qeq_trans _
    (/ (t + epsilon) * qterm_homogeneous_semantics d (t + epsilon)
      (qvec_add x (qvec_scale epsilon witness)) term) _).
  - apply qterm_homogeneous_divide. exact Hnonzero.
  - apply Qmult_comp; [reflexivity|].
    apply qterm_homogeneous_add_scaled.
Qed.

Lemma weak_atom_with_witness_normalizes : forall d atom t epsilon
    (x witness : QVec d),
    0 <= t -> 0 < epsilon ->
    weak_homogenized_atom d t x atom ->
    qaffine_atom_semantics (qvec_environment witness) atom ->
    qaffine_atom_semantics
      (qvec_environment (normalized_cell_point t epsilon x witness)) atom.
Proof.
  intros d atom t epsilon x witness Ht Hepsilon Hweak Hwitness.
  assert (Hdenominator : 0 < t + epsilon).
  { apply Qlt_le_trans with epsilon; [exact Hepsilon|].
    pose proof (proj2 (Qplus_le_l 0 t epsilon) Ht) as Hsum.
    setoid_replace (0 + epsilon) with epsilon in Hsum by ring.
    exact Hsum. }
  assert (Hinverse : 0 < / (t + epsilon)).
  { apply Qinv_lt_0_compat. exact Hdenominator. }
  destruct atom as [lhs rhs|lhs rhs|lhs rhs]; cbn in *.
  - setoid_rewrite (normalized_cell_term_correct d lhs t epsilon x witness
      Hdenominator).
    setoid_rewrite (normalized_cell_term_correct d rhs t epsilon x witness
      Hdenominator).
    apply Qmult_comp; [reflexivity|].
    apply Qplus_comp; [exact Hweak|].
    apply Qmult_comp; [reflexivity|exact Hwitness].
  - setoid_rewrite (normalized_cell_term_correct d lhs t epsilon x witness
      Hdenominator).
    setoid_rewrite (normalized_cell_term_correct d rhs t epsilon x witness
      Hdenominator).
    apply (proj2 (Qmult_le_l _ _ _ Hinverse)).
    apply Qplus_le_compat; [exact Hweak|].
    pose proof (Qmult_le_compat_r _ _ epsilon Hwitness
      (Qlt_le_weak _ _ Hepsilon)) as Hscaled.
    setoid_replace
      (qterm_semantics (qvec_environment witness) lhs * epsilon)
      with (epsilon * qterm_semantics (qvec_environment witness) lhs)
      in Hscaled by ring.
    setoid_replace
      (qterm_semantics (qvec_environment witness) rhs * epsilon)
      with (epsilon * qterm_semantics (qvec_environment witness) rhs)
      in Hscaled by ring.
    exact Hscaled.
  - setoid_rewrite (normalized_cell_term_correct d lhs t epsilon x witness
      Hdenominator).
    setoid_rewrite (normalized_cell_term_correct d rhs t epsilon x witness
      Hdenominator).
    apply (proj2 (Qmult_lt_l _ _ _ Hinverse)).
    assert (Hscaled : epsilon *
        qterm_semantics (qvec_environment witness) lhs <
      epsilon * qterm_semantics (qvec_environment witness) rhs).
    { setoid_replace (epsilon *
          qterm_semantics (qvec_environment witness) lhs)
        with (qterm_semantics (qvec_environment witness) lhs * epsilon)
        by ring.
      setoid_replace (epsilon *
          qterm_semantics (qvec_environment witness) rhs)
        with (qterm_semantics (qvec_environment witness) rhs * epsilon)
        by ring.
      apply Qmult_lt_compat_r; assumption. }
    setoid_replace
      (qterm_homogeneous_semantics d t x lhs +
        epsilon * qterm_semantics (qvec_environment witness) lhs)
      with
      (epsilon * qterm_semantics (qvec_environment witness) lhs +
        qterm_homogeneous_semantics d t x lhs) by ring.
    setoid_replace
      (qterm_homogeneous_semantics d t x rhs +
        epsilon * qterm_semantics (qvec_environment witness) rhs)
      with
      (epsilon * qterm_semantics (qvec_environment witness) rhs +
        qterm_homogeneous_semantics d t x rhs) by ring.
    apply Qplus_lt_le_compat; assumption.
Qed.

Lemma weak_cell_with_witness_normalizes : forall d cell t epsilon
    (x witness : QVec d),
    0 <= t -> 0 < epsilon ->
    weak_homogenized_cell d t x cell ->
    qconjunction_semantics (qvec_environment witness) cell ->
    qconjunction_semantics
      (qvec_environment (normalized_cell_point t epsilon x witness)) cell.
Proof.
  intros d cell t epsilon x witness Ht Hepsilon Hweak Hwitness.
  induction cell as [|atom tail IH].
  - constructor.
  - inversion Hweak as [|? ? Hweak_atom Hweak_tail]; subst.
    inversion Hwitness as [|? ? Hwitness_atom Hwitness_tail]; subst.
    constructor.
    + eapply weak_atom_with_witness_normalizes; eauto.
    + eapply IH; eauto.
Qed.

Theorem homogenized_cell_contains_one : forall d cell (x : QVec d),
    qconjunction_semantics (qvec_environment x) cell ->
    HConicalConstraints (homogenized_cell_matrix d cell) (qvec_cons 1 x).
Proof.
  intros d cell x Hcell. apply (proj2 (cell_homogenization_correct d cell 1 x)).
  split.
  - unfold Qle; cbn. lia.
  - induction cell as [|atom tail IH].
    + constructor.
    + inversion Hcell as [|? ? Hatom Htail]; subst. constructor.
      * destruct atom as [lhs rhs|lhs rhs|lhs rhs]; cbn in *;
          setoid_rewrite qterm_homogeneous_at_one.
        -- exact Hatom.
        -- exact Hatom.
        -- apply Qlt_le_weak. exact Hatom.
      * apply IH. exact Htail.
Qed.

Fixpoint qvec_abs_sum (d : nat) : QVec d -> Q :=
  match d return QVec d -> Q with
  | O => fun _ => 0
  | S d' => fun value => Qabs (value Fin.F1) +
      qvec_abs_sum d' (fun index => value (Fin.FS index))
  end.

Lemma qvec_abs_sum_nonnegative : forall d (value : QVec d),
    0 <= qvec_abs_sum d value.
Proof.
  intros d. induction d as [|d IH]; intro value; cbn.
  - apply Qle_refl.
  - pose proof (Qplus_le_compat 0 (Qabs (value Fin.F1)) 0
      (qvec_abs_sum d (fun index => value (Fin.FS index)))
      (Qabs_nonneg _) (IH _)) as Hsum.
    setoid_replace (0 + 0) with 0 in Hsum by ring. exact Hsum.
Qed.

Lemma qvec_abs_component_le_sum : forall d (value : QVec d) index,
    Qabs (value index) <= qvec_abs_sum d value.
Proof.
  intros d. induction d as [|d IH]; intros value index.
  - inversion index.
  - refine (Fin.caseS' index (fun index =>
      Qabs (value index) <= qvec_abs_sum (S d) value) _ _).
    + cbn. pose proof (Qplus_le_compat
        (Qabs (value Fin.F1)) (Qabs (value Fin.F1)) 0
        (qvec_abs_sum d (fun index => value (Fin.FS index)))
        (Qle_refl _) (qvec_abs_sum_nonnegative d _)) as Hsum.
      setoid_replace (Qabs (value Fin.F1) + 0)
        with (Qabs (value Fin.F1)) in Hsum by ring. exact Hsum.
    + intro tail_index. cbn.
      eapply Qle_trans; [apply (IH (fun index => value (Fin.FS index))
        tail_index)|].
      pose proof (Qplus_le_compat 0 (Qabs (value Fin.F1))
        (qvec_abs_sum d (fun index => value (Fin.FS index)))
        (qvec_abs_sum d (fun index => value (Fin.FS index)))
        (Qabs_nonneg _) (Qle_refl _)) as Hsum.
      setoid_replace
        (0 + qvec_abs_sum d (fun index => value (Fin.FS index)))
        with (qvec_abs_sum d (fun index => value (Fin.FS index)))
        in Hsum by ring. exact Hsum.
Qed.

Lemma qabs_scale_nonnegative : forall coefficient value,
    0 <= coefficient ->
    Qabs (coefficient * value) == coefficient * Qabs value.
Proof.
  intros coefficient value Hcoefficient.
  destruct (Qlt_le_dec value 0) as [Hnegative|Hpositive].
  - assert (Hproduct : coefficient * value <= 0).
    { pose proof (Qmult_le_compat_r value 0 coefficient
        (Qlt_le_weak _ _ Hnegative) Hcoefficient) as Hproduct.
      setoid_replace (value * coefficient) with (coefficient * value)
        in Hproduct by ring.
      setoid_replace (0 * coefficient) with 0 in Hproduct by ring.
      exact Hproduct. }
    setoid_rewrite (Qabs_neg _ Hproduct).
    setoid_rewrite (Qabs_neg _ (Qlt_le_weak _ _ Hnegative)). ring.
  - assert (Hproduct : 0 <= coefficient * value).
    { apply Qmult_le_0_compat; assumption. }
    setoid_rewrite (Qabs_pos _ Hproduct).
    setoid_rewrite (Qabs_pos _ Hpositive). reflexivity.
Qed.

Lemma epsilon_component_bound : forall d (witness : QVec d) delta,
    0 < delta -> forall index,
    Qabs ((delta / (1 + qvec_abs_sum d witness)) * witness index) < delta.
Proof.
  intros d witness delta Hdelta index.
  pose proof (qvec_abs_sum_nonnegative d witness) as Hsum.
  assert (Hden : 0 < 1 + qvec_abs_sum d witness).
  { apply Qlt_le_trans with 1; [unfold Qlt; cbn; lia|].
    pose proof (Qplus_le_compat 1 1 0 (qvec_abs_sum d witness)
      (Qle_refl _) Hsum) as Hden.
    setoid_replace (1 + 0) with 1 in Hden by ring. exact Hden. }
  assert (Hepsilon : 0 <= delta / (1 + qvec_abs_sum d witness)).
  { apply Qlt_le_weak. apply Qmult_lt_0_compat; [exact Hdelta|].
    apply Qinv_lt_0_compat. exact Hden. }
  setoid_rewrite (qabs_scale_nonnegative _ _ Hepsilon).
  eapply Qle_lt_trans.
  - pose proof (Qmult_le_compat_r (Qabs (witness index))
      (qvec_abs_sum d witness)
      (delta / (1 + qvec_abs_sum d witness))
      (qvec_abs_component_le_sum d witness index) Hepsilon) as Hbound.
    setoid_replace
      (Qabs (witness index) * (delta / (1 + qvec_abs_sum d witness)))
      with ((delta / (1 + qvec_abs_sum d witness)) * Qabs (witness index))
      in Hbound by ring.
    setoid_replace
      (qvec_abs_sum d witness * (delta / (1 + qvec_abs_sum d witness)))
      with ((delta / (1 + qvec_abs_sum d witness)) *
        qvec_abs_sum d witness) in Hbound by ring. exact Hbound.
  - apply (proj1 (Qmult_lt_r
      ((delta / (1 + qvec_abs_sum d witness)) *
        qvec_abs_sum d witness) delta
      (1 + qvec_abs_sum d witness) Hden)).
    setoid_replace
      (((delta / (1 + qvec_abs_sum d witness)) *
        qvec_abs_sum d witness) * (1 + qvec_abs_sum d witness))
      with (delta * qvec_abs_sum d witness) by
        (field; intro Hzero; apply (Qlt_not_eq _ _ Hden); symmetry; exact Hzero).
    setoid_replace (delta * (1 + qvec_abs_sum d witness))
      with ((qvec_abs_sum d witness + 1) * delta) by ring.
    setoid_replace (delta * qvec_abs_sum d witness)
      with (qvec_abs_sum d witness * delta) by ring.
    apply Qmult_lt_compat_r; [exact Hdelta|].
    apply qle_lt_plus_one. apply Qle_refl.
Qed.

Theorem homogenized_cell_projection_closed : forall d (C : QSet d)
    (cell : QAffineConjunction) (witness : QVec d) (t : Q) (x : QVec d),
    IsCone C -> TopologicallyClosed C ->
    (forall y, qconjunction_semantics (qvec_environment y) cell -> C y) ->
    qconjunction_semantics (qvec_environment witness) cell ->
    HConicalConstraints (homogenized_cell_matrix d cell) (qvec_cons t x) ->
    C x.
Proof.
  intros d C cell witness t x HCone Hclosed Hcell_subset Hwitness Hhom.
  destruct (proj1 (cell_homogenization_correct d cell t x) Hhom)
    as [Ht Hweak].
  apply Hclosed. intros delta Hdelta.
  set (epsilon := delta / (1 + qvec_abs_sum d witness)).
  assert (Hepsilon : 0 < epsilon).
  { unfold epsilon. apply Qmult_lt_0_compat; [exact Hdelta|].
    apply Qinv_lt_0_compat.
    pose proof (qvec_abs_sum_nonnegative d witness) as Hsum.
    apply (Qlt_le_trans 0 1 (1 + qvec_abs_sum d witness));
      [unfold Qlt; cbn; lia|].
    pose proof (Qplus_le_compat 1 1 0 (qvec_abs_sum d witness)
      (Qle_refl _) Hsum) as Hden.
    setoid_replace (1 + 0) with 1 in Hden by ring. exact Hden. }
  assert (Hdenominator : 0 < t + epsilon).
  { eapply Qlt_le_trans; [exact Hepsilon|].
    pose proof (proj2 (Qplus_le_l 0 t epsilon) Ht) as Hsum.
    setoid_replace (0 + epsilon) with epsilon in Hsum by ring. exact Hsum. }
  set (normalized := normalized_cell_point t epsilon x witness).
  assert (Hnormalized_cell :
      qconjunction_semantics (qvec_environment normalized) cell).
  { unfold normalized. eapply weak_cell_with_witness_normalizes; eauto. }
  assert (Hnormalized_C : C normalized).
  { apply Hcell_subset. exact Hnormalized_cell. }
  exists (qvec_scale (t + epsilon) normalized). split.
  - apply (cone_closed_scale C HCone).
    + apply Qlt_le_weak. exact Hdenominator.
    + exact Hnormalized_C.
  - intro index. unfold normalized, normalized_cell_point, qvec_scale,
      qvec_add.
    assert (Hnonzero : ~ t + epsilon == 0).
    { intro Heq. setoid_rewrite Heq in Hdenominator.
      exact (Qlt_irrefl 0 Hdenominator). }
    setoid_replace
      (x index - (t + epsilon) *
        (/ (t + epsilon) * (x index + epsilon * witness index)))
      with (- (epsilon * witness index)) by (field; exact Hnonzero).
    setoid_rewrite Qabs_opp.
    unfold epsilon. apply epsilon_component_bound. exact Hdelta.
Qed.

Lemma qcone_combination_tail : forall d (generators : list (QVec (S d)))
    value,
    QConeCombination generators value ->
    QConeCombination (List.map (@qvec_tail d) generators) (qvec_tail value).
Proof.
  intros d generators value Hcombination. induction Hcombination.
  - change (QConeCombination (List.map (@qvec_tail d) generators)
      (qvec_zero d)). constructor.
  - change (QConeCombination (List.map (@qvec_tail d) generators)
      (qvec_add (qvec_scale coefficient (qvec_tail generator))
        (qvec_tail tail))).
    constructor; [exact H|apply in_map; exact H0|exact IHHcombination].
Qed.

Lemma qcone_generated_tail : forall d (generators : list (QVec (S d)))
    value,
    qcone_generated generators value ->
    qcone_generated (List.map (@qvec_tail d) generators) (qvec_tail value).
Proof.
  intros d generators value [generated [Hgenerated Heq]].
  exists (qvec_tail generated). split.
  - now apply qcone_combination_tail.
  - intro index. apply (Heq (Fin.FS index)).
Qed.

Lemma qcone_combination_mono : forall d (left right : list (QVec d)) value,
    (forall generator, List.In generator left -> List.In generator right) ->
    QConeCombination left value -> QConeCombination right value.
Proof.
  intros d left right value Hin Hcombination. induction Hcombination.
  - constructor.
  - constructor; [exact H|apply Hin; exact H0|exact IHHcombination].
Qed.

Lemma qcone_generated_mono : forall d (left right : list (QVec d)) value,
    (forall generator, List.In generator left -> List.In generator right) ->
    qcone_generated left value -> qcone_generated right value.
Proof.
  intros d left right value Hin [generated [Hgenerated Heq]].
  exists generated. split; [eapply qcone_combination_mono; eauto|exact Heq].
Qed.

Lemma qcone_generated_in_cone : forall d (C : QSet d) generators value,
    IsCone C ->
    (forall left right, QVecEq left right -> (C left <-> C right)) ->
    (forall generator, List.In generator generators -> C generator) ->
    qcone_generated generators value -> C value.
Proof.
  intros d C generators value HCone Hext Hgenerators
    [generated [Hgenerated Heq]].
  assert (Hcombination : forall generated,
      QConeCombination generators generated -> C generated).
  { intros generated' Hgenerated'. induction Hgenerated'.
    - apply (cone_contains_zero C HCone).
    - apply (cone_closed_add C HCone).
      + apply (cone_closed_scale C HCone); [exact H|].
        apply Hgenerators. exact H0.
      + exact IHHgenerated'. }
  assert (HCgenerated : C generated) by (apply Hcombination; exact Hgenerated).
  apply (proj2 (Hext value generated Heq)). exact HCgenerated.
Qed.

Lemma nonempty_cell_finitely_generated_in_cone : forall d (C : QSet d)
    (cell : QAffineConjunction) (witness : QVec d),
    IsCone C -> TopologicallyClosed C ->
    (forall y, qconjunction_semantics (qvec_environment y) cell -> C y) ->
    qconjunction_semantics (qvec_environment witness) cell ->
    exists generators : list (QVec d),
      (forall generator, List.In generator generators -> C generator) /\
      (forall y, qconjunction_semantics (qvec_environment y) cell ->
        qcone_generated generators y).
Proof.
  intros d C cell witness HCone Hclosed Hsubset Hwitness.
  destruct (rational_hcone_finitely_generated
    (qcell_homogenized_rows d cell) (S d)
    (homogenized_cell_matrix d cell)) as [hom_generators Hhom_generators].
  exists (List.map (@qvec_tail d) hom_generators). split.
  - intros generator Hin. apply in_map_iff in Hin.
    destruct Hin as [source [<- Hsource]].
    apply (homogenized_cell_projection_closed d C cell witness
      (qvec_head source) (qvec_tail source) HCone Hclosed Hsubset Hwitness).
    apply (proj2 (hconstraints_qvec_ext _ _
      (homogenized_cell_matrix d cell) source
      (qvec_cons (qvec_head source) (qvec_tail source))
      (qvec_cons_head_tail d source))).
    apply (proj2 (Hhom_generators source)).
    apply qcone_generated_generator. exact Hsource.
  - intros y Hy.
    pose proof (homogenized_cell_contains_one d cell y Hy) as Hone.
    pose proof (proj1 (Hhom_generators (qvec_cons 1 y)) Hone) as Hgenerated.
    pose proof (qcone_generated_tail d hom_generators
      (qvec_cons 1 y) Hgenerated) as Htail.
    exact Htail.
Qed.

Lemma finite_cells_generators : forall d (C : QSet d)
    (cells : list QAffineConjunction),
    IsCone C -> TopologicallyClosed C ->
    (forall cell, List.In cell cells -> forall y,
      qconjunction_semantics (qvec_environment y) cell -> C y) ->
    exists generators : list (QVec d),
      (forall generator, List.In generator generators -> C generator) /\
      (forall cell, List.In cell cells -> forall y,
        qconjunction_semantics (qvec_environment y) cell ->
        qcone_generated generators y).
Proof.
  intros d C cells. induction cells as [|cell tail IH];
    intros HCone Hclosed Hsubset.
  - exists []. split.
    + intros generator Hin. inversion Hin.
    + intros selected Hin. inversion Hin.
  - assert (Htail_subset : forall selected, List.In selected tail -> forall y,
        qconjunction_semantics (qvec_environment y) selected -> C y).
    { intros selected Hin. apply Hsubset. now right. }
    destruct (IH HCone Hclosed Htail_subset) as
      [tail_generators [Htail_sound Htail_complete]].
    destruct (classic (exists witness : QVec d,
      qconjunction_semantics (qvec_environment witness) cell))
      as [[witness Hwitness]|Hempty].
    + assert (Hcell_subset : forall y,
          qconjunction_semantics (qvec_environment y) cell -> C y).
      { intros y Hy. apply (Hsubset cell); [now left|exact Hy]. }
      destruct (nonempty_cell_finitely_generated_in_cone d C cell witness
        HCone Hclosed Hcell_subset Hwitness) as
        [cell_generators [Hcell_sound Hcell_complete]].
      exists (cell_generators ++ tail_generators). split.
      * intros generator Hin. apply in_app_or in Hin. destruct Hin.
        -- apply Hcell_sound. exact H.
        -- apply Htail_sound. exact H.
      * intros selected [<-|Hin] y Hy.
        -- eapply qcone_generated_mono; [|apply Hcell_complete; exact Hy].
           intros generator Hgenerator. apply in_or_app. now left.
        -- eapply qcone_generated_mono;
             [|apply (Htail_complete selected Hin y Hy)].
           intros generator Hgenerator. apply in_or_app. now right.
    + exists tail_generators. split; [exact Htail_sound|].
      intros selected [<-|Hin] y Hy.
      * exfalso. apply Hempty. exists y. exact Hy.
      * apply (Htail_complete selected Hin y Hy).
Qed.

Theorem rational_closed_cone_finitely_generated :
  forall d (C : QSet d),
    QDefinable C -> IsCone C -> TopologicallyClosed C ->
    exists generators : list (QVec d),
      SameSet C (qcone_generated generators).
Proof.
  intros d C Hdefinable HCone Hclosed.
  destruct (qdefinable_finite_cells d C Hdefinable) as [cells Hcells].
  assert (Hsubset : forall cell, List.In cell cells -> forall y,
      qconjunction_semantics (qvec_environment y) cell -> C y).
  { intros cell Hin y Hy. apply (proj2 (Hcells y)). exists cell. auto. }
  destruct (finite_cells_generators d C cells HCone Hclosed Hsubset) as
    [generators [Hgenerators Hcomplete]].
  exists generators. intro value. split.
  - intro HC. destruct (proj1 (Hcells value) HC) as [cell [Hin Hcell]].
    apply (Hcomplete cell Hin value Hcell).
  - intro Hgenerated.
    eapply qcone_generated_in_cone; [exact HCone| |exact Hgenerators|exact Hgenerated].
    intros left right Heq. eapply qdefinable_qvec_extensional; eauto.
Qed.
