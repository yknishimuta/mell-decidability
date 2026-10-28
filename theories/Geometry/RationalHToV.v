From Coq Require Import Fin Lia List QArith Qring Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge RationalDefinability QConeCore.
From Mell.Semilinear Require Import LinearEquations Presentation.

Import ListNotations.
Open Scope Q_scope.

Lemma q_of_nat_nonzero_hl : forall value,
    (0 < value)%nat -> ~ q_of_nat value == 0.
Proof.
  intros value Hpositive Heq. unfold q_of_nat in Heq.
  apply (proj1 (inject_Z_injective _ _)) in Heq. lia.
Qed.

Definition QMatrix (rows columns : nat) := Vector.t (Vector.t Q columns) rows.

Fixpoint vector_of_finfun (A : Type) (d : nat) :
    (Fin.t d -> A) -> Vector.t A d :=
  match d return (Fin.t d -> A) -> Vector.t A d with
  | O => fun _ => @Vector.nil A
  | S d' => fun value => @Vector.cons A (value Fin.F1) d'
      (vector_of_finfun A d' (fun index => value (Fin.FS index)))
  end.

Lemma vector_of_finfun_nth : forall A d (value : Fin.t d -> A) index,
    Vector.nth (vector_of_finfun A d value) index = value index.
Proof.
  intros A d. induction d as [|d IH]; intros value index.
  - inversion index.
  - refine (Fin.caseS' index (fun index =>
      Vector.nth (vector_of_finfun A (S d) value) index = value index) _ _).
    + reflexivity.
    + intro tail_index. cbn. apply IH.
Qed.

Fixpoint qvec_to_vector (d : nat) : QVec d -> Vector.t Q d :=
  match d return QVec d -> Vector.t Q d with
  | O => fun _ => @Vector.nil Q
  | S d' => fun value => @Vector.cons Q (value Fin.F1) d'
      (qvec_to_vector d' (fun index => value (Fin.FS index)))
  end.

Lemma qvec_to_vector_nth : forall d (value : QVec d) index,
    Vector.nth (qvec_to_vector d value) index = value index.
Proof.
  intros d. induction d as [|d IH]; intros value index.
  - inversion index.
  - refine (Fin.caseS' index (fun index =>
      Vector.nth (qvec_to_vector (S d) value) index = value index) _ _).
    + reflexivity.
    + intro tail_index. cbn. apply IH.
Qed.

Fixpoint qdot {d} (left : Vector.t Q d) : Vector.t Q d -> Q :=
  match left with
  | @Vector.nil _ => fun _ => 0
  | @Vector.cons _ head tail_d tail => fun right =>
      head * Vector.hd right + qdot tail (Vector.tl right)
  end.

Definition qrow_apply {d} (row : Vector.t Q d) (value : QVec d) : Q :=
  qdot row (qvec_to_vector d value).

Definition HConicalConstraints {rows d} (matrix : QMatrix rows d)
    (value : QVec d) : Prop :=
  forall row, 0 <= qrow_apply (Vector.nth matrix row) value.

Lemma qdot_ext : forall d (left left' right right' : Vector.t Q d),
    (forall index, Vector.nth left index == Vector.nth left' index) ->
    (forall index, Vector.nth right index == Vector.nth right' index) ->
    qdot left right == qdot left' right'.
Proof.
  intros d left. induction left as [|head d tail IH];
    intros left' right right' Hleft Hright.
  - refine (Vector.case0 (fun left' => qdot (@Vector.nil Q) right ==
      qdot left' right') _ left'). reflexivity.
  - refine (Vector.caseS' left' (fun left' =>
      (forall index, Vector.nth (@Vector.cons Q head d tail) index ==
        Vector.nth left' index) ->
      (forall index, Vector.nth right index == Vector.nth right' index) ->
      qdot (@Vector.cons Q head d tail) right == qdot left' right') _ Hleft Hright).
    intros other other_tail Hleft' Hright'.
    refine (Vector.caseS' right (fun right =>
      (forall index, Vector.nth right index == Vector.nth right' index) ->
      qdot (@Vector.cons Q head d tail) right ==
        qdot (@Vector.cons Q other d other_tail) right') _ Hright').
    intros right_head right_tail Hright_cons.
    refine (Vector.caseS' right' (fun right' =>
      (forall index,
        Vector.nth (@Vector.cons Q right_head d right_tail) index ==
        Vector.nth right' index) ->
      qdot (@Vector.cons Q head d tail)
        (@Vector.cons Q right_head d right_tail) ==
        qdot (@Vector.cons Q other d other_tail) right') _ Hright_cons).
    intros right'_head right'_tail Hright_both.
    pose proof (Hleft' Fin.F1) as Hleft_head.
    pose proof (Hright_both Fin.F1) as Hright_head.
    cbn in Hleft_head, Hright_head |- *. apply Qplus_comp.
    + apply Qmult_comp; [exact Hleft_head | exact Hright_head].
    + apply IH.
      * intro index. pose proof (Hleft' (Fin.FS index)) as Htail.
        cbn in Htail. exact Htail.
      * intro index. pose proof (Hright_both (Fin.FS index)) as Htail.
        cbn in Htail. exact Htail.
Qed.

Lemma qdot_scale_left : forall d coefficient
    (left right : Vector.t Q d),
    qdot (Vector.map (Qmult coefficient) left) right ==
      coefficient * qdot left right.
Proof.
  intros d coefficient left. induction left as [|head d tail IH]; intro right.
  - cbn. ring.
  - refine (Vector.caseS' right (fun right =>
      qdot (Vector.map (Qmult coefficient) (@Vector.cons Q head d tail)) right ==
        coefficient * qdot (@Vector.cons Q head d tail) right) _).
    intros right_head right_tail. cbn. setoid_rewrite IH. ring.
Qed.

Lemma qdot_add_right : forall d (row left right : Vector.t Q d),
    qdot row (Vector.map2 Qplus left right) ==
      qdot row left + qdot row right.
Proof.
  intros d row. induction row as [|coefficient d tail IH]; intros left right.
  - cbn. ring.
  - refine (Vector.caseS' left (fun left =>
      qdot (@Vector.cons Q coefficient d tail) (Vector.map2 Qplus left right) ==
        qdot (@Vector.cons Q coefficient d tail) left +
          qdot (@Vector.cons Q coefficient d tail) right) _).
    intros left_head left_tail.
    refine (Vector.caseS' right (fun right =>
      qdot (@Vector.cons Q coefficient d tail)
        (Vector.map2 Qplus (@Vector.cons Q left_head d left_tail) right) ==
      qdot (@Vector.cons Q coefficient d tail)
          (@Vector.cons Q left_head d left_tail) +
        qdot (@Vector.cons Q coefficient d tail) right) _).
    intros right_head right_tail. cbn. setoid_rewrite IH. ring.
Qed.

Lemma qvector_clear_denominators : forall d (value : Vector.t Q d),
    exists denominator numerator,
      (0 < denominator)%nat /\
      forall index,
        inject_Z (Vector.nth numerator index) ==
          q_of_nat denominator * Vector.nth value index.
Proof.
  intros d value. induction value as [|head d tail IH].
  - exists 1%nat, (@Vector.nil Z). split; [lia|].
    intro index. inversion index.
  - destruct head as [head_num head_den].
    destruct IH as [tail_denominator [tail_numerator
      [Htail_positive Htail]]].
    exists (Pos.to_nat head_den * tail_denominator)%nat,
      (@Vector.cons Z (head_num * Z.of_nat tail_denominator)%Z
        d (Vector.map (Z.mul (Z.pos head_den)) tail_numerator)).
    split.
    + pose proof (Pos2Nat.is_pos head_den). nia.
    + intro index. refine (Fin.caseS' index (fun index =>
        inject_Z (Vector.nth
          (@Vector.cons Z (head_num * Z.of_nat tail_denominator)%Z d
            (Vector.map (Z.mul (Z.pos head_den)) tail_numerator)) index) ==
        q_of_nat (Pos.to_nat head_den * tail_denominator) *
          Vector.nth (@Vector.cons Q (head_num # head_den) d tail) index) _ _).
      * cbn. unfold q_of_nat. rewrite Nat2Z.inj_mul, positive_nat_Z,
          inject_Z_mult.
        pose proof (Qmake_Qdiv head_num head_den) as Hhead.
        setoid_rewrite Hhead.
        transitivity
          (inject_Z (Z.of_nat tail_denominator) *
            (inject_Z (Z.pos head_den) *
              (inject_Z head_num / inject_Z (Z.pos head_den)))).
        -- setoid_rewrite Qmult_div_r.
           ++ ring.
           ++ intro Hzero. apply (proj1 (inject_Z_injective _ _)) in Hzero.
              discriminate.
        -- transitivity
             ((inject_Z (Z.of_nat tail_denominator) *
                inject_Z (Z.pos head_den)) *
               (inject_Z head_num / inject_Z (Z.pos head_den))).
           ++ apply Qmult_assoc.
           ++ apply Qmult_comp; [apply Qmult_comm|reflexivity].
      * intro tail_index. cbn.
        rewrite (nth_map _ _ tail_index tail_index eq_refl), inject_Z_mult.
        unfold q_of_nat in *. rewrite Nat2Z.inj_mul, positive_nat_Z,
          inject_Z_mult. setoid_rewrite (Htail tail_index). ring.
Qed.

Lemma qvec_clear_denominators : forall d (value : QVec d),
    exists denominator numerator,
      (0 < denominator)%nat /\
      QVecEq value
        (qvec_scale (/ q_of_nat denominator) (zvec_to_qvec numerator)).
Proof.
  intros d value.
  destruct (qvector_clear_denominators d (qvec_to_vector d value)) as
    [denominator [numerator [Hpositive Hclear]]].
  exists denominator, numerator. split; [exact Hpositive|].
  intro index. unfold qvec_scale, zvec_to_qvec.
  specialize (Hclear index). rewrite qvec_to_vector_nth in Hclear.
  transitivity
    (/ q_of_nat denominator *
      (q_of_nat denominator * value index)).
  - symmetry. field. apply q_of_nat_nonzero_hl. exact Hpositive.
  - apply Qmult_comp; [reflexivity|symmetry; exact Hclear].
Qed.

Definition zvec_scale_nat {d} (coefficient : nat) (value : ZVec d) : ZVec d :=
  Vector.map (Z.mul (Z.of_nat coefficient)) value.

Lemma zvec_scale_nat_nth : forall d coefficient (value : ZVec d) index,
    Vector.nth (zvec_scale_nat coefficient value) index =
      (Z.of_nat coefficient * Vector.nth value index)%Z.
Proof.
  intros. unfold zvec_scale_nat.
  now rewrite (nth_map _ _ index index eq_refl).
Qed.

Lemma qmatrix_clear_denominators : forall rows d (matrix : QMatrix rows d),
    exists denominator integer_matrix,
      (0 < denominator)%nat /\
      forall row column,
        inject_Z (Vector.nth (Vector.nth integer_matrix row) column) ==
          q_of_nat denominator *
            Vector.nth (Vector.nth matrix row) column.
Proof.
  intros rows d matrix. induction matrix as [|head rows tail IH].
  - exists 1%nat, (@Vector.nil (ZVec d)). split; [lia|].
    intro row. inversion row.
  - destruct (qvector_clear_denominators d head) as
      [head_denominator [head_integer [Hhead_positive Hhead]]].
    destruct IH as [tail_denominator [tail_integer
      [Htail_positive Htail]]].
    exists (head_denominator * tail_denominator)%nat,
      (@Vector.cons (ZVec d)
        (zvec_scale_nat tail_denominator head_integer) rows
        (Vector.map (zvec_scale_nat head_denominator) tail_integer)).
    split; [nia|].
    intros row column.
    refine (Fin.caseS' row (fun row =>
      inject_Z (Vector.nth
        (Vector.nth
          (@Vector.cons (ZVec d)
            (zvec_scale_nat tail_denominator head_integer) rows
            (Vector.map (zvec_scale_nat head_denominator) tail_integer)) row)
        column) ==
      q_of_nat (head_denominator * tail_denominator) *
        Vector.nth
          (Vector.nth
            (@Vector.cons (Vector.t Q d) head rows tail) row) column) _ _).
    + cbn. rewrite zvec_scale_nat_nth.
      unfold q_of_nat. rewrite Nat2Z.inj_mul, !inject_Z_mult.
      setoid_rewrite (Hhead column). unfold q_of_nat. ring.
    + intro tail_row. cbn.
      rewrite (nth_map _ _ tail_row tail_row eq_refl). cbn.
      rewrite zvec_scale_nat_nth.
      unfold q_of_nat. rewrite Nat2Z.inj_mul, !inject_Z_mult.
      setoid_rewrite (Htail tail_row column). unfold q_of_nat. ring.
Qed.

Definition zrow_qapply {d} (row : ZVec d) (value : QVec d) : Q :=
  qdot (Vector.map inject_Z row) (qvec_to_vector d value).

Lemma qrow_apply_qvec_ext : forall d (row : Vector.t Q d) left right,
    QVecEq left right ->
    qrow_apply row left == qrow_apply row right.
Proof.
  intros d row left right Heq. unfold qrow_apply.
  apply qdot_ext; [intro index; reflexivity|].
  intro index. rewrite !qvec_to_vector_nth. apply Heq.
Qed.

Lemma cleared_matrix_row_apply : forall rows d (matrix : QMatrix rows d)
    denominator (integer_matrix : ZMatrix rows d),
    (forall row column,
      inject_Z (Vector.nth (Vector.nth integer_matrix row) column) ==
        q_of_nat denominator *
          Vector.nth (Vector.nth matrix row) column) ->
    forall row value,
      zrow_qapply (Vector.nth integer_matrix row) value ==
        q_of_nat denominator *
          qrow_apply (Vector.nth matrix row) value.
Proof.
  intros rows d matrix denominator integer_matrix Hclear row value.
  unfold zrow_qapply, qrow_apply.
  transitivity
    (qdot (Vector.map (Qmult (q_of_nat denominator))
      (Vector.nth matrix row)) (qvec_to_vector d value)).
  - apply qdot_ext; [|intro index; reflexivity].
    intro column. rewrite (nth_map _ _ column column eq_refl),
      (nth_map _ _ column column eq_refl).
    apply Hclear.
  - apply qdot_scale_left.
Qed.

Lemma cleared_matrix_constraints_iff : forall rows d
    (matrix : QMatrix rows d) denominator
    (integer_matrix : ZMatrix rows d),
    (0 < denominator)%nat ->
    (forall row column,
      inject_Z (Vector.nth (Vector.nth integer_matrix row) column) ==
        q_of_nat denominator *
          Vector.nth (Vector.nth matrix row) column) ->
    forall value,
      HConicalConstraints matrix value <->
      (forall row, 0 <= zrow_qapply (Vector.nth integer_matrix row) value).
Proof.
  intros rows d matrix denominator integer_matrix Hpositive Hclear value.
  split; intros H row.
  - setoid_rewrite (cleared_matrix_row_apply rows d matrix denominator
      integer_matrix Hclear row value).
    apply Qmult_le_0_compat.
    + unfold q_of_nat, Qle; cbn. lia.
    + apply H.
  - assert (Hqpositive : 0 < q_of_nat denominator).
    { unfold q_of_nat, Qlt; cbn. lia. }
    apply (proj1 (Qmult_le_l 0
      (qrow_apply (Vector.nth matrix row) value)
      (q_of_nat denominator) Hqpositive)).
    setoid_rewrite Qmult_0_r.
    setoid_rewrite <- (cleared_matrix_row_apply rows d matrix denominator
      integer_matrix Hclear row value).
    apply H.
Qed.

Lemma zrow_apply_append : forall left_d right_d
    (left : ZVec left_d) (right : ZVec right_d)
    (left_value : NVec left_d) (right_value : NVec right_d),
    zrow_apply (Vector.append left right)
      (Vector.append left_value right_value) =
      (zrow_apply left left_value + zrow_apply right right_value)%Z.
Proof.
  intros left_d right_d left. induction left as [|coefficient left_d tail IH];
    intros right left_value right_value.
  - refine (Vector.case0 (fun left_value =>
      zrow_apply (Vector.append (@Vector.nil Z) right)
        (Vector.append left_value right_value) =
      (zrow_apply (@Vector.nil Z) left_value +
        zrow_apply right right_value)%Z) _ left_value). reflexivity.
  - refine (Vector.caseS' left_value (fun left_value =>
      zrow_apply (Vector.append (@Vector.cons Z coefficient left_d tail) right)
        (Vector.append left_value right_value) =
      (zrow_apply (@Vector.cons Z coefficient left_d tail) left_value +
        zrow_apply right right_value)%Z) _).
    intros head value_tail. cbn. rewrite IH. ring.
Qed.

Lemma zrow_apply_opp : forall d (row : ZVec d) value,
    zrow_apply (Vector.map Z.opp row) value = (- zrow_apply row value)%Z.
Proof.
  intros d row. induction row as [|coefficient d tail IH]; intro value.
  - cbn. lia.
  - refine (Vector.caseS' value (fun value =>
      zrow_apply (Vector.map Z.opp (@Vector.cons Z coefficient d tail)) value =
        (- zrow_apply (@Vector.cons Z coefficient d tail) value)%Z) _).
    intros head value_tail. cbn. rewrite IH. ring.
Qed.

Fixpoint zneg_unit {rows} (row : Fin.t rows) : ZVec rows :=
  match rows return Fin.t rows -> ZVec rows with
  | O => fun impossible => Fin.case0 _ impossible
  | S rows' => fun row =>
      Fin.caseS' row (fun _ => ZVec (S rows'))
        (@Vector.cons Z (-1)%Z rows' (Vector.const 0%Z rows'))
        (fun tail_row =>
          @Vector.cons Z 0%Z rows' (zneg_unit tail_row))
  end row.

Lemma zrow_apply_zero_row : forall rows (value : NVec rows),
    zrow_apply (zvec_zero rows) value = 0%Z.
Proof.
  intros rows value. induction value as [|head rows tail IH]; cbn.
  - reflexivity.
  - exact IH.
Qed.

Lemma zrow_apply_zneg_unit : forall rows (row : Fin.t rows) value,
    zrow_apply (zneg_unit row) value =
      (- Z.of_nat (Vector.nth value row))%Z.
Proof.
  intros rows. induction rows as [|rows IH]; intros row value.
  - inversion row.
  - refine (Fin.caseS' row (fun row =>
      zrow_apply (zneg_unit row) value =
        (- Z.of_nat (Vector.nth value row))%Z) _ _).
    + refine (Vector.caseS' value (fun value =>
        zrow_apply (zneg_unit Fin.F1) value =
          (- Z.of_nat (Vector.nth value Fin.F1))%Z) _).
      intros head tail. cbn. rewrite zrow_apply_zero_row, Z.add_0_r. reflexivity.
    + intros tail_row. refine (Vector.caseS' value (fun value =>
        zrow_apply (zneg_unit (Fin.FS tail_row)) value =
          (- Z.of_nat (Vector.nth value (Fin.FS tail_row)))%Z) _).
      intros head tail. cbn. apply IH.
Qed.

Definition homogenized_row {rows d} (row : Fin.t rows) (value : ZVec d) :
    ZVec (d + (d + rows)) :=
  Vector.append value
    (Vector.append (Vector.map Z.opp value) (zneg_unit row)).

Definition homogenized_matrix {rows d} (matrix : ZMatrix rows d) :
    ZMatrix rows (d + (d + rows)) :=
  vector_of_finfun (ZVec (d + (d + rows))) rows
    (fun row => homogenized_row row (Vector.nth matrix row)).

Lemma zrow_apply_homogenized : forall rows d (row : Fin.t rows)
    (matrix_row : ZVec d) (positive negative : NVec d) (slack : NVec rows),
    zrow_apply (homogenized_row row matrix_row)
      (Vector.append positive (Vector.append negative slack)) =
    (zrow_apply matrix_row positive - zrow_apply matrix_row negative -
      Z.of_nat (Vector.nth slack row))%Z.
Proof.
  intros. unfold homogenized_row.
  rewrite !zrow_apply_append, zrow_apply_opp, zrow_apply_zneg_unit. ring.
Qed.

Lemma homogenized_matrix_nth : forall rows d (matrix : ZMatrix rows d)
    (row : Fin.t rows),
    Vector.nth (homogenized_matrix matrix) row =
      homogenized_row row (Vector.nth matrix row).
Proof.
  intros. unfold homogenized_matrix.
  apply vector_of_finfun_nth.
Qed.

Lemma homogenized_solution_exact : forall rows d (matrix : ZMatrix rows d)
    positive negative slack,
    HomogeneousSolution (homogenized_matrix matrix)
      (Vector.append positive (Vector.append negative slack)) <->
    forall row,
      (zrow_apply (Vector.nth matrix row) positive -
        zrow_apply (Vector.nth matrix row) negative =
        Z.of_nat (Vector.nth slack row))%Z.
Proof.
  intros rows d matrix positive negative slack.
  unfold HomogeneousSolution, LinearSolution, matrix_apply. split.
  - intros Heq row.
    pose proof ((proj2 (Vector.eq_nth_iff Z rows _ _) Heq)
      row row eq_refl) as Hrow.
    unfold zvec_zero in Hrow.
    rewrite (nth_map _ _ row row eq_refl),
      (const_nth Z 0%Z rows row), homogenized_matrix_nth in Hrow.
    rewrite zrow_apply_homogenized in Hrow. lia.
  - intro Hrows. apply (proj1 (Vector.eq_nth_iff Z rows _ _)).
    intros row row' Heq; subst row'.
    unfold zvec_zero.
    rewrite (nth_map _ _ row row eq_refl),
      (const_nth Z 0%Z rows row), homogenized_matrix_nth,
      zrow_apply_homogenized.
    specialize (Hrows row). lia.
Qed.

Definition nvec_left {d extra} (value : NVec (d + extra)) : NVec d :=
  fst (Vector.splitat d value).

Definition nvec_right {d extra} (value : NVec (d + extra)) : NVec extra :=
  snd (Vector.splitat d value).

Lemma nvec_parts : forall d extra (value : NVec (d + extra)),
    value = Vector.append (nvec_left value) (nvec_right value).
Proof.
  intros d extra value. unfold nvec_left, nvec_right.
  destruct (Vector.splitat d value) as [left right] eqn:Hsplit.
  apply Vector.append_splitat in Hsplit. now symmetry.
Qed.

Definition solution_positive {rows d} (value : NVec (d + (d + rows))) :
    NVec d := nvec_left value.

Definition solution_remainder {rows d}
    (value : NVec (d + (d + rows))) : NVec (d + rows) := nvec_right value.

Definition solution_negative {rows d} (value : NVec (d + (d + rows))) :
    NVec d := nvec_left (solution_remainder value).

Definition solution_slack {rows d} (value : NVec (d + (d + rows))) :
    NVec rows := nvec_right (solution_remainder value).

Lemma solution_three_parts : forall rows d
    (value : NVec (d + (d + rows))),
    value = Vector.append (solution_positive value)
      (Vector.append (solution_negative value) (solution_slack value)).
Proof.
  intros rows d value. unfold solution_positive, solution_remainder,
    solution_negative, solution_slack, nvec_left, nvec_right.
  destruct (Vector.splitat d value) as [positive remainder] eqn:Houter.
  destruct (Vector.splitat d remainder) as [negative slack] eqn:Hinner.
  apply Vector.append_splitat in Houter.
  apply Vector.append_splitat in Hinner. subst remainder value.
  unfold solution_remainder, nvec_right.
  rewrite VectorSpec.splitat_append. cbn.
  rewrite VectorSpec.splitat_append. reflexivity.
Qed.

Definition project_solution {rows d}
    (value : NVec (d + (d + rows))) : QVec d :=
  fun index =>
    inject_Z (Z.of_nat (Vector.nth (solution_positive value) index)) -
    inject_Z (Z.of_nat (Vector.nth (solution_negative value) index)).

Lemma nvec_add_append_hl : forall left_d right_d
    (left1 left2 : NVec left_d) (right1 right2 : NVec right_d),
    nvec_add (Vector.append left1 right1) (Vector.append left2 right2) =
      Vector.append (nvec_add left1 left2) (nvec_add right1 right2).
Proof.
  intros left_d right_d left1. induction left1 as [|head left_d tail IH];
    intros left2 right1 right2.
  - refine (Vector.case0 (fun left2 => _ = _) _ left2). reflexivity.
  - refine (Vector.caseS' left2 (fun left2 => _ = _) _).
    intros head2 tail2. cbn. f_equal. apply IH.
Qed.

Lemma nvec_scale_append_hl : forall left_d right_d coefficient
    (left : NVec left_d) (right : NVec right_d),
    nvec_scale coefficient (Vector.append left right) =
      Vector.append (nvec_scale coefficient left) (nvec_scale coefficient right).
Proof.
  intros. unfold nvec_scale. apply Vector.map_append.
Qed.

Lemma project_solution_append : forall rows d
    (positive negative : NVec d) (slack : NVec rows) index,
    project_solution (Vector.append positive (Vector.append negative slack)) index =
      (inject_Z (Z.of_nat (Vector.nth positive index)) -
        inject_Z (Z.of_nat (Vector.nth negative index)))%Q.
Proof.
  intros. unfold project_solution, solution_positive, solution_negative,
    solution_remainder, nvec_left, nvec_right.
  rewrite VectorSpec.splitat_append. cbn.
  rewrite VectorSpec.splitat_append. reflexivity.
Qed.

Lemma project_solution_add : forall rows d
    (left right : NVec (d + (d + rows))),
    QVecEq (project_solution (nvec_add left right))
      (qvec_add (project_solution left) (project_solution right)).
Proof.
  intros rows d left right index.
  pose proof (solution_three_parts rows d left) as Hleft.
  pose proof (solution_three_parts rows d right) as Hright.
  rewrite Hleft, Hright, !nvec_add_append_hl,
    !project_solution_append.
  unfold qvec_add.
  rewrite (project_solution_append rows d (solution_positive left)
      (solution_negative left) (solution_slack left) index),
    (project_solution_append rows d (solution_positive right)
      (solution_negative right) (solution_slack right) index).
  repeat rewrite (nth_map2 Nat.add _ _ index index index
    eq_refl eq_refl), Nat2Z.inj_add, inject_Z_plus. ring.
Qed.

Lemma project_solution_scale : forall rows d coefficient
    (value : NVec (d + (d + rows))),
    QVecEq (project_solution (nvec_scale coefficient value))
      (qvec_scale (q_of_nat coefficient) (project_solution value)).
Proof.
  intros rows d coefficient value index.
  pose proof (solution_three_parts rows d value) as Hvalue.
  rewrite Hvalue, !nvec_scale_append_hl, !project_solution_append.
  unfold qvec_scale.
  rewrite (project_solution_append rows d (solution_positive value)
    (solution_negative value) (solution_slack value) index).
  unfold q_of_nat, nvec_scale.
  repeat rewrite (nth_map _ _ index index eq_refl), Nat2Z.inj_mul,
    inject_Z_mult. ring.
Qed.

Lemma zrow_qdot_difference : forall d (row : ZVec d)
    (positive negative : NVec d),
    qdot (Vector.map inject_Z row)
      (Vector.map2 (fun p n => inject_Z (Z.of_nat p) -
        inject_Z (Z.of_nat n)) positive negative) ==
    inject_Z (zrow_apply row positive - zrow_apply row negative).
Proof.
  intros d row. induction row as [|coefficient d tail IH];
    intros positive negative.
  - cbn. reflexivity.
  - revert negative.
    refine (Vector.caseS' positive (fun positive => forall negative,
      qdot (Vector.map inject_Z (@Vector.cons Z coefficient d tail))
        (Vector.map2 (fun p n => inject_Z (Z.of_nat p) -
          inject_Z (Z.of_nat n)) positive negative) ==
      inject_Z (zrow_apply (@Vector.cons Z coefficient d tail) positive -
        zrow_apply (@Vector.cons Z coefficient d tail) negative)) _).
    intros positive_head positive_tail negative.
    refine (Vector.caseS' negative (fun negative =>
      qdot (Vector.map inject_Z (@Vector.cons Z coefficient d tail))
        (Vector.map2 (fun p n => inject_Z (Z.of_nat p) -
          inject_Z (Z.of_nat n))
          (@Vector.cons nat positive_head d positive_tail) negative) ==
      inject_Z (zrow_apply (@Vector.cons Z coefficient d tail)
          (@Vector.cons nat positive_head d positive_tail) -
        zrow_apply (@Vector.cons Z coefficient d tail) negative)) _).
    intros negative_head negative_tail. cbn. setoid_rewrite IH.
    unfold Z.sub. rewrite !inject_Z_plus, !inject_Z_opp,
      !inject_Z_mult. rewrite inject_Z_plus, inject_Z_mult. ring.
Qed.

Lemma zrow_qapply_difference : forall d (row : ZVec d)
    (positive negative : NVec d),
    zrow_qapply row (fun index =>
      inject_Z (Z.of_nat (Vector.nth positive index)) -
      inject_Z (Z.of_nat (Vector.nth negative index))) ==
    inject_Z (zrow_apply row positive - zrow_apply row negative).
Proof.
  intros d row positive negative. unfold zrow_qapply.
  transitivity
    (qdot (Vector.map inject_Z row)
      (Vector.map2 (fun p n => inject_Z (Z.of_nat p) -
        inject_Z (Z.of_nat n)) positive negative)).
  - apply qdot_ext; [intro index; reflexivity|]. intro index.
    rewrite qvec_to_vector_nth,
      (nth_map2 _ _ _ index index index eq_refl eq_refl). reflexivity.
  - apply zrow_qdot_difference.
Qed.

Lemma zrow_qapply_project : forall rows d (row : ZVec d)
    (value : NVec (d + (d + rows))),
    zrow_qapply row (project_solution value) ==
      inject_Z (zrow_apply row (solution_positive value) -
        zrow_apply row (solution_negative value)).
Proof.
  intros rows d row value. unfold project_solution.
  apply zrow_qapply_difference.
Qed.

Lemma homogeneous_project_nonnegative : forall rows d
    (matrix : ZMatrix rows d) value,
    HomogeneousSolution (homogenized_matrix matrix) value ->
    forall row, 0 <= zrow_qapply (Vector.nth matrix row)
      (project_solution value).
Proof.
  intros rows d matrix value Hsolution row.
  pose proof (solution_three_parts rows d value) as Hparts.
  rewrite Hparts in Hsolution.
  pose proof (proj1 (@homogenized_solution_exact rows d matrix
    (solution_positive value) (solution_negative value)
    (solution_slack value)) Hsolution) as Hrows.
  setoid_rewrite (zrow_qapply_project rows d (Vector.nth matrix row) value).
  rewrite (Hrows row). unfold Qle; cbn. lia.
Qed.

Lemma qdot_scale_right : forall d coefficient
    (left right : Vector.t Q d),
    qdot left (Vector.map (Qmult coefficient) right) ==
      coefficient * qdot left right.
Proof.
  intros d coefficient left. induction left as [|head d tail IH]; intro right.
  - cbn. ring.
  - refine (Vector.caseS' right (fun right =>
      qdot (@Vector.cons Q head d tail) (Vector.map (Qmult coefficient) right) ==
        coefficient * qdot (@Vector.cons Q head d tail) right) _).
    intros right_head right_tail. cbn. setoid_rewrite IH. ring.
Qed.

Lemma qvec_to_vector_add : forall d (left right : QVec d) index,
    Vector.nth (qvec_to_vector d (qvec_add left right)) index ==
      Vector.nth (Vector.map2 Qplus (qvec_to_vector d left)
        (qvec_to_vector d right)) index.
Proof.
  intros. rewrite qvec_to_vector_nth,
    (nth_map2 _ _ _ index index index eq_refl eq_refl),
    !qvec_to_vector_nth. reflexivity.
Qed.

Lemma qvec_to_vector_scale : forall d coefficient (value : QVec d) index,
    Vector.nth (qvec_to_vector d (qvec_scale coefficient value)) index ==
      Vector.nth (Vector.map (Qmult coefficient)
        (qvec_to_vector d value)) index.
Proof.
  intros. rewrite qvec_to_vector_nth,
    (nth_map _ _ index index eq_refl), qvec_to_vector_nth. reflexivity.
Qed.

Lemma qrow_apply_zero : forall d (row : Vector.t Q d),
    qrow_apply row (qvec_zero d) == 0.
Proof.
  intros d row. induction row as [|head d tail IH].
  - reflexivity.
  - cbn [qrow_apply qvec_to_vector qvec_zero qdot].
    setoid_rewrite IH. unfold qvec_zero. cbn. ring.
Qed.

Lemma qrow_apply_add : forall d (row : Vector.t Q d) left right,
    qrow_apply row (qvec_add left right) ==
      qrow_apply row left + qrow_apply row right.
Proof.
  intros d row left right. unfold qrow_apply.
  transitivity (qdot row (Vector.map2 Qplus
    (qvec_to_vector d left) (qvec_to_vector d right))).
  - apply qdot_ext; [intro index; reflexivity|].
    apply qvec_to_vector_add.
  - apply qdot_add_right.
Qed.

Lemma qrow_apply_scale : forall d (row : Vector.t Q d) coefficient value,
    qrow_apply row (qvec_scale coefficient value) ==
      coefficient * qrow_apply row value.
Proof.
  intros d row coefficient value. unfold qrow_apply.
  transitivity (qdot row (Vector.map (Qmult coefficient)
    (qvec_to_vector d value))).
  - apply qdot_ext; [intro index; reflexivity|].
    apply qvec_to_vector_scale.
  - apply qdot_scale_right.
Qed.

Lemma hconstraints_qvec_ext : forall rows d (matrix : QMatrix rows d)
    left right,
    QVecEq left right ->
    (HConicalConstraints matrix left <-> HConicalConstraints matrix right).
Proof.
  intros rows d matrix left right Heq. split; intros H row.
  - setoid_rewrite <- (qrow_apply_qvec_ext d (Vector.nth matrix row)
      left right Heq). apply H.
  - setoid_rewrite (qrow_apply_qvec_ext d (Vector.nth matrix row)
      left right Heq). apply H.
Qed.

Lemma hconstraints_is_cone : forall rows d (matrix : QMatrix rows d),
    IsCone (HConicalConstraints matrix).
Proof.
  intros rows d matrix. constructor.
  - intro row. setoid_rewrite qrow_apply_zero. unfold Qle; cbn; lia.
  - intros left right Hleft Hright row.
    setoid_rewrite qrow_apply_add.
    change (0 + 0 <= qrow_apply (Vector.nth matrix row) left +
      qrow_apply (Vector.nth matrix row) right).
    apply Qplus_le_compat;
      [apply Hleft|apply Hright].
  - intros coefficient value Hcoefficient Hvalue row.
    setoid_rewrite qrow_apply_scale.
    apply Qmult_le_0_compat; [exact Hcoefficient|apply Hvalue].
Qed.

Lemma qcone_generated_subset_cone : forall d generators (set : QSet d),
    IsCone set ->
    (forall generator, List.In generator generators -> set generator) ->
    forall value, qcone_generated generators value ->
      (forall left right, QVecEq left right -> (set left <-> set right)) ->
      set value.
Proof.
  intros d generators set Hcone Hgenerators value
    [generated [Hcombination Heq]] Hext.
  assert (Hgenerated : set generated).
  { clear value Heq Hext. induction Hcombination.
    - apply cone_contains_zero with (set := set). exact Hcone.
    - apply cone_closed_add with (set := set);
        [exact Hcone| |exact IHHcombination].
      apply cone_closed_scale with (set := set); [exact Hcone|exact H|].
      now apply Hgenerators. }
  apply (proj2 (Hext value generated Heq)). exact Hgenerated.
Qed.

Lemma project_solution_zero : forall rows d,
    QVecEq (project_solution (nvec_zero (d + (d + rows)))) (qvec_zero d).
Proof.
  intros rows d.
  pose proof (project_solution_scale rows d 0
    (nvec_zero (d + (d + rows)))) as Hscale.
  rewrite nvec_scale_zero in Hscale.
  eapply qvec_eq_trans; [exact Hscale|].
  intro index. unfold qvec_scale, q_of_nat, qvec_zero. ring.
Qed.

Lemma weighted_sum_project_cone : forall rows d
    (generators : list (NVec (d + (d + rows)))) coefficients value,
    weighted_sum coefficients generators = Some value ->
    qcone_generated (List.map (@project_solution rows d) generators)
      (project_solution value).
Proof.
  intros rows d generators. induction generators as [|generator generators IH];
    intros coefficients value Hsum.
  - destruct coefficients; cbn in Hsum; try discriminate.
    inversion Hsum; subst value.
    change (qcone_generated []
      (project_solution (nvec_zero (d + (d + rows))))).
    apply (proj1 (qcone_generated_qvec_ext d []
      (qvec_zero d) (project_solution (nvec_zero (d + (d + rows))))
      (qvec_eq_sym d _ _ (project_solution_zero rows d)))).
    apply qcone_generated_zero.
  - destruct coefficients as [|coefficient coefficients]; try discriminate.
    cbn in Hsum.
    destruct (weighted_sum coefficients generators) as [tail|] eqn:Htail;
      try discriminate.
    inversion Hsum; subst value.
    assert (Htail_cone := IH coefficients tail Htail).
    assert (Hgenerator_cone : qcone_generated
      (List.map (@project_solution rows d) (generator :: generators))
      (project_solution generator)).
    { apply qcone_generated_generator. cbn. now left. }
    assert (Hscaled : qcone_generated
      (List.map (@project_solution rows d) (generator :: generators))
      (qvec_scale (q_of_nat coefficient) (project_solution generator))).
    { apply qcone_generated_scale.
      - unfold q_of_nat, Qle; cbn. lia.
      - exact Hgenerator_cone. }
    assert (Htail_cone' : qcone_generated
      (List.map (@project_solution rows d) (generator :: generators))
      (project_solution tail)).
    { destruct Htail_cone as [generated [Hcomb Heq]].
      assert (Hcomb' : QConeCombination
        (List.map (@project_solution rows d) (generator :: generators))
        generated).
      { clear Heq. induction Hcomb.
        - constructor.
        - constructor; [exact H|now right|exact IHHcomb]. }
      exists generated. split; [exact Hcomb'|exact Heq]. }
    pose proof (qcone_generated_add d
      (List.map (@project_solution rows d) (generator :: generators))
      (qvec_scale (q_of_nat coefficient) (project_solution generator))
      (project_solution tail) Hscaled Htail_cone') as Hadd.
    apply (proj2 (qcone_generated_qvec_ext d _
      (project_solution
        (nvec_add (nvec_scale coefficient generator) tail))
      (qvec_add (qvec_scale (q_of_nat coefficient) (project_solution generator))
        (project_solution tail))
      ltac:(eapply qvec_eq_trans;
        [apply project_solution_add|apply qvec_eq_add;
          [apply project_solution_scale|apply qvec_eq_refl]]))).
    exact Hadd.
Qed.

Definition zvec_positive {d} (value : ZVec d) : NVec d :=
  Vector.map Z.to_nat value.

Definition zvec_negative {d} (value : ZVec d) : NVec d :=
  Vector.map (fun coordinate => Z.to_nat (- coordinate)) value.

Lemma zvec_positive_negative : forall d (value : ZVec d) index,
    (Z.of_nat (Vector.nth (zvec_positive value) index) -
      Z.of_nat (Vector.nth (zvec_negative value) index) =
      Vector.nth value index)%Z.
Proof.
  intros d value index. unfold zvec_positive, zvec_negative.
  rewrite !nth_map with (p2 := index) by reflexivity.
  rewrite !ZifyInst.of_nat_to_nat_eq. lia.
Qed.

Lemma zrow_qapply_qvec_ext : forall d (row : ZVec d) left right,
    QVecEq left right ->
    zrow_qapply row left == zrow_qapply row right.
Proof.
  intros d row left right Heq. unfold zrow_qapply.
  apply qdot_ext; [intro index; reflexivity|]. intro index.
  rewrite !qvec_to_vector_nth. apply Heq.
Qed.

Lemma zrow_qapply_scale : forall d (row : ZVec d) coefficient value,
    zrow_qapply row (qvec_scale coefficient value) ==
      coefficient * zrow_qapply row value.
Proof.
  intros. unfold zrow_qapply.
  transitivity (qdot (Vector.map inject_Z row)
    (Vector.map (Qmult coefficient) (qvec_to_vector d value))).
  - apply qdot_ext; [intro index; reflexivity|].
    apply qvec_to_vector_scale.
  - apply qdot_scale_right.
Qed.

Lemma zrow_qapply_zvec : forall d (row value : ZVec d),
    zrow_qapply row (zvec_to_qvec value) ==
      inject_Z (zrow_apply row (zvec_positive value) -
        zrow_apply row (zvec_negative value)).
Proof.
  intros d row value.
  transitivity (zrow_qapply row (fun index =>
    inject_Z (Z.of_nat (Vector.nth (zvec_positive value) index)) -
    inject_Z (Z.of_nat (Vector.nth (zvec_negative value) index)))).
  - apply zrow_qapply_qvec_ext. intro index. unfold zvec_to_qvec.
    unfold Qminus.
    rewrite <- inject_Z_opp, <- inject_Z_plus.
    apply inject_Z_injective. symmetry. apply zvec_positive_negative.
  - apply zrow_qapply_difference.
Qed.

Lemma cleared_point_row_integer : forall d (row value : ZVec d)
    denominator (point : QVec d),
    (0 < denominator)%nat ->
    QVecEq point
      (qvec_scale (/ q_of_nat denominator) (zvec_to_qvec value)) ->
    zrow_qapply row point ==
      / q_of_nat denominator *
        inject_Z (zrow_apply row (zvec_positive value) -
          zrow_apply row (zvec_negative value)).
Proof.
  intros d row value denominator point Hpositive Heq.
  transitivity (zrow_qapply row
    (qvec_scale (/ q_of_nat denominator) (zvec_to_qvec value))).
  - apply zrow_qapply_qvec_ext. exact Heq.
  - setoid_rewrite zrow_qapply_scale. apply Qmult_comp; [reflexivity|].
    apply zrow_qapply_zvec.
Qed.

Lemma cleared_point_integer_nonnegative : forall d (row value : ZVec d)
    denominator (point : QVec d),
    (0 < denominator)%nat ->
    QVecEq point
      (qvec_scale (/ q_of_nat denominator) (zvec_to_qvec value)) ->
    0 <= zrow_qapply row point ->
    (0 <= zrow_apply row (zvec_positive value) -
      zrow_apply row (zvec_negative value))%Z.
Proof.
  intros d row value denominator point Hpositive Heq Hnonnegative.
  pose proof (cleared_point_row_integer d row value denominator point
    Hpositive Heq) as Hrow.
  assert (Hscaled : 0 <= q_of_nat denominator * zrow_qapply row point).
  { apply Qmult_le_0_compat.
    - unfold q_of_nat, Qle; cbn. lia.
    - exact Hnonnegative. }
  assert (Hequal : q_of_nat denominator * zrow_qapply row point ==
      inject_Z (zrow_apply row (zvec_positive value) -
        zrow_apply row (zvec_negative value))).
  { setoid_rewrite Hrow. field. apply q_of_nat_nonzero_hl. exact Hpositive. }
  setoid_rewrite Hequal in Hscaled. unfold Qle in Hscaled; cbn in Hscaled.
  lia.
Qed.

Definition integer_slack {rows d} (matrix : ZMatrix rows d)
    (value : ZVec d) : NVec rows :=
  vector_of_finfun nat rows (fun row => Z.to_nat
    (zrow_apply (Vector.nth matrix row) (zvec_positive value) -
      zrow_apply (Vector.nth matrix row) (zvec_negative value))).

Lemma integer_slack_nth : forall rows d (matrix : ZMatrix rows d)
    value row,
    Vector.nth (integer_slack matrix value) row = Z.to_nat
      (zrow_apply (Vector.nth matrix row) (zvec_positive value) -
        zrow_apply (Vector.nth matrix row) (zvec_negative value)).
Proof. intros. unfold integer_slack. apply vector_of_finfun_nth. Qed.

Lemma cleared_point_homogeneous_solution : forall rows d
    (matrix : ZMatrix rows d) denominator value point,
    (0 < denominator)%nat ->
    QVecEq point
      (qvec_scale (/ q_of_nat denominator) (zvec_to_qvec value)) ->
    (forall row, 0 <= zrow_qapply (Vector.nth matrix row) point) ->
    HomogeneousSolution (homogenized_matrix matrix)
      (Vector.append (zvec_positive value)
        (Vector.append (zvec_negative value) (integer_slack matrix value))).
Proof.
  intros rows d matrix denominator value point Hpositive Heq Hconstraints.
  apply (proj2 (@homogenized_solution_exact rows d matrix
    (zvec_positive value) (zvec_negative value)
    (integer_slack matrix value))). intro row.
  rewrite integer_slack_nth.
  symmetry. apply Z2Nat.id.
  now apply (cleared_point_integer_nonnegative d (Vector.nth matrix row)
    value denominator point Hpositive Heq (Hconstraints row)).
Qed.

Lemma project_integer_solution : forall rows d (matrix : ZMatrix rows d)
    value,
    QVecEq
      (project_solution
        (Vector.append (zvec_positive value)
          (Vector.append (zvec_negative value) (integer_slack matrix value))))
      (zvec_to_qvec value).
Proof.
  intros rows d matrix value index. rewrite project_solution_append.
  unfold zvec_to_qvec, Qminus. rewrite <- inject_Z_opp, <- inject_Z_plus.
  apply inject_Z_injective. apply zvec_positive_negative.
Qed.

Theorem rational_hcone_finitely_generated : forall rows d
    (matrix : QMatrix rows d),
    exists generators : list (QVec d),
      forall value : QVec d,
        HConicalConstraints matrix value <->
        qcone_generated generators value.
Proof.
  intros rows d matrix.
  destruct (qmatrix_clear_denominators rows d matrix) as
    [matrix_denominator [integer_matrix
      [Hmatrix_denominator Hmatrix_clear]]].
  destruct (homogeneous_solutions_finitely_generated rows
    (d + (d + rows)) (homogenized_matrix integer_matrix)) as
    [integer_generators [Hgenerator_solution Hgenerated]].
  exists (List.map (@project_solution rows d) integer_generators).
  intro value. split.
  - intro Hconstraints.
    pose proof (proj1 (cleared_matrix_constraints_iff rows d matrix
      matrix_denominator integer_matrix Hmatrix_denominator Hmatrix_clear
      value) Hconstraints) as Hinteger_constraints.
    destruct (qvec_clear_denominators d value) as
      [point_denominator [integer_value
        [Hpoint_denominator Hpoint_clear]]].
    set (integer_solution :=
      Vector.append (zvec_positive integer_value)
        (Vector.append (zvec_negative integer_value)
          (integer_slack integer_matrix integer_value))).
    assert (Hsolution : HomogeneousSolution
      (homogenized_matrix integer_matrix) integer_solution).
    { unfold integer_solution.
      apply (cleared_point_homogeneous_solution rows d integer_matrix
        point_denominator integer_value value Hpoint_denominator
        Hpoint_clear Hinteger_constraints). }
    pose proof (proj1 (Hgenerated integer_solution) Hsolution) as
      [coefficients Hcoefficients].
    pose proof (weighted_sum_project_cone rows d integer_generators
      coefficients integer_solution Hcoefficients) as Hproject_cone.
    assert (Hscaled_cone : qcone_generated
      (List.map (@project_solution rows d) integer_generators)
      (qvec_scale (/ q_of_nat point_denominator)
        (project_solution integer_solution))).
    { apply qcone_generated_scale.
      - apply Qinv_le_0_compat. unfold q_of_nat, Qle; cbn. lia.
      - exact Hproject_cone. }
    apply (proj2 (qcone_generated_qvec_ext d _ value
      (qvec_scale (/ q_of_nat point_denominator)
        (project_solution integer_solution))
      ltac:(eapply qvec_eq_trans; [exact Hpoint_clear|];
        apply qvec_eq_scale; [reflexivity|];
        apply qvec_eq_sym; unfold integer_solution;
        apply project_integer_solution))).
    exact Hscaled_cone.
  - intro Hcone.
    apply (proj2 (cleared_matrix_constraints_iff rows d matrix
      matrix_denominator integer_matrix Hmatrix_denominator Hmatrix_clear
      value)).
    apply (qcone_generated_subset_cone d
      (List.map (@project_solution rows d) integer_generators)
      (fun point => forall row,
        0 <= zrow_qapply (Vector.nth integer_matrix row) point)).
    + constructor.
      * intro row. unfold zrow_qapply. setoid_rewrite qrow_apply_zero.
        unfold Qle; cbn; lia.
      * intros left right Hleft Hright row.
        change (0 <= qrow_apply
          (Vector.map inject_Z (Vector.nth integer_matrix row))
          (qvec_add left right)).
        setoid_rewrite qrow_apply_add.
        change (0 + 0 <=
          qrow_apply (Vector.map inject_Z (Vector.nth integer_matrix row)) left +
          qrow_apply (Vector.map inject_Z (Vector.nth integer_matrix row)) right).
        apply Qplus_le_compat; [apply Hleft|apply Hright].
      * intros coefficient point Hcoefficient Hpoint row.
        change (0 <= qrow_apply
          (Vector.map inject_Z (Vector.nth integer_matrix row))
          (qvec_scale coefficient point)).
        setoid_rewrite qrow_apply_scale.
        apply Qmult_le_0_compat; [exact Hcoefficient|apply Hpoint].
    + intros generator Hin.
      apply in_map_iff in Hin as [integer_generator [Heq Hin]].
      subst generator. now apply homogeneous_project_nonnegative,
        Hgenerator_solution.
    + exact Hcone.
    + intros left right Heq. split; intros H row.
      * setoid_rewrite <- (zrow_qapply_qvec_ext d
          (Vector.nth integer_matrix row) left right Heq). apply H.
      * setoid_rewrite (zrow_qapply_qvec_ext d
          (Vector.nth integer_matrix row) left right Heq). apply H.
Qed.
