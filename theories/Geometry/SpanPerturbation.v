From Coq Require Import Fin Lia List Lra QArith QArith.Qabs Qminmax Qring
  Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import LatticeGordanH LatticeGordanPullback
  LatticeGordanV MathCompBridge QConeCore RationalConeAssembly RationalHToV
  RationalSpan.

Import ListNotations.
Open Scope Q_scope.

Definition qvec_cons_local {d} (head : Q) (tail : QVec d) : QVec (S d) :=
  fun index => Fin.caseS' index (fun _ => Q) head tail.

Definition qunit_head (d : nat) : QVec (S d) :=
  qvec_cons_local 1 (qvec_zero d).

Definition qneg_unit_head (d : nat) : QVec (S d) :=
  qvec_cons_local (-1) (qvec_zero d).

Definition qlift_tail {d} (value : QVec d) : QVec (S d) :=
  qvec_cons_local 0 value.

Fixpoint signed_coordinate_generators (d : nat) : list (QVec d) :=
  match d with
  | O => []
  | S d' => qunit_head d' :: qneg_unit_head d' ::
      List.map qlift_tail (signed_coordinate_generators d')
  end.

Definition qpositive_part (value : Q) : Q := (Qabs value + value) / 2.
Definition qnegative_part (value : Q) : Q := (Qabs value - value) / 2.

Lemma qpositive_part_nonnegative : forall value, 0 <= qpositive_part value.
Proof.
  intro value. unfold qpositive_part, Qdiv.
  apply Qmult_le_0_compat.
  - pose proof (proj1 (Qabs_Qle_condition value (Qabs value))
      (Qle_refl _)) as Habs.
    setoid_replace 0 with (Qabs value + - Qabs value) by ring.
    apply Qplus_le_compat; [apply Qle_refl|exact (proj1 Habs)].
  - unfold Qinv, Qle; cbn; lia.
Qed.

Lemma qnegative_part_nonnegative : forall value, 0 <= qnegative_part value.
Proof.
  intro value. unfold qnegative_part, Qminus, Qdiv.
  apply Qmult_le_0_compat.
  - pose proof (proj1 (Qabs_Qle_condition value (Qabs value))
      (Qle_refl _)) as Habs.
    setoid_replace 0 with (Qabs value + - Qabs value) by ring.
    apply Qplus_le_compat; [apply Qle_refl|].
    apply Qopp_le_compat. exact (proj2 Habs).
  - unfold Qinv, Qle; cbn; lia.
Qed.

Lemma qpositive_negative_difference : forall value,
    qpositive_part value - qnegative_part value == value.
Proof. intro value. unfold qpositive_part, qnegative_part, Qdiv, Qminus; field. Qed.

Lemma qpositive_negative_sum : forall value,
    qpositive_part value + qnegative_part value == Qabs value.
Proof. intro value. unfold qpositive_part, qnegative_part, Qdiv, Qminus; field. Qed.

Fixpoint signed_coefficient_list (d : nat) : QVec d -> list Q :=
  match d return QVec d -> list Q with
  | O => fun _ => []
  | S d' => fun value =>
      qpositive_part (value Fin.F1) :: qnegative_part (value Fin.F1) ::
        signed_coefficient_list d' (fun index => value (Fin.FS index))
  end.

Lemma signed_coefficient_list_length : forall d (value : QVec d),
    length (signed_coefficient_list d value) =
      length (signed_coordinate_generators d).
Proof.
  intros d. induction d as [|d IH]; intro value; cbn.
  - reflexivity.
  - rewrite length_map, IH. reflexivity.
Qed.

Definition signed_coefficients (d : nat) (value : QVec d) :
    Vector.t Q (length (signed_coordinate_generators d)) :=
  list_coefficients (length (signed_coordinate_generators d))
    (signed_coefficient_list d value).

Lemma signed_coefficient_list_nonnegative : forall d (value : QVec d),
    List.Forall (fun coefficient => 0 <= coefficient)
      (signed_coefficient_list d value).
Proof.
  intros d. induction d as [|d IH]; intro value; cbn.
  - constructor.
  - repeat constructor; try apply qpositive_part_nonnegative;
      try apply qnegative_part_nonnegative. apply IH.
Qed.

Lemma signed_coefficients_nonnegative : forall d (value : QVec d) index,
    0 <= Vector.nth (signed_coefficients d value) index.
Proof.
  intros d value index. unfold signed_coefficients.
  apply list_coefficients_nonnegative with
    (values := signed_coefficient_list d value).
  - apply signed_coefficient_list_length.
  - apply signed_coefficient_list_nonnegative.
Qed.

Lemma list_coefficients_to_list_exact : forall values n,
    length values = n ->
    Vector.to_list (list_coefficients n values) = values.
Proof.
  intros values. induction values as [|head tail IH]; intros n Hlength.
  - destruct n; [reflexivity|discriminate].
  - destruct n; [discriminate|]. cbn in Hlength. injection Hlength as Hlength.
    cbn. f_equal. now apply IH.
Qed.

Lemma qlift_tail_scale : forall d coefficient (value : QVec d),
    QVecEq (qvec_scale coefficient (qlift_tail value))
      (qlift_tail (qvec_scale coefficient value)).
Proof.
  intros d coefficient value index.
  refine (Fin.caseS' index (fun index => _) _ _).
  - change (coefficient * 0 == 0). ring.
  - intro tail_index. change (coefficient * value tail_index ==
      coefficient * value tail_index). reflexivity.
Qed.

Lemma qlift_tail_add : forall d (left right : QVec d),
    QVecEq (qvec_add (qlift_tail left) (qlift_tail right))
      (qlift_tail (qvec_add left right)).
Proof.
  intros d left right index.
  refine (Fin.caseS' index (fun index => _) _ _).
  - change (0 + 0 == 0). ring.
  - intro tail_index. change (left tail_index + right tail_index ==
      left tail_index + right tail_index). reflexivity.
Qed.

Lemma qlift_tail_zero : forall d,
    QVecEq (qvec_zero (S d)) (qlift_tail (qvec_zero d)).
Proof.
  intros d index. refine (Fin.caseS' index (fun index => _) _ _).
  - reflexivity.
  - intro tail_index. reflexivity.
Qed.

Lemma qlinear_combination_lift_tail : forall d
    (generators : list (QVec d)) coefficients,
    QVecEq
      (qlinear_combination (List.map qlift_tail generators) coefficients)
      (qlift_tail (qlinear_combination generators coefficients)).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients; destruct coefficients as [|coefficient coefficients].
  - apply qlift_tail_zero.
  - apply qlift_tail_zero.
  - apply qlift_tail_zero.
  - cbn [List.map qlinear_combination].
    eapply qvec_eq_trans.
    + apply qvec_eq_add; [apply qlift_tail_scale|apply IH].
    + apply qlift_tail_add.
Qed.

Lemma qv_signed_coefficients : forall d (value : QVec d),
    QVecEq
      (qv_combination (signed_coordinate_generators d)
        (signed_coefficients d value)) value.
Proof.
  intros d value.
  eapply qvec_eq_trans.
  - apply qv_combination_to_list.
  - unfold signed_coefficients.
    rewrite (list_coefficients_to_list_exact
      (signed_coefficient_list d value)
      (length (signed_coordinate_generators d))
      (signed_coefficient_list_length d value)).
    revert value. induction d as [|d IH]; intro value.
    - intro index. inversion index.
    - cbn [signed_coordinate_generators signed_coefficient_list
        qlinear_combination].
      eapply qvec_eq_trans.
      + apply qvec_eq_add; [apply qvec_eq_refl|].
        apply qvec_eq_add; [apply qvec_eq_refl|].
        apply qlinear_combination_lift_tail.
      + intro index. refine (Fin.caseS' index (fun index => _) _ _).
        * change (qpositive_part (value Fin.F1) * 1 +
            (qnegative_part (value Fin.F1) * -1 + 0) == value Fin.F1).
          transitivity (qpositive_part (value Fin.F1) -
            qnegative_part (value Fin.F1)); [ring|].
          apply qpositive_negative_difference.
        * intro tail_index.
          change (qpositive_part (value Fin.F1) * 0 +
            (qnegative_part (value Fin.F1) * 0 +
              qlinear_combination (signed_coordinate_generators d)
                (signed_coefficient_list d
                  (fun index => value (Fin.FS index))) tail_index) ==
            value (Fin.FS tail_index)).
          specialize (IH (fun index => value (Fin.FS index)) tail_index).
          setoid_rewrite IH. ring.
Qed.

Fixpoint qlist_sum (values : list Q) : Q :=
  match values with
  | [] => 0
  | value :: tail => value + qlist_sum tail
  end.

Fixpoint qvector_sum {n} (values : Vector.t Q n) : Q :=
  match values with
  | @Vector.nil _ => 0
  | @Vector.cons _ head _ tail => head + qvector_sum tail
  end.

Lemma qvec_abs_sum_of_vector_nonnegative : forall n
    (values : Vector.t Q n),
    Vector.Forall (fun value => 0 <= value) values ->
    qvec_abs_sum n (qvec_of_vector values) == qvector_sum values.
Proof.
  intros n values. induction values as [|head n tail IH]; intro Hvalues; cbn.
  - reflexivity.
  - pose proof (proj1 (Vector.Forall_nth _ _ _ _) Hvalues) as Hnth.
    apply Qplus_comp.
    + apply Qabs_pos. exact (Hnth Fin.F1).
    + apply IH. apply (proj2 (Vector.Forall_nth _ _ _ _)).
      intro index. exact (Hnth (Fin.FS index)).
Qed.

Lemma qvector_sum_list_coefficients : forall values n,
    length values = n ->
    qvector_sum (list_coefficients n values) == qlist_sum values.
Proof.
  intros values. induction values as [|head tail IH]; intros n Hlength.
  - destruct n; [reflexivity|discriminate].
  - destruct n; [discriminate|]. cbn in Hlength. injection Hlength as Hlength.
    cbn. apply Qplus_comp; [reflexivity|now apply IH].
Qed.

Lemma signed_coefficients_sum : forall d (value : QVec d),
    qvector_sum (signed_coefficients d value) == qvec_abs_sum d value.
Proof.
  intros d value. unfold signed_coefficients.
  eapply Qeq_trans.
  - apply qvector_sum_list_coefficients, signed_coefficient_list_length.
  - revert value. induction d as [|d IH]; intro value; cbn.
  - reflexivity.
  - transitivity ((qpositive_part (value Fin.F1) +
      qnegative_part (value Fin.F1)) +
      qlist_sum (signed_coefficient_list d
        (fun index => value (Fin.FS index)))).
    + ring.
    + transitivity (Qabs (value Fin.F1) +
        qlist_sum (signed_coefficient_list d
          (fun index => value (Fin.FS index)))).
      * apply Qplus_comp; [apply qpositive_negative_sum|reflexivity].
      * apply Qplus_comp; [reflexivity|apply IH].
Qed.

Lemma q_of_nat_succ_local : forall n,
    q_of_nat (S n) == q_of_nat n + 1.
Proof.
  intro n. unfold q_of_nat. rewrite Nat2Z.inj_succ.
  change (inject_Z (Z.of_nat n + 1) == inject_Z (Z.of_nat n) + inject_Z 1).
  rewrite inject_Z_plus. reflexivity.
Qed.

Lemma qvec_abs_sum_small : forall d (value : QVec d) epsilon,
    0 < epsilon ->
    (forall index, - epsilon < value index /\ value index < epsilon) ->
    qvec_abs_sum d value < q_of_nat (S d) * epsilon.
Proof.
  intros d. induction d as [|d IH]; intros value epsilon Hepsilon Hsmall.
  - cbn. unfold q_of_nat. setoid_replace (inject_Z 1 * epsilon)
      with epsilon by ring. exact Hepsilon.
  - cbn. assert (Hhead : Qabs (value Fin.F1) < epsilon).
    { apply (proj2 (Qabs_Qlt_condition _ _)). apply Hsmall. }
    assert (Htail : qvec_abs_sum d (fun index => value (Fin.FS index)) <
        q_of_nat (S d) * epsilon).
    { apply IH; [exact Hepsilon|intro index; apply Hsmall]. }
    setoid_rewrite q_of_nat_succ_local.
    setoid_replace ((q_of_nat (S d) + 1) * epsilon)
      with (epsilon + q_of_nat (S d) * epsilon) by ring.
    apply Qplus_lt_compat; assumption.
Qed.

Fixpoint qvector_min {n} (values : Vector.t Q n) : Q :=
  match values with
  | @Vector.nil _ => 1
  | @Vector.cons _ head _ tail => Qmin head (qvector_min tail)
  end.

Lemma qvector_min_positive : forall n (values : Vector.t Q n),
    Vector.Forall (fun value => 0 < value) values ->
    0 < qvector_min values.
Proof.
  intros n values H. induction H; cbn.
  - unfold Qlt; cbn; lia.
  - apply Q.min_glb_lt; assumption.
Qed.

Lemma qvector_min_le_nth : forall n (values : Vector.t Q n) index,
    qvector_min values <= Vector.nth values index.
Proof.
  intros n values. induction values as [|head n tail IH]; intro index.
  - inversion index.
  - refine (Fin.caseS' index (fun index => _) _ _).
    + cbn. apply Q.le_min_l.
    + intro tail_index. cbn. eapply Qle_trans; [apply Q.le_min_r|apply IH].
Qed.

Definition QVecNonnegative {d} (value : QVec d) : Prop :=
  forall index, 0 <= value index.

Lemma qvec_nonnegative_zero : forall d, QVecNonnegative (qvec_zero d).
Proof. intros d index. apply Qle_refl. Qed.

Lemma qvec_nonnegative_add : forall d (left right : QVec d),
    QVecNonnegative left -> QVecNonnegative right ->
    QVecNonnegative (qvec_add left right).
Proof.
  intros d left right Hleft Hright index. unfold qvec_add.
  setoid_replace 0 with (0 + 0) by ring.
  apply Qplus_le_compat; [apply Hleft|apply Hright].
Qed.

Lemma qvec_nonnegative_scale : forall d coefficient (value : QVec d),
    0 <= coefficient -> QVecNonnegative value ->
    QVecNonnegative (qvec_scale coefficient value).
Proof.
  intros d coefficient value Hcoefficient Hvalue index. unfold qvec_scale.
  apply Qmult_le_0_compat; [exact Hcoefficient|apply Hvalue].
Qed.

Lemma qvec_abs_sum_add_le : forall d (left right : QVec d),
    qvec_abs_sum d (qvec_add left right) <=
      qvec_abs_sum d left + qvec_abs_sum d right.
Proof.
  intros d. induction d as [|d IH]; intros left right; cbn.
  - apply Qle_refl.
  - eapply Qle_trans.
    + apply Qplus_le_compat; [apply Qabs_triangle|apply IH].
    + setoid_replace
        (Qabs (left Fin.F1) + Qabs (right Fin.F1) +
          (qvec_abs_sum d (fun index => left (Fin.FS index)) +
           qvec_abs_sum d (fun index => right (Fin.FS index))))
        with
        ((Qabs (left Fin.F1) +
          qvec_abs_sum d (fun index => left (Fin.FS index))) +
         (Qabs (right Fin.F1) +
          qvec_abs_sum d (fun index => right (Fin.FS index)))) by ring.
      apply Qle_refl.
Qed.

Lemma qvec_abs_sum_zero_local : forall d,
    qvec_abs_sum d (qvec_zero d) == 0.
Proof.
  intro d. induction d as [|d IH]; cbn; [reflexivity|].
  change (Qabs 0 + qvec_abs_sum d (qvec_zero d) == 0).
  setoid_rewrite (Qabs_pos 0 (Qle_refl _)). setoid_rewrite IH. ring.
Qed.

Lemma qvec_abs_sum_add_nonnegative : forall d (left right : QVec d),
    QVecNonnegative left -> QVecNonnegative right ->
    qvec_abs_sum d (qvec_add left right) ==
      qvec_abs_sum d left + qvec_abs_sum d right.
Proof.
  intros d. induction d as [|d IH]; intros left right Hleft Hright; cbn.
  - reflexivity.
  - setoid_rewrite (Qabs_pos (left Fin.F1) (Hleft Fin.F1)).
    setoid_rewrite (Qabs_pos (right Fin.F1) (Hright Fin.F1)).
    setoid_rewrite (Qabs_pos (left Fin.F1 + right Fin.F1)
      (Qplus_le_compat _ _ _ _ (Hleft Fin.F1) (Hright Fin.F1))).
    specialize (IH (fun index => left (Fin.FS index))
      (fun index => right (Fin.FS index))
      (fun index => Hleft (Fin.FS index))
      (fun index => Hright (Fin.FS index))).
    setoid_rewrite IH. ring.
Qed.

Lemma qvec_abs_sum_scale_nonnegative : forall d coefficient (value : QVec d),
    0 <= coefficient ->
    qvec_abs_sum d (qvec_scale coefficient value) ==
      coefficient * qvec_abs_sum d value.
Proof.
  intros d. induction d as [|d IH]; intros coefficient value Hcoefficient; cbn.
  - ring.
  - setoid_rewrite (qabs_scale_nonnegative coefficient (value Fin.F1)
      Hcoefficient).
    specialize (IH coefficient (fun index => value (Fin.FS index))
      Hcoefficient). setoid_rewrite IH. ring.
Qed.

Fixpoint qweighted_sum {d} (generators : list (QVec d))
    (coefficients : list Q) (measure : QVec d -> Q) : Q :=
  match generators, coefficients with
  | generator :: tail, coefficient :: coefficients' =>
      coefficient * measure generator + qweighted_sum tail coefficients' measure
  | _, _ => 0
  end.

Lemma qlinear_combination_abs_sum_bound : forall d
    (generators : list (QVec d)) coefficients,
    length coefficients = length generators ->
    List.Forall (fun coefficient => 0 <= coefficient) coefficients ->
    qvec_abs_sum d (qlinear_combination generators coefficients) <=
      qweighted_sum generators coefficients (qvec_abs_sum d).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength Hcoefficients.
  - destruct coefficients; [|discriminate].
    cbn [qlinear_combination qweighted_sum].
    setoid_rewrite qvec_abs_sum_zero_local. apply Qle_refl.
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    inversion Hcoefficients as [|? ? Hcoefficient Htail]; subst.
    cbn [qlinear_combination qweighted_sum].
    eapply Qle_trans; [apply qvec_abs_sum_add_le|].
    setoid_rewrite (qvec_abs_sum_scale_nonnegative d coefficient generator
      Hcoefficient).
    apply Qplus_le_compat; [apply Qle_refl|apply IH; assumption].
Qed.

Lemma qlinear_combination_nonnegative : forall d
    (generators : list (QVec d)) coefficients,
    length coefficients = length generators ->
    List.Forall QVecNonnegative generators ->
    List.Forall (fun coefficient => 0 <= coefficient) coefficients ->
    QVecNonnegative (qlinear_combination generators coefficients).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength Hgenerators Hcoefficients.
  - destruct coefficients; [apply qvec_nonnegative_zero|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    inversion Hgenerators as [|? ? Hgenerator Hgenerator_tail]; subst.
    inversion Hcoefficients as [|? ? Hcoefficient Hcoefficient_tail]; subst.
    cbn [qlinear_combination]. apply qvec_nonnegative_add.
    + now apply qvec_nonnegative_scale.
    + apply IH; assumption.
Qed.

Lemma qlinear_combination_abs_sum_nonnegative : forall d
    (generators : list (QVec d)) coefficients,
    length coefficients = length generators ->
    List.Forall QVecNonnegative generators ->
    List.Forall (fun coefficient => 0 <= coefficient) coefficients ->
    qvec_abs_sum d (qlinear_combination generators coefficients) ==
      qweighted_sum generators coefficients (qvec_abs_sum d).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength Hgenerators Hcoefficients.
  - destruct coefficients; [|discriminate].
    cbn [qlinear_combination qweighted_sum].
    apply qvec_abs_sum_zero_local.
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    inversion Hgenerators as [|? ? Hgenerator Hgenerator_tail]; subst.
    inversion Hcoefficients as [|? ? Hcoefficient Hcoefficient_tail]; subst.
    cbn [qlinear_combination qweighted_sum].
    setoid_rewrite (qvec_abs_sum_add_nonnegative d
      (qvec_scale coefficient generator)
      (qlinear_combination generators coefficients)
      (qvec_nonnegative_scale d coefficient generator Hcoefficient Hgenerator)
      (qlinear_combination_nonnegative d generators coefficients Hlength
        Hgenerator_tail Hcoefficient_tail)).
    setoid_rewrite (qvec_abs_sum_scale_nonnegative d coefficient generator
      Hcoefficient).
    setoid_rewrite (IH coefficients Hlength Hgenerator_tail
      Hcoefficient_tail). reflexivity.
Qed.

Lemma qvec_abs_sum_zero_of_nonnegative : forall d (value : QVec d),
    QVecNonnegative value -> qvec_abs_sum d value <= 0 ->
    QVecEq value (qvec_zero d).
Proof.
  intros d value Hnonnegative Hsum index.
  pose proof (qvec_abs_component_le_sum d value index) as Hcomponent.
  setoid_rewrite (Qabs_pos (value index) (Hnonnegative index)) in Hcomponent.
  unfold qvec_zero. apply Qle_antisym; [eapply Qle_trans; eauto|apply Hnonnegative].
Qed.

Definition lifted_mass {m n} (value : QVec (m + n)) : Q :=
  qvec_abs_sum n (qvec_right value).

Fixpoint prune_coefficients {m n} (generators : list (QVec (m + n)))
    (coefficients : list Q) : list Q :=
  match generators, coefficients with
  | generator :: generators', coefficient :: coefficients' =>
      (if Qlt_le_dec 0 (lifted_mass generator) then coefficient else 0) ::
        prune_coefficients generators' coefficients'
  | _, _ => []
  end.

Lemma prune_coefficients_length : forall m n
    (generators : list (QVec (m + n))) coefficients,
    length coefficients = length generators ->
    length (prune_coefficients generators coefficients) = length generators.
Proof.
  intros m n generators. induction generators as [|generator generators IH];
    intros coefficients Hlength.
  - destruct coefficients; [reflexivity|discriminate].
  - destruct coefficients; [discriminate|]. cbn in Hlength.
    injection Hlength as Hlength. cbn. f_equal. now apply IH.
Qed.

Lemma prune_coefficients_nonnegative : forall m n
    (generators : list (QVec (m + n))) coefficients,
    length coefficients = length generators ->
    List.Forall (fun coefficient => 0 <= coefficient) coefficients ->
    List.Forall (fun coefficient => 0 <= coefficient)
      (prune_coefficients generators coefficients).
Proof.
  intros m n generators. induction generators as [|generator generators IH];
    intros coefficients Hlength Hcoefficients.
  - destruct coefficients; [constructor|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    inversion Hcoefficients as [|? ? Hcoefficient Htail]; subst.
    cbn. constructor.
    + destruct (Qlt_le_dec 0 (lifted_mass generator));
        [exact Hcoefficient|apply Qle_refl].
    + now apply IH.
Qed.

Lemma hcone_generators_right_nonnegative : forall d
    (groups : list (ZVec d)) (cones : list (QVec d))
    (lifted_generators : list (QVec (length groups + length cones))),
    (forall value,
      HConicalConstraints (pullback_matrix groups cones) value <->
      qcone_generated lifted_generators value) ->
    List.Forall (fun generator => QVecNonnegative (qvec_right generator))
      lifted_generators.
Proof.
  intros d groups cones lifted_generators Hlifted.
  apply List.Forall_forall. intros generator Hin.
  assert (Hconstraints : HConicalConstraints (pullback_matrix groups cones)
      generator).
  { apply (proj2 (Hlifted generator)).
    now apply qcone_generated_generator. }
  assert (Hjoined : HConicalConstraints (pullback_matrix groups cones)
      (qvec_join (qvec_left generator) (qvec_right generator))).
  { apply (proj1 (hconstraints_qvec_ext _ _ _ generator _
      (qvec_join_split _ _ generator))). exact Hconstraints. }
  destruct (proj1 (pullback_matrix_constraints d groups cones
    (qvec_left generator) (qvec_right generator)) Hjoined) as
    [Hnonnegative _]. exact Hnonnegative.
Qed.

Lemma inactive_right_zero : forall m n (generator : QVec (m + n)),
    QVecNonnegative (qvec_right generator) ->
    ~ 0 < lifted_mass generator ->
    QVecEq (qvec_right generator) (qvec_zero n).
Proof.
  intros m n generator Hnonnegative Hinactive.
  apply qvec_abs_sum_zero_of_nonnegative; [exact Hnonnegative|].
  apply Qnot_lt_le. exact Hinactive.
Qed.

Lemma qvec_right_zero_local : forall n m,
    QVecEq (qvec_right (qvec_zero (n + m))) (qvec_zero m).
Proof.
  intros n m index. eapply Qeq_trans; [apply qvec_right_nth|]. reflexivity.
Qed.

Lemma qvec_right_add_local : forall n m (left right : QVec (n + m)),
    QVecEq (qvec_right (qvec_add left right))
      (qvec_add (qvec_right left) (qvec_right right)).
Proof.
  intros n m left right index.
  eapply Qeq_trans; [apply qvec_right_nth|]. unfold qvec_add.
  apply Qplus_comp; symmetry; apply qvec_right_nth.
Qed.

Lemma qvec_right_scale_local : forall n m coefficient
    (value : QVec (n + m)),
    QVecEq (qvec_right (qvec_scale coefficient value))
      (qvec_scale coefficient (qvec_right value)).
Proof.
  intros n m coefficient value index.
  eapply Qeq_trans; [apply qvec_right_nth|]. unfold qvec_scale.
  apply Qmult_comp; [reflexivity|symmetry; apply qvec_right_nth].
Qed.

Lemma qlinear_combination_map_right : forall n m
    (generators : list (QVec (n + m))) coefficients,
    QVecEq
      (qlinear_combination (List.map (@qvec_right n m) generators)
        coefficients)
      (qvec_right (qlinear_combination generators coefficients)).
Proof.
  intros n m generators. induction generators as [|generator generators IH];
    intros coefficients; destruct coefficients as [|coefficient coefficients].
  - apply qvec_eq_sym, qvec_right_zero_local.
  - apply qvec_eq_sym, qvec_right_zero_local.
  - apply qvec_eq_sym, qvec_right_zero_local.
  - cbn [List.map qlinear_combination].
    eapply qvec_eq_trans.
    + apply qvec_eq_add.
      * apply qvec_eq_scale; [reflexivity|apply qvec_eq_refl].
      * apply IH.
    + apply qvec_eq_sym.
      eapply qvec_eq_trans; [apply qvec_right_add_local|].
      apply qvec_eq_add; [apply qvec_right_scale_local|apply qvec_eq_refl].
Qed.

Lemma pruned_right_combination : forall m n
    (generators : list (QVec (m + n))) coefficients,
    length coefficients = length generators ->
    List.Forall (fun generator => QVecNonnegative (qvec_right generator))
      generators ->
    QVecEq
      (qlinear_combination (List.map (@qvec_right m n) generators)
        (prune_coefficients generators coefficients))
      (qlinear_combination (List.map (@qvec_right m n) generators)
        coefficients).
Proof.
  intros m n generators. induction generators as [|generator generators IH];
    intros coefficients Hlength Hgenerators.
  - destruct coefficients; [apply qvec_eq_refl|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    inversion Hgenerators as [|? ? Hgenerator Htail]; subst.
    cbn [prune_coefficients List.map qlinear_combination].
    destruct (Qlt_le_dec 0 (lifted_mass generator)) as [Hactive|Hinactive].
    + apply qvec_eq_add; [apply qvec_eq_refl|now apply IH].
    + eapply qvec_eq_trans with (y := qvec_add (qvec_zero n)
        (qlinear_combination (List.map (@qvec_right m n) generators)
          coefficients)).
      * apply qvec_eq_add; [|now apply IH].
        intro index. unfold qvec_scale, qvec_zero. ring.
      * apply qvec_eq_add; [|apply qvec_eq_refl].
        intro index. unfold qvec_scale, qvec_zero.
        pose proof (inactive_right_zero m n generator Hgenerator
          (Qle_not_lt _ _ Hinactive)) as Hzero.
        specialize (Hzero index). unfold qvec_zero in Hzero.
        setoid_rewrite Hzero. ring.
Qed.

Lemma pruned_combination_right : forall m n
    (generators : list (QVec (m + n))) coefficients,
    length coefficients = length generators ->
    List.Forall (fun generator => QVecNonnegative (qvec_right generator))
      generators ->
    QVecEq
      (qvec_right (qlinear_combination generators
        (prune_coefficients generators coefficients)))
      (qvec_right (qlinear_combination generators coefficients)).
Proof.
  intros m n generators coefficients Hlength Hgenerators.
  eapply qvec_eq_trans.
  - apply qvec_eq_sym, qlinear_combination_map_right.
  - eapply qvec_eq_trans.
    + apply pruned_right_combination; assumption.
    + apply qlinear_combination_map_right.
Qed.

Definition lifted_weight {m n} (generator : QVec (m + n)) : Q :=
  if Qlt_le_dec 0 (lifted_mass generator)
  then qvec_abs_sum m (qvec_left generator) / lifted_mass generator
  else 0.

Definition lifted_global_bound {m n}
    (generators : list (QVec (m + n))) : Q :=
  qlist_sum (List.map lifted_weight generators).

Lemma lifted_weight_nonnegative : forall m n (generator : QVec (m + n)),
    0 <= lifted_weight generator.
Proof.
  intros m n generator. unfold lifted_weight.
  destruct (Qlt_le_dec 0 (lifted_mass generator)) as [Hmass|Hmass].
  - apply Qmult_le_0_compat.
    + apply qvec_abs_sum_nonnegative.
    + apply Qlt_le_weak, Qinv_lt_0_compat. exact Hmass.
  - apply Qle_refl.
Qed.

Lemma lifted_global_bound_nonnegative : forall m n
    (generators : list (QVec (m + n))),
    0 <= lifted_global_bound generators.
Proof.
  intros m n generators. induction generators as [|generator generators IH];
    cbn [lifted_global_bound qlist_sum List.map].
  - apply Qle_refl.
  - setoid_replace 0 with (0 + 0) by ring.
    apply Qplus_le_compat; [apply lifted_weight_nonnegative|exact IH].
Qed.

Lemma qweighted_sum_nonnegative : forall d (measure : QVec d -> Q)
    (generators : list (QVec d)) coefficients,
    length coefficients = length generators ->
    List.Forall (fun coefficient => 0 <= coefficient) coefficients ->
    (forall generator, List.In generator generators -> 0 <= measure generator) ->
    0 <= qweighted_sum generators coefficients measure.
Proof.
  intros d measure generators. induction generators as [|generator generators IH];
    intros coefficients Hlength Hcoefficients Hmeasure.
  - destruct coefficients; [apply Qle_refl|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    inversion Hcoefficients as [|? ? Hcoefficient Htail]; subst.
    cbn [qweighted_sum]. setoid_replace 0 with (0 + 0) by ring.
    apply Qplus_le_compat.
    + apply Qmult_le_0_compat; [exact Hcoefficient|apply Hmeasure; now left].
    + apply IH; try assumption. intros value Hin. apply Hmeasure. now right.
Qed.

Lemma pruned_left_weight_bound : forall m n
    (generators : list (QVec (m + n))) coefficients,
    length coefficients = length generators ->
    List.Forall (fun coefficient => 0 <= coefficient) coefficients ->
    List.Forall (fun generator => QVecNonnegative (qvec_right generator))
      generators ->
    qweighted_sum (List.map (@qvec_left m n) generators)
      (prune_coefficients generators coefficients) (qvec_abs_sum m) <=
    qweighted_sum (List.map (@qvec_right m n) generators)
      coefficients (qvec_abs_sum n) * lifted_global_bound generators.
Proof.
  intros m n generators. induction generators as [|generator generators IH];
    intros coefficients Hlength Hcoefficients Hgenerators.
  - destruct coefficients; [apply Qle_refl|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    inversion Hcoefficients as [|? ? Hcoefficient Hcoefficient_tail]; subst.
    inversion Hgenerators as [|? ? Hgenerator Hgenerator_tail]; subst.
    cbn [prune_coefficients qweighted_sum lifted_global_bound qlist_sum
      List.map lifted_weight].
    pose proof (IH coefficients Hlength Hcoefficient_tail Hgenerator_tail)
      as IHbound.
    pose proof (qvec_abs_sum_nonnegative m (qvec_left generator)) as Hleft.
    pose proof (qvec_abs_sum_nonnegative n (qvec_right generator)) as Hmass.
    pose proof (qweighted_sum_nonnegative n (qvec_abs_sum n)
      (List.map (@qvec_right m n) generators) coefficients) as Htail_mass.
    assert (Hmap_length : length coefficients =
        length (List.map (@qvec_right m n) generators)) by
      (rewrite length_map; exact Hlength).
    specialize (Htail_mass Hmap_length Hcoefficient_tail).
    assert (Hmeasure : forall value,
        List.In value (List.map (@qvec_right m n) generators) ->
        0 <= qvec_abs_sum n value) by
      (intros; apply qvec_abs_sum_nonnegative).
    specialize (Htail_mass Hmeasure).
    pose proof (lifted_global_bound_nonnegative m n generators) as Htail_bound.
    destruct (Qlt_le_dec 0 (lifted_mass generator)) as [Hactive|Hinactive].
    + unfold lifted_mass in Hactive.
      unfold lifted_mass in *.
      assert (Hidentity :
          coefficient * qvec_abs_sum m (qvec_left generator) ==
          (coefficient * qvec_abs_sum n (qvec_right generator)) *
            (qvec_abs_sum m (qvec_left generator) /
              qvec_abs_sum n (qvec_right generator))).
      { field. intro Hzero. apply (Qlt_not_eq _ _ Hactive).
        symmetry. exact Hzero. }
      assert (Hratio : 0 <=
          qvec_abs_sum m (qvec_left generator) /
            qvec_abs_sum n (qvec_right generator)).
      { apply Qmult_le_0_compat; [exact Hleft|].
        apply Qlt_le_weak, Qinv_lt_0_compat. exact Hactive. }
      assert (Hhead_bound :
          coefficient * qvec_abs_sum m (qvec_left generator) <=
          (coefficient * qvec_abs_sum n (qvec_right generator) +
            qweighted_sum (List.map (@qvec_right m n) generators)
              coefficients (qvec_abs_sum n)) *
          (qvec_abs_sum m (qvec_left generator) /
            qvec_abs_sum n (qvec_right generator))).
      { setoid_rewrite Hidentity. apply Qmult_le_compat_r; [|exact Hratio].
        setoid_replace (coefficient * qvec_abs_sum n (qvec_right generator))
          with (coefficient * qvec_abs_sum n (qvec_right generator) + 0)
          at 1 by ring.
        apply Qplus_le_compat; [apply Qle_refl|exact Htail_mass]. }
      assert (Htail_bound' :
          qweighted_sum (List.map (@qvec_left m n) generators)
            (prune_coefficients generators coefficients) (qvec_abs_sum m) <=
          (coefficient * qvec_abs_sum n (qvec_right generator) +
            qweighted_sum (List.map (@qvec_right m n) generators)
              coefficients (qvec_abs_sum n)) *
            lifted_global_bound generators).
      { eapply Qle_trans; [exact IHbound|].
        apply Qmult_le_compat_r; [|exact Htail_bound].
        setoid_replace
          (qweighted_sum (List.map (@qvec_right m n) generators)
            coefficients (qvec_abs_sum n))
          with (0 + qweighted_sum (List.map (@qvec_right m n) generators)
            coefficients (qvec_abs_sum n)) at 1 by ring.
        apply Qplus_le_compat; [|apply Qle_refl].
        apply Qmult_le_0_compat; assumption. }
      eapply Qle_trans.
      * apply Qplus_le_compat; [exact Hhead_bound|exact Htail_bound'].
      * assert (Hweight : lifted_weight generator ==
            qvec_abs_sum m (qvec_left generator) /
              qvec_abs_sum n (qvec_right generator)).
        { unfold lifted_weight, lifted_mass.
          destruct (Qlt_le_dec 0 (qvec_abs_sum n (qvec_right generator)))
            as [Hpositive|Hnonpositive]; [reflexivity|].
          exfalso. exact (Qle_not_lt _ _ Hnonpositive Hactive). }
        unfold lifted_global_bound. cbn [qlist_sum List.map].
        setoid_rewrite Hweight.
        setoid_replace
          ((coefficient * qvec_abs_sum n (qvec_right generator) +
            qweighted_sum (List.map (@qvec_right m n) generators)
              coefficients (qvec_abs_sum n)) *
             (qvec_abs_sum m (qvec_left generator) /
                qvec_abs_sum n (qvec_right generator)) +
           (coefficient * qvec_abs_sum n (qvec_right generator) +
            qweighted_sum (List.map (@qvec_right m n) generators)
              coefficients (qvec_abs_sum n)) *
             lifted_global_bound generators)
          with
          ((coefficient * qvec_abs_sum n (qvec_right generator) +
            qweighted_sum (List.map (@qvec_right m n) generators)
              coefficients (qvec_abs_sum n)) *
           (qvec_abs_sum m (qvec_left generator) /
              qvec_abs_sum n (qvec_right generator) +
            lifted_global_bound generators)) by ring.
        apply Qle_refl.
    + assert (Htail_bound' :
          qweighted_sum (List.map (@qvec_left m n) generators)
            (prune_coefficients generators coefficients) (qvec_abs_sum m) <=
          (coefficient * qvec_abs_sum n (qvec_right generator) +
            qweighted_sum (List.map (@qvec_right m n) generators)
              coefficients (qvec_abs_sum n)) *
            lifted_global_bound generators).
      { eapply Qle_trans; [exact IHbound|].
        apply Qmult_le_compat_r; [|exact Htail_bound].
        setoid_replace
          (qweighted_sum (List.map (@qvec_right m n) generators)
            coefficients (qvec_abs_sum n))
          with (0 + qweighted_sum (List.map (@qvec_right m n) generators)
            coefficients (qvec_abs_sum n)) at 1 by ring.
        apply Qplus_le_compat; [|apply Qle_refl].
        apply Qmult_le_0_compat; assumption. }
      setoid_replace (0 * qvec_abs_sum m (qvec_left generator) +
        qweighted_sum (List.map (@qvec_left m n) generators)
          (prune_coefficients generators coefficients) (qvec_abs_sum m))
        with (qweighted_sum (List.map (@qvec_left m n) generators)
          (prune_coefficients generators coefficients) (qvec_abs_sum m)) by ring.
      assert (Hweight : lifted_weight generator == 0).
      { unfold lifted_weight.
        destruct (Qlt_le_dec 0 (lifted_mass generator)) as [Hpositive|];
          [exfalso; exact (Qle_not_lt _ _ Hinactive Hpositive)|reflexivity]. }
      unfold lifted_global_bound. cbn [qlist_sum List.map].
      setoid_rewrite Hweight. setoid_replace (0 + lifted_global_bound generators)
        with (lifted_global_bound generators) by ring.
      exact Htail_bound'.
Qed.

Lemma qvec_abs_sum_ext_local : forall d (left right : QVec d),
    QVecEq left right -> qvec_abs_sum d left == qvec_abs_sum d right.
Proof.
  intros d. induction d as [|d IH]; intros left right Heq; cbn.
  - reflexivity.
  - apply Qplus_comp.
    + apply Qabs_wd. apply Heq.
    + apply IH. intro index. apply Heq.
Qed.

Lemma qv_combination_coefficients_ext : forall d
    (generators : list (QVec d)) (left right : QVec (length generators)),
    QVecEq left right ->
    QVecEq
      (qv_combination generators (qvec_to_vector (length generators) left))
      (qv_combination generators (qvec_to_vector (length generators) right)).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros left right Heq.
  - apply qvec_eq_refl.
  - change (QVec (S (length generators))) in left.
    change (QVec (S (length generators))) in right.
    intro index. cbn [qv_combination qvec_to_vector]. unfold qvec_add, qvec_scale.
    apply Qplus_comp.
    + apply Qmult_comp; [apply Heq|reflexivity].
    + apply IH. intro coefficient. apply Heq.
Qed.

Lemma qvec_right_ext_local : forall n m (left right : QVec (n + m)),
    QVecEq left right -> QVecEq (qvec_right left) (qvec_right right).
Proof.
  intros n m left right Heq index.
  eapply Qeq_trans; [apply qvec_right_nth|].
  eapply Qeq_trans; [apply Heq|]. symmetry. apply qvec_right_nth.
Qed.

Lemma qlist_map_nonnegative_right : forall m n
    (generators : list (QVec (m + n))),
    List.Forall (fun generator => QVecNonnegative (qvec_right generator))
      generators ->
    List.Forall QVecNonnegative
      (List.map (@qvec_right m n) generators).
Proof.
  intros m n generators H. induction H; cbn; constructor; assumption.
Qed.

Lemma positive_fraction_bound : forall minimum factor,
    0 < minimum -> 0 <= factor ->
    minimum / (1 + factor) * factor < minimum.
Proof.
  intros minimum factor Hminimum Hfactor.
  assert (Hdenominator : 0 < 1 + factor).
  { eapply Qlt_le_trans; [|apply Qplus_le_compat; [apply Qle_refl|exact Hfactor]].
    unfold Qlt; cbn; lia. }
  apply (proj1 (Qmult_lt_r _ _ (1 + factor) Hdenominator)).
  setoid_replace ((minimum / (1 + factor) * factor) * (1 + factor))
    with (minimum * factor) by
      (field; intro Hzero; apply (Qlt_not_eq _ _ Hdenominator);
       symmetry; exact Hzero).
  setoid_replace (minimum * (1 + factor))
    with (minimum * factor + minimum) by ring.
  setoid_replace (minimum * factor) with (minimum * factor + 0) at 1
    by (symmetry; apply Qplus_0_r).
  apply (proj2 (Qplus_lt_r 0 minimum (minimum * factor))).
  exact Hminimum.
Qed.

Theorem qspan_uniform_small_coefficients :
  forall d (generators : list (ZVec d))
    (positive : Vector.t Q (length generators)),
    Vector.Forall (fun coefficient => 0 < coefficient) positive ->
    exists epsilon : Q,
      0 < epsilon /\
      forall w : QVec d,
        QSpan generators w ->
        (forall index : Fin.t d,
          - epsilon < w index /\ w index < epsilon) ->
        exists delta : Vector.t Q (length generators),
          QVecEq w (qgroup_combination generators delta) /\
          (forall index : Fin.t (length generators),
            - Vector.nth positive index < Vector.nth delta index /\
            Vector.nth delta index < Vector.nth positive index).
Proof.
  intros d generators positive Hpositive.
  set (cones := signed_coordinate_generators d).
  destruct (rational_hcone_finitely_generated
    (length cones + (d + d)) (length generators + length cones)
    (pullback_matrix generators cones)) as [lifted_generators Hlifted].
  assert (Hright_generators :
      List.Forall
        (fun generator => QVecNonnegative (qvec_right generator))
        lifted_generators).
  { now apply hcone_generators_right_nonnegative with
      (groups := generators) (cones := cones). }
  set (bound := lifted_global_bound lifted_generators).
  set (minimum := qvector_min positive).
  set (factor := q_of_nat (S d) * bound).
  set (epsilon := minimum / (1 + factor)).
  assert (Hminimum : 0 < minimum).
  { unfold minimum. now apply qvector_min_positive. }
  assert (Hbound : 0 <= bound).
  { unfold bound. apply lifted_global_bound_nonnegative. }
  assert (Hdimension : 0 <= q_of_nat (S d)).
  { apply Qlt_le_weak, q_of_nat_positive_v. lia. }
  assert (Hfactor : 0 <= factor).
  { unfold factor. now apply Qmult_le_0_compat. }
  assert (Hepsilon : 0 < epsilon).
  { unfold epsilon. apply Qmult_lt_0_compat; [exact Hminimum|].
    apply Qinv_lt_0_compat.
    eapply Qlt_le_trans; [|apply Qplus_le_compat; [apply Qle_refl|exact Hfactor]].
    unfold Qlt; cbn; lia. }
  exists epsilon. split; [exact Hepsilon|].
  intros w [source_coefficients Hw] Hsmall.
  set (z := qvec_of_vector source_coefficients).
  set (lambda := qvec_of_vector (signed_coefficients d w)).
  assert (Hlambda_nonnegative : forall index, 0 <= lambda index).
  { intro index. unfold lambda, qvec_of_vector.
    apply signed_coefficients_nonnegative. }
  assert (Hmap : QVecEq (F_Q generators z)
      (qv_combination cones (qvec_to_vector (length cones) lambda))).
  { eapply qvec_eq_trans.
    - unfold F_Q, z. rewrite qvec_to_vector_of_vector.
      apply qvec_eq_sym. exact Hw.
    - unfold cones, lambda. rewrite qvec_to_vector_of_vector.
      apply qvec_eq_sym, qv_signed_coefficients. }
  assert (Hconstraints : HConicalConstraints (pullback_matrix generators cones)
      (qvec_join z lambda)).
  { apply (proj2 (pullback_matrix_constraints d generators cones z lambda)).
    split; assumption. }
  assert (Hcone : qcone_generated lifted_generators (qvec_join z lambda)).
  { apply (proj1 (Hlifted _)). exact Hconstraints. }
  apply qcone_generated_aligned_coefficients in Hcone as
    [coefficients [Hlength [Hcoefficients Hlifted_point]]].
  set (active_coefficients := prune_coefficients lifted_generators coefficients).
  set (active_point := qlinear_combination lifted_generators active_coefficients).
  assert (Hactive_length : length active_coefficients = length lifted_generators).
  { unfold active_coefficients. now apply prune_coefficients_length. }
  assert (Hactive_nonnegative :
      List.Forall (fun coefficient => 0 <= coefficient) active_coefficients).
  { unfold active_coefficients. now apply prune_coefficients_nonnegative. }
  assert (Hactive_cone : qcone_generated lifted_generators active_point).
  { unfold active_point. now apply qlinear_combination_cone. }
  assert (Hactive_constraints :
      HConicalConstraints (pullback_matrix generators cones) active_point).
  { apply (proj2 (Hlifted active_point)). exact Hactive_cone. }
  assert (Hactive_joined : HConicalConstraints (pullback_matrix generators cones)
      (qvec_join (qvec_left active_point) (qvec_right active_point))).
  { apply (proj1 (hconstraints_qvec_ext _ _ _ active_point _
      (qvec_join_split _ _ active_point))). exact Hactive_constraints. }
  destruct (proj1 (pullback_matrix_constraints d generators cones
    (qvec_left active_point) (qvec_right active_point)) Hactive_joined) as
    [_ Hactive_map].
  assert (Hright_active : QVecEq (qvec_right active_point) lambda).
  { unfold active_point, active_coefficients.
    eapply qvec_eq_trans.
    - apply pruned_combination_right; assumption.
    - eapply qvec_eq_trans.
      + apply qvec_eq_sym, qvec_right_ext_local. exact Hlifted_point.
      + apply qvec_join_right. }
  assert (Hsigned : QVecEq w
      (qv_combination cones (qvec_to_vector (length cones) lambda))).
  { unfold cones, lambda. rewrite qvec_to_vector_of_vector.
    apply qvec_eq_sym, qv_signed_coefficients. }
  assert (Hw_active : QVecEq w (F_Q generators (qvec_left active_point))).
  { eapply qvec_eq_trans.
    - eapply qvec_eq_trans.
      + exact Hsigned.
      + apply qv_combination_coefficients_ext. apply qvec_eq_sym.
        exact Hright_active.
    - apply qvec_eq_sym. exact Hactive_map. }
  exists (qvec_to_vector (length generators) (qvec_left active_point)). split.
  - unfold F_Q in Hw_active. exact Hw_active.
  - intro index. apply (proj1 (Qabs_Qlt_condition _ _)).
    eapply Qle_lt_trans.
    + rewrite qvec_to_vector_nth.
      apply qvec_abs_component_le_sum.
    + eapply Qle_lt_trans.
      * unfold active_point.
        assert (Hleft_abs :
            qvec_abs_sum (length generators)
              (qvec_left
                (qlinear_combination lifted_generators active_coefficients)) ==
            qvec_abs_sum (length generators)
              (qlinear_combination
                (List.map (@qvec_left (length generators) (length cones))
                  lifted_generators) active_coefficients)).
        { apply qvec_abs_sum_ext_local, qvec_eq_sym.
          apply qlinear_combination_map_left. }
        setoid_rewrite Hleft_abs.
        eapply Qle_trans.
        -- apply qlinear_combination_abs_sum_bound.
           ++ rewrite length_map. exact Hactive_length.
           ++ exact Hactive_nonnegative.
        -- unfold active_coefficients, bound.
           apply pruned_left_weight_bound; assumption.
      * assert (Hright_mass :
            qweighted_sum
              (List.map (@qvec_right (length generators) (length cones))
                lifted_generators) coefficients (qvec_abs_sum (length cones)) ==
            qvec_abs_sum d w).
        { transitivity (qvec_abs_sum (length cones)
            (qlinear_combination
              (List.map (@qvec_right (length generators) (length cones))
                lifted_generators) coefficients)).
          - symmetry. apply qlinear_combination_abs_sum_nonnegative.
            + rewrite length_map. exact Hlength.
            + now apply qlist_map_nonnegative_right.
            + exact Hcoefficients.
          - eapply Qeq_trans.
            + apply qvec_abs_sum_ext_local, qlinear_combination_map_right.
            + eapply Qeq_trans.
              * apply qvec_abs_sum_ext_local.
                eapply qvec_eq_trans.
                -- apply qvec_right_ext_local. apply qvec_eq_sym.
                   exact Hlifted_point.
                -- apply qvec_join_right.
              * unfold cones, lambda.
                eapply Qeq_trans.
                -- apply qvec_abs_sum_of_vector_nonnegative.
                   apply (proj2 (Vector.Forall_nth _ _ _ _)).
                   intro coefficient. apply signed_coefficients_nonnegative.
                -- apply signed_coefficients_sum. }
        setoid_rewrite Hright_mass.
        assert (Hwsmall : qvec_abs_sum d w < q_of_nat (S d) * epsilon).
        { now apply qvec_abs_sum_small. }
        eapply Qle_lt_trans.
        -- apply Qmult_le_compat_r; [apply Qlt_le_weak; exact Hwsmall|exact Hbound].
        -- setoid_replace
             (q_of_nat (S d) * epsilon *
               lifted_global_bound lifted_generators)
             with (epsilon * factor) by
               (unfold factor, bound; ring).
           unfold epsilon.
           eapply Qlt_le_trans.
           ++ now apply positive_fraction_bound.
           ++ unfold minimum. apply qvector_min_le_nth.
Qed.
