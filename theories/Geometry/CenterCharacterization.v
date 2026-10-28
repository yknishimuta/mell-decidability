From Coq Require Import List Lia Lra QArith Qring Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Center ClosedLinearization LatticeGordanH
  LatticeGordanPullback LatticeGordanV MathCompBridge Periodic QConeCore
  RationalHToV RationalSpan.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Definition PositiveSpanningCombination {d} (set : ZSet d)
    (value : ZVec d) : Prop :=
  exists generators : list (ZVec d),
    List.Forall set generators /\
    (forall point : QVec d,
      VecOf set point <-> QSpan generators point) /\
    exists coefficients : Vector.t Q (length generators),
      Vector.Forall (fun coefficient => 0 < coefficient) coefficients /\
      QVecEq (zvec_to_qvec value)
        (qgroup_combination generators coefficients).

Lemma periodic_rsum : forall d (set : ZSet d) values,
    Periodic set -> List.Forall set values -> set (zvec_rsum values).
Proof.
  intros d set values Hperiodic Hvalues. induction Hvalues; cbn.
  - exact (proj1 Hperiodic).
  - apply (proj2 Hperiodic); assumption.
Qed.

Lemma qgroup_combination_const : forall d
    (generators : list (ZVec d)) coefficient,
    QVecEq
      (qgroup_combination generators
        (Vector.const coefficient (length generators)))
      (qvec_scale coefficient (zvec_to_qvec (zvec_rsum generators))).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intro coefficient; intro index.
  - cbn. unfold qvec_scale, qvec_zero, zvec_to_qvec, zvec_zero.
    rewrite const_nth. ring.
  - cbn. unfold qvec_add, qvec_scale, zvec_to_qvec, zvec_rsum, zvec_add.
    rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
      inject_Z_plus. specialize (IH coefficient index). cbn in IH.
    transitivity
      (coefficient * inject_Z (Vector.nth generator index) +
       coefficient * inject_Z (Vector.nth (zvec_rsum generators) index)).
    + apply Qplus_comp; [reflexivity|exact IH].
    + symmetry. apply Qmult_plus_distr_r.
Qed.

Lemma vector_forall_const_positive : forall n coefficient,
    0 < coefficient ->
    Vector.Forall (fun value : Q => 0 < value)
      (Vector.const coefficient n).
Proof.
  intros n coefficient Hpositive. induction n; cbn; constructor; assumption.
Qed.

Lemma qspan_cons_equiv : forall d head (generators : list (ZVec d)),
    QSpan generators (zvec_to_qvec head) ->
    forall value, QSpan (head :: generators) value <-> QSpan generators value.
Proof.
  intros d head generators Hhead value. split.
  - intros [coefficients Hvalue].
    revert Hvalue.
    refine (Vector.caseS' coefficients (fun coefficients =>
      QVecEq value (qgroup_combination (head :: generators) coefficients) ->
      QSpan generators value) _).
    intros coefficient tail Hvalue.
    apply (proj2 (qspan_qvec_ext d generators _ _ Hvalue)). cbn.
    apply qspan_add.
    + apply qspan_scale. exact Hhead.
    + exists tail. apply qvec_eq_refl.
  - apply qspan_cons.
Qed.

Lemma zvec_neg_rsum_difference : forall d (set : ZSet d) generators,
    Periodic set -> List.Forall set generators ->
    Difference set (zvec_sub (zvec_zero d) (zvec_rsum generators)).
Proof.
  intros d set generators Hperiodic Hgenerators.
  exists (zvec_zero d), (zvec_rsum generators). repeat split.
  - exact (proj1 Hperiodic).
  - now apply periodic_rsum.
Qed.

Lemma q_of_nat_succ_positive : forall n, 0 < q_of_nat (S n).
Proof. intro n. apply q_of_nat_positive_v. lia. Qed.

Lemma center_implies_positive_spanning : forall d (set : ZSet d) value,
    Periodic set -> Center set value ->
    PositiveSpanningCombination set value.
Proof.
  intros d set value Hperiodic Hcenter.
  destruct (finite_p_spanning d set Hperiodic) as
    [generators [Hgenerators Hspan]].
  set (sum := zvec_rsum generators).
  destruct (Hcenter (zvec_sub (zvec_zero d) sum)
    (zvec_neg_rsum_difference d set generators Hperiodic Hgenerators)) as
    [radius Htail].
  set (extra := zvec_add (zvec_sub (zvec_zero d) sum)
    (zvec_nsmul (S radius) value)).
  assert (Hextra : set extra).
  { unfold extra. replace (S radius) with (radius + 1)%nat by lia.
    apply Htail. }
  exists (extra :: generators). split.
  - constructor; assumption.
  - split.
    + intro point. rewrite Hspan.
      symmetry. apply qspan_cons_equiv. apply (proj1 (Hspan _)).
      exists [extra]. split; [constructor; [exact Hextra|constructor]|].
      apply qspan_member. now left.
    + set (coefficient := / q_of_nat (S radius)).
      exists (Vector.const coefficient (length (extra :: generators))).
      split.
      * apply vector_forall_const_positive. unfold coefficient.
        apply Qinv_lt_0_compat, q_of_nat_succ_positive.
      * eapply qvec_eq_trans with
          (y := qvec_scale coefficient
            (zvec_to_qvec (zvec_rsum (extra :: generators)))).
        -- intro index. unfold coefficient, extra, sum, qvec_scale,
             zvec_to_qvec, zvec_rsum, zvec_add, zvec_sub.
           repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
           unfold Z.sub. rewrite !inject_Z_plus, !inject_Z_opp, nth_zvec_nsmul,
             inject_Z_mult. unfold q_of_nat.
           rewrite Nat2Z.inj_succ.
           unfold zvec_zero. rewrite const_nth.
           field. unfold Qeq. cbn. lia.
        -- apply qvec_eq_sym, qgroup_combination_const.
Qed.

Fixpoint zvector_abs_sum {n} (values : Vector.t Z n) : nat :=
  match values with
  | @Vector.nil _ => 0%nat
  | @Vector.cons _ head n tail =>
      (Z.to_nat (Z.abs head) + zvector_abs_sum tail)%nat
  end.

Lemma zvector_abs_sum_bound : forall n (values : Vector.t Z n) index,
    (- Z.of_nat (zvector_abs_sum values) <= Vector.nth values index <=
      Z.of_nat (zvector_abs_sum values))%Z.
Proof.
  intros n values. induction values as [|head n tail IH]; intro index.
  - inversion index.
  - refine (Fin.caseS' index (fun index => _) _ _).
    + cbn. rewrite Nat2Z.inj_add, Z2Nat.id by apply Z.abs_nonneg.
      pose proof (proj1 (Z.abs_le head (Z.abs head)) (Z.le_refl _)).
      pose proof (Nat2Z.is_nonneg (zvector_abs_sum tail)). lia.
    + intro tail_index. cbn. rewrite Nat2Z.inj_add,
        Z2Nat.id by apply Z.abs_nonneg.
      specialize (IH tail_index). pose proof (Z.abs_nonneg head). lia.
Qed.

Lemma vector_forall_nth : forall A (predicate : A -> Prop) n
    (values : Vector.t A n),
    Vector.Forall predicate values ->
    forall index, predicate (Vector.nth values index).
Proof.
  intros A predicate n values Hvalues.
  apply (proj1 (Vector.Forall_nth A predicate n values)); exact Hvalues.
Qed.

Lemma qgroup_combination_coeff_ext : forall d
    (generators : list (ZVec d))
    (left right : Vector.t Q (length generators)),
    (forall index, Vector.nth left index == Vector.nth right index) ->
    QVecEq (qgroup_combination generators left)
      (qgroup_combination generators right).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros left right Heq.
  - intro index. reflexivity.
  - revert right Heq.
    refine (Vector.caseS' left (fun left => forall right,
      (forall index, Vector.nth left index == Vector.nth right index) ->
      QVecEq (qgroup_combination (generator :: generators) left)
        (qgroup_combination (generator :: generators) right)) _).
    intros left_head left_tail right.
    refine (Vector.caseS' right (fun right =>
      (forall index,
        Vector.nth (@Vector.cons Q left_head _ left_tail) index ==
        Vector.nth right index) ->
      QVecEq
        (qgroup_combination (generator :: generators)
          (@Vector.cons Q left_head _ left_tail))
        (qgroup_combination (generator :: generators) right)) _).
    intros right_head right_tail Hall.
    apply qvec_eq_add.
    + apply qvec_eq_scale; [apply (Hall Fin.F1)|apply qvec_eq_refl].
    + apply IH. intro index.
      apply (Hall (Fin.FS index)).
Qed.

Lemma zgroup_combination_nonnegative_generated : forall d
    (generators : list (ZVec d))
    (coefficients : Vector.t Z (length generators)),
    Vector.Forall (fun coefficient => (0 <= coefficient)%Z) coefficients ->
    zvec_generated generators (zgroup_combination generators coefficients).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hnonnegative.
  - refine (Vector.case0 (fun coefficients =>
      zvec_generated [] (zgroup_combination [] coefficients)) _ coefficients).
    exists (@Vector.nil nat). reflexivity.
  - revert Hnonnegative.
    refine (Vector.caseS' coefficients (fun coefficients =>
      Vector.Forall (fun coefficient => (0 <= coefficient)%Z) coefficients ->
      zvec_generated (generator :: generators)
        (zgroup_combination (generator :: generators) coefficients)) _).
    intros head tail Hnonnegative.
    assert (Hhead : (0 <= head)%Z).
    { exact (vector_forall_nth _ _ _ _ Hnonnegative Fin.F1). }
    assert (Htail : Vector.Forall
        (fun coefficient => (0 <= coefficient)%Z) tail).
    { apply (proj2 (Vector.Forall_nth _ _ _ _)). intro index.
      exact (vector_forall_nth _ _ _ _ Hnonnegative (Fin.FS index)). }
    destruct (IH tail Htail) as [natural_tail Hnatural_tail].
    exists (@Vector.cons nat (Z.to_nat head) _ natural_tail). cbn.
    rewrite <- zvec_zsmul_nat, Z2Nat.id by exact Hhead.
    change (zvec_add (zvec_zsmul head generator)
      (zvec_linear_combination generators (Vector.to_list natural_tail)) =
      zvec_add (zvec_zsmul head generator)
        (zgroup_combination generators tail)).
    now rewrite Hnatural_tail.
Qed.

Definition combined_integer_coefficients {n} (scale : nat)
    (positive offset : Vector.t Z n) : Vector.t Z n :=
  Vector.map2 (fun positive_coefficient offset_coefficient =>
    (Z.of_nat scale * positive_coefficient + offset_coefficient)%Z)
    positive offset.

Lemma cleared_positive_numerator : forall n
    (coefficients : Vector.t Q n) denominator numerator,
    (0 < denominator)%nat ->
    Vector.Forall (fun coefficient => 0 < coefficient) coefficients ->
    (forall index,
      inject_Z (Vector.nth numerator index) ==
        q_of_nat denominator * Vector.nth coefficients index) ->
    forall index, (1 <= Vector.nth numerator index)%Z.
Proof.
  intros n coefficients denominator numerator Hden Hpositive Hclear index.
  assert (Hqpositive : 0 < inject_Z (Vector.nth numerator index)).
  { setoid_rewrite (Hclear index).
    apply Qmult_lt_0_compat.
    - apply q_of_nat_positive_v. exact Hden.
    - now apply vector_forall_nth. }
  change (inject_Z 0 < inject_Z (Vector.nth numerator index)) in Hqpositive.
  rewrite <- Zlt_Qlt in Hqpositive. lia.
Qed.

Lemma combined_integer_coefficients_positive : forall n scale
    (positive offset : Vector.t Z n),
    scale = S (zvector_abs_sum offset) ->
    (forall index, (1 <= Vector.nth positive index)%Z) ->
    Vector.Forall (fun coefficient => (0 < coefficient)%Z)
      (combined_integer_coefficients scale positive offset).
Proof.
  intros n scale positive offset Hscale Hpositive.
  apply (proj2 (Vector.Forall_nth Z
    (fun coefficient => (0 < coefficient)%Z) n
    (combined_integer_coefficients scale positive offset))).
  intro index. unfold combined_integer_coefficients.
  rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl), Hscale.
  pose proof (zvector_abs_sum_bound n offset index) as Hbound.
  specialize (Hpositive index). rewrite Nat2Z.inj_succ. nia.
Qed.

Lemma combined_integer_coefficients_qeq : forall n scale
    (positive offset : Vector.t Z n)
    positive_denominator offset_denominator
    (positive_q offset_q : Vector.t Q n),
    (forall index,
      inject_Z (Vector.nth positive index) ==
        q_of_nat positive_denominator * Vector.nth positive_q index) ->
    (forall index,
      inject_Z (Vector.nth offset index) ==
        q_of_nat offset_denominator * Vector.nth offset_q index) ->
    forall index,
      inject_Z (Vector.nth
        (combined_integer_coefficients scale positive offset) index) ==
      q_of_nat (positive_denominator * scale) *
        Vector.nth positive_q index +
      q_of_nat offset_denominator * Vector.nth offset_q index.
Proof.
  intros n scale positive offset positive_denominator offset_denominator
    positive_q offset_q Hpositive Hoffset index.
  unfold combined_integer_coefficients.
  rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl),
    inject_Z_plus, inject_Z_mult.
  setoid_rewrite (Hpositive index). setoid_rewrite (Hoffset index).
  unfold q_of_nat. rewrite Nat2Z.inj_mul, inject_Z_mult. ring.
Qed.

Lemma qgroup_combination_scaled_sum : forall d
    (generators : list (ZVec d))
    (positive offset : Vector.t Q (length generators))
    positive_scale offset_scale,
    QVecEq
      (qgroup_combination generators
        (Vector.map2 Qplus
          (Vector.map (Qmult positive_scale) positive)
          (Vector.map (Qmult offset_scale) offset)))
      (qvec_add
        (qvec_scale positive_scale
          (qgroup_combination generators positive))
        (qvec_scale offset_scale
          (qgroup_combination generators offset))).
Proof.
  intros. eapply qvec_eq_trans.
  - apply qgroup_combination_add_q.
  - apply qvec_eq_add; apply qgroup_combination_scale_q.
Qed.

Lemma positive_combination_absorbs_span : forall d (set : ZSet d)
    (generators : list (ZVec d)) value offset,
    Periodic set -> List.Forall set generators ->
    (exists positive : Vector.t Q (length generators),
      Vector.Forall (fun coefficient => 0 < coefficient) positive /\
      QVecEq (zvec_to_qvec value)
        (qgroup_combination generators positive)) ->
    QSpan generators (zvec_to_qvec offset) ->
    exists radius offset_scale : nat,
      (0 < radius)%nat /\ (0 < offset_scale)%nat /\
      set (zvec_add (zvec_nsmul radius value)
        (zvec_nsmul offset_scale offset)).
Proof.
  intros d set generators value offset Hperiodic Hgenerators
    [positive [Hpositive Hvalue]] [offset_q Hoffset].
  destruct (qvector_clear_denominators (length generators) positive) as
    [positive_denominator [positive_integer [Hpositive_den Hpositive_clear]]].
  destruct (qvector_clear_denominators (length generators) offset_q) as
    [offset_denominator [offset_integer [Hoffset_den Hoffset_clear]]].
  set (scale := S (zvector_abs_sum offset_integer)).
  set (integer_coefficients := combined_integer_coefficients scale
    positive_integer offset_integer).
  assert (Hpositive_integer : forall index,
      (1 <= Vector.nth positive_integer index)%Z).
  { apply cleared_positive_numerator with
      (coefficients := positive) (denominator := positive_denominator);
      assumption. }
  assert (Hinteger_positive : Vector.Forall
      (fun coefficient => (0 < coefficient)%Z) integer_coefficients).
  { unfold integer_coefficients. apply combined_integer_coefficients_positive.
    - reflexivity.
    - exact Hpositive_integer. }
  assert (Hgenerated : zvec_generated generators
      (zgroup_combination generators integer_coefficients)).
  { apply zgroup_combination_nonnegative_generated.
    apply (proj2 (Vector.Forall_nth _ _ _ _)). intro index.
    apply Z.lt_le_incl.
    exact (vector_forall_nth Z (fun coefficient => (0 < coefficient)%Z)
      _ _ Hinteger_positive index). }
  assert (Hmember : set (zgroup_combination generators integer_coefficients)).
  { eapply generated_in_periodic; eauto.
    intros generator Hin.
    exact (proj1 (List.Forall_forall set generators) Hgenerators generator Hin). }
  exists (positive_denominator * scale)%nat, offset_denominator.
  repeat split.
  - unfold scale. nia.
  - exact Hoffset_den.
  - replace (zvec_add
      (zvec_nsmul (positive_denominator * scale) value)
      (zvec_nsmul offset_denominator offset))
      with (zgroup_combination generators integer_coefficients).
    + exact Hmember.
    + apply zvec_to_qvec_injective. apply qvec_eq_sym. eapply qvec_eq_trans.
      * apply zvec_to_qvec_add.
      * eapply qvec_eq_trans.
        -- apply qvec_eq_add; apply zvec_nsmul_to_qvec.
        -- eapply qvec_eq_trans.
           ++ apply qvec_eq_add.
              ** apply qvec_eq_scale; [reflexivity|exact Hvalue].
              ** apply qvec_eq_scale; [reflexivity|exact Hoffset].
           ++ eapply qvec_eq_trans.
              ** apply qvec_eq_sym, qgroup_combination_scaled_sum.
              ** eapply qvec_eq_trans with
                   (y := qgroup_combination generators
                     (Vector.map inject_Z integer_coefficients)).
                 --- apply qgroup_combination_coeff_ext. intro index.
                     rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl),
                       (nth_map _ _ index index eq_refl),
                       (nth_map _ _ index index eq_refl),
                       (nth_map _ _ index index eq_refl).
                     symmetry. apply combined_integer_coefficients_qeq;
                       assumption.
                 --- apply qgroup_combination_inject.
Qed.

Lemma vecof_neg_add : forall d (set : ZSet d) left right,
    set left -> set right ->
    VecOf set
      (zvec_to_qvec (zvec_sub (zvec_zero d) (zvec_add left right))).
Proof.
  intros d set left right Hleft Hright.
  exists [left; right]. split.
  - repeat constructor; assumption.
  - exists (@Vector.cons Q (-1) 1
      (@Vector.cons Q (-1) 0 (@Vector.nil Q))).
    intro index. unfold zvec_to_qvec, zvec_sub, zvec_add, zvec_zero.
    repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
    unfold Z.sub. rewrite const_nth, !inject_Z_plus, !inject_Z_opp.
    cbn [qgroup_combination].
    unfold qvec_add, qvec_scale, qvec_zero, zvec_to_qvec. cbn.
    rewrite inject_Z_plus. ring.
Qed.

Lemma absorbed_translate_memberships : forall d (set : ZSet d)
    radius scale (value left right : ZVec d),
    Periodic set -> (0 < scale)%nat -> set left -> set right ->
    set (zvec_add (zvec_nsmul radius value)
      (zvec_nsmul scale
        (zvec_sub (zvec_zero d) (zvec_add left right)))) ->
    set (zvec_nsmul radius value) /\
    set (zvec_sub (zvec_nsmul radius value) left) /\
    set (zvec_sub (zvec_nsmul radius value) right).
Proof.
  intros d set radius scale value left right Hperiodic Hscale
    Hleft Hright Habsorbed.
  destruct scale as [|scale]; [lia|].
  assert (Hscale_left : set (zvec_nsmul scale left)).
  { now apply periodic_nsmul with (set := set). }
  assert (Hscale_right : set (zvec_nsmul scale right)).
  { now apply periodic_nsmul with (set := set). }
  assert (Hsucc_left : set (zvec_nsmul (S scale) left)).
  { now apply periodic_nsmul with (set := set). }
  assert (Hsucc_right : set (zvec_nsmul (S scale) right)).
  { now apply periodic_nsmul with (set := set). }
  split.
  - replace (zvec_nsmul radius value) with
      (zvec_add
        (zvec_add
          (zvec_add (zvec_nsmul radius value)
            (zvec_nsmul (S scale)
              (zvec_sub (zvec_zero d) (zvec_add left right))))
          (zvec_nsmul (S scale) left))
        (zvec_nsmul (S scale) right)).
    + apply (proj2 Hperiodic); [|exact Hsucc_right].
      apply (proj2 Hperiodic); assumption.
    + apply zvec_ext. intro index.
      unfold zvec_add, zvec_sub, zvec_zero.
      repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
      repeat rewrite nth_zvec_nsmul.
      repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
      rewrite const_nth, Nat2Z.inj_succ. ring.
  - split.
    + replace (zvec_sub (zvec_nsmul radius value) left) with
        (zvec_add
          (zvec_add
            (zvec_add (zvec_nsmul radius value)
              (zvec_nsmul (S scale)
                (zvec_sub (zvec_zero d) (zvec_add left right))))
            (zvec_nsmul scale left))
          (zvec_nsmul (S scale) right)).
      * apply (proj2 Hperiodic); [|exact Hsucc_right].
        apply (proj2 Hperiodic); assumption.
      * apply zvec_ext. intro index.
        unfold zvec_add, zvec_sub, zvec_zero.
        repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
        repeat rewrite nth_zvec_nsmul.
        repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
        rewrite const_nth, Nat2Z.inj_succ. ring.
    + replace (zvec_sub (zvec_nsmul radius value) right) with
        (zvec_add
          (zvec_add
            (zvec_add (zvec_nsmul radius value)
              (zvec_nsmul (S scale)
                (zvec_sub (zvec_zero d) (zvec_add left right))))
            (zvec_nsmul (S scale) left))
          (zvec_nsmul scale right)).
      * apply (proj2 Hperiodic); [|exact Hscale_right].
        apply (proj2 Hperiodic); assumption.
      * apply zvec_ext. intro index.
        unfold zvec_add, zvec_sub, zvec_zero.
        repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
        repeat rewrite nth_zvec_nsmul.
        repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
        rewrite const_nth, Nat2Z.inj_succ. ring.
Qed.

Lemma periodic_tail_from_blocks : forall d (set : ZSet d)
    radius (offset value left right : ZVec d),
    Periodic set -> (0 < radius)%nat ->
    set (zvec_add offset left) ->
    set (zvec_add value right) ->
    set (zvec_nsmul radius value) ->
    set (zvec_sub (zvec_nsmul radius value) left) ->
    set (zvec_sub (zvec_nsmul radius value) right) ->
    forall n, (radius * radius + radius <= n)%nat ->
      set (zvec_add offset (zvec_nsmul n value)).
Proof.
  intros d set radius offset value left right Hperiodic Hradius
    Hoffset_left Hvalue_right Hblock Hblock_left Hblock_right n Hn.
  set (quotient := (n / radius)%nat).
  set (remainder := (n mod radius)%nat).
  assert (Hradius_nonzero : radius <> 0%nat) by lia.
  assert (Hdecompose : n = (radius * quotient + remainder)%nat).
  { unfold quotient, remainder. apply Nat.div_mod. exact Hradius_nonzero. }
  assert (Hremainder : (remainder < radius)%nat).
  { unfold remainder. apply Nat.mod_upper_bound. exact Hradius_nonzero. }
  assert (Hquotient : (remainder + 1 <= quotient)%nat).
  { assert (Hlower : (radius + 1 <= quotient)%nat).
    { unfold quotient. apply Nat.div_le_lower_bound; [exact Hradius_nonzero|].
      nia. }
    lia. }
  assert (Hremainder_value :
      set (zvec_nsmul remainder (zvec_add value right))).
  { now apply periodic_nsmul with (set := set). }
  assert (Hremainder_block : set
      (zvec_nsmul remainder
        (zvec_sub (zvec_nsmul radius value) right))).
  { now apply periodic_nsmul with (set := set). }
  assert (Hremaining_blocks : set
      (zvec_nsmul (quotient - remainder - 1) (zvec_nsmul radius value))).
  { now apply periodic_nsmul with (set := set). }
  replace (zvec_add offset (zvec_nsmul n value)) with
    (zvec_add
      (zvec_add
        (zvec_add
          (zvec_add (zvec_add offset left)
            (zvec_nsmul remainder (zvec_add value right)))
          (zvec_sub (zvec_nsmul radius value) left))
        (zvec_nsmul remainder
          (zvec_sub (zvec_nsmul radius value) right)))
      (zvec_nsmul (quotient - remainder - 1)
        (zvec_nsmul radius value))).
  - apply (proj2 Hperiodic).
    + apply (proj2 Hperiodic).
      * apply (proj2 Hperiodic).
        -- apply (proj2 Hperiodic); assumption.
        -- exact Hblock_left.
      * exact Hremainder_block.
    + exact Hremaining_blocks.
  - apply zvec_ext. intro index.
    unfold zvec_add, zvec_sub.
    repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
    repeat rewrite nth_zvec_nsmul.
    repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
    repeat rewrite nth_zvec_nsmul.
    rewrite !Nat2Z.inj_sub by lia.
    assert (Hdecompose_Z :
        Z.of_nat n = (Z.of_nat radius * Z.of_nat quotient +
          Z.of_nat remainder)%Z).
    { rewrite Hdecompose, Nat2Z.inj_add, Nat2Z.inj_mul. reflexivity. }
    nia.
Qed.

Theorem positive_spanning_implies_center : forall d (set : ZSet d) value,
    Periodic set -> Difference set value ->
    PositiveSpanningCombination set value -> Center set value.
Proof.
  intros d set value Hperiodic Hvalue_difference
    [generators [Hgenerators [Hspan
      [positive [Hpositive Hvalue_combination]]]]] offset Hoffset.
  destruct Hoffset as
    [offset_left [offset_right
      [Hoffset_left_member [Hoffset_right_member Hoffset]]]].
  destruct Hvalue_difference as
    [value_left [value_right
      [Hvalue_left_member [Hvalue_right_member Hvalue]]]].
  subst offset value.
  assert (Hoffset_ready :
      set (zvec_add (zvec_sub offset_left offset_right) offset_right)).
  { rewrite zvec_add_comm, zvec_sub_add_cancel. exact Hoffset_left_member. }
  assert (Hvalue_ready :
      set (zvec_add (zvec_sub value_left value_right) value_right)).
  { rewrite zvec_add_comm, zvec_sub_add_cancel. exact Hvalue_left_member. }
  assert (Hnegative_span : QSpan generators
      (zvec_to_qvec
        (zvec_sub (zvec_zero d)
          (zvec_add offset_right value_right)))).
  { apply (proj1 (Hspan _)).
    apply vecof_neg_add; assumption. }
  destruct (positive_combination_absorbs_span d set generators
    (zvec_sub value_left value_right)
    (zvec_sub (zvec_zero d) (zvec_add offset_right value_right))
    Hperiodic Hgenerators) as
    [radius [scale [Hradius [Hscale Habsorbed]]]].
  - exists positive. split; assumption.
  - exact Hnegative_span.
  - destruct (absorbed_translate_memberships d set radius scale
      (zvec_sub value_left value_right) offset_right value_right
      Hperiodic Hscale Hoffset_right_member Hvalue_right_member Habsorbed) as
      [Hblock [Hblock_offset Hblock_value]].
    exists (radius * radius + radius)%nat. intro n.
    apply periodic_tail_from_blocks with
      (radius := radius) (left := offset_right) (right := value_right);
      try assumption.
    lia.
Qed.

Theorem center_characterization : forall d (set : ZSet d) value,
    Periodic set ->
    (Center set value <->
      Difference set value /\ PositiveSpanningCombination set value).
Proof.
  intros d set value Hperiodic. split.
  - intro Hcenter. split.
    + now apply center_in_difference with (set := set).
    + now apply center_implies_positive_spanning.
  - intros [Hdifference Hpositive].
    now apply positive_spanning_implies_center.
Qed.
