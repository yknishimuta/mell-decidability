From Coq Require Import Classical_Prop Fin Lia List Lra QArith QArith.Qabs
  QArith.Qround Qring Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge Periodic QConeCore RationalHToV.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Lemma zvec_to_qvec_injective : forall d (x y : ZVec d),
    QVecEq (zvec_to_qvec x) (zvec_to_qvec y) -> x = y.
Proof.
  intros d x y H. apply zvec_ext. intro index.
  apply inject_Z_injective. apply H.
Qed.

Definition IntegerScaling {d} (q : QVec d) (z : ZVec d) : Prop :=
  exists denominator : nat, (0 < denominator)%nat /\
    QVecEq q (qvec_scale (/ q_of_nat denominator) (zvec_to_qvec z)).

Lemma q_of_nat_positive_v : forall value,
    (0 < value)%nat -> 0 < q_of_nat value.
Proof. intros value H. unfold q_of_nat, Qlt; cbn; lia. Qed.

Inductive IntegerizedList {d} : list (QVec d) -> list (ZVec d) -> Prop :=
| integerized_nil : IntegerizedList [] []
| integerized_cons : forall q z qs zs,
    IntegerScaling q z -> IntegerizedList qs zs ->
    IntegerizedList (q :: qs) (z :: zs).

Lemma integerized_list_exists : forall d (values : list (QVec d)),
    exists integers, IntegerizedList values integers.
Proof.
  intros d values. induction values as [|value values [integers HI]].
  - exists []; constructor.
  - destruct (qvec_clear_denominators d value) as
      [denominator [numerator [Hpositive Hscale]]].
    exists (numerator :: integers). constructor; [|exact HI].
    exists denominator. auto.
Qed.

Lemma integer_scaling_forward : forall d (q : QVec d) (z : ZVec d) coefficient,
    IntegerScaling q z -> 0 <= coefficient ->
    exists scaled, 0 <= scaled /\
      QVecEq (qvec_scale coefficient q)
        (qvec_scale scaled (zvec_to_qvec z)).
Proof.
  intros d q z coefficient [denominator [Hden Hq]] Hcoefficient.
  exists (coefficient / q_of_nat denominator). split.
  - apply Qmult_le_0_compat; [exact Hcoefficient|].
    apply Qlt_le_weak, Qinv_lt_0_compat, q_of_nat_positive_v. exact Hden.
  - intro index. unfold qvec_scale in *. specialize (Hq index).
    setoid_rewrite Hq. unfold Qdiv. ring.
Qed.

Lemma integer_scaling_backward : forall d (q : QVec d) (z : ZVec d) coefficient,
    IntegerScaling q z -> 0 <= coefficient ->
    exists scaled, 0 <= scaled /\
      QVecEq (qvec_scale coefficient (zvec_to_qvec z))
        (qvec_scale scaled q).
Proof.
  intros d q z coefficient [denominator [Hden Hq]] Hcoefficient.
  exists (coefficient * q_of_nat denominator). split.
  - apply Qmult_le_0_compat; [exact Hcoefficient|].
    apply Qlt_le_weak, q_of_nat_positive_v. exact Hden.
  - intro index. unfold qvec_scale in *. specialize (Hq index).
    assert (Hnonzero : ~ q_of_nat denominator == 0).
    { apply q_of_nat_nonzero_hl. exact Hden. }
    transitivity
      (coefficient * (q_of_nat denominator * q index)).
    + apply Qmult_comp; [reflexivity|].
      symmetry.
      transitivity (q_of_nat denominator *
        (/ q_of_nat denominator * zvec_to_qvec z index)).
      * apply Qmult_comp; [reflexivity|exact Hq].
      * field. exact Hnonzero.
    + ring.
Qed.

Lemma integerized_lookup_left : forall d (qs : list (QVec d))
    (zs : list (ZVec d)) (q : QVec d),
    IntegerizedList qs zs -> List.In q qs ->
    exists z, List.In z zs /\ IntegerScaling q z.
Proof.
  intros d qs zs q HI. revert q. induction HI; intros target Hin.
  - contradiction.
  - destruct Hin as [Heq|Htail].
    + exists z. split; [now left|]. now destruct Heq.
    + destruct (IHHI _ Htail) as [z' [Hin' Hz']].
      exists z'. split; [now right|exact Hz'].
Qed.

Lemma integerized_lookup_right : forall d (qs : list (QVec d))
    (zs : list (ZVec d)) (z : ZVec d),
    IntegerizedList qs zs -> List.In z zs ->
    exists q, List.In q qs /\ IntegerScaling q z.
Proof.
  intros d qs zs z HI. revert z. induction HI; intros target Hin.
  - contradiction.
  - destruct Hin as [Heq|Htail].
    + exists q. split; [now left|]. now destruct Heq.
    + destruct (IHHI _ Htail) as [q' [Hin' Hq']].
      exists q'. split; [now right|exact Hq'].
Qed.

Lemma integerized_combination_forward : forall d (qs : list (QVec d))
    (zs : list (ZVec d)) (generated : QVec d),
    IntegerizedList qs zs -> QConeCombination qs generated ->
    exists generated',
      QConeCombination (List.map zvec_to_qvec zs) generated' /\
      QVecEq generated generated'.
Proof.
  intros d qs zs generated HI Hcomb. revert zs HI.
  induction Hcomb; intros zs HI.
  - exists (qvec_zero d). split; [constructor|apply qvec_eq_refl].
  - destruct (integerized_lookup_left d qs zs generator HI H0)
      as [z [Hzin Hscale]].
    destruct (integer_scaling_forward d generator z coefficient Hscale H)
      as [scaled [Hscaled Heqscale]].
    destruct (IHHcomb zs HI) as [tail' [Htail' Heqtail]].
    exists (qvec_add (qvec_scale scaled (zvec_to_qvec z)) tail'). split.
    + constructor; [exact Hscaled|apply in_map; exact Hzin|exact Htail'].
    + apply qvec_eq_add; assumption.
Qed.

Lemma integerized_combination_backward : forall d (qs : list (QVec d))
    (zs : list (ZVec d)) (generated : QVec d),
    IntegerizedList qs zs ->
    QConeCombination (List.map zvec_to_qvec zs) generated ->
    exists generated', QConeCombination qs generated' /\
      QVecEq generated generated'.
Proof.
  intros d qs zs generated HI Hcomb.
  remember (List.map zvec_to_qvec zs) as mapped eqn:Hmapped.
  revert qs zs HI Hmapped.
  induction Hcomb; intros qs zs HI Hmapped; subst mapped.
  - exists (qvec_zero d). split; [constructor|apply qvec_eq_refl].
  - apply in_map_iff in H0. destruct H0 as [z [<- Hzin]].
    destruct (integerized_lookup_right d qs zs z HI Hzin)
      as [q [Hqin Hscale]].
    destruct (integer_scaling_backward d q z coefficient Hscale H)
      as [scaled [Hscaled Heqscale]].
    destruct (IHHcomb qs zs HI eq_refl) as [tail' [Htail' Heqtail]].
    exists (qvec_add (qvec_scale scaled q) tail'). split.
    + constructor; assumption.
    + apply qvec_eq_add; assumption.
Qed.

Lemma integerized_cone_forward : forall d (qs : list (QVec d))
    (zs : list (ZVec d)),
    IntegerizedList qs zs -> forall value,
    qcone_generated qs value ->
    qcone_generated (List.map zvec_to_qvec zs) value.
Proof.
  intros d qs zs HI value [generated [Hcomb Heq]].
  destruct (integerized_combination_forward d qs zs generated HI Hcomb)
    as [generated' [Hgenerated' Hgenerated]].
  exists generated'. split; [exact Hgenerated'|].
  eapply qvec_eq_trans; eauto.
Qed.

Lemma integerized_cone_backward : forall d (qs : list (QVec d))
    (zs : list (ZVec d)),
    IntegerizedList qs zs -> forall value,
    qcone_generated (List.map zvec_to_qvec zs) value ->
    qcone_generated qs value.
Proof.
  intros d qs zs HI value [generated [Hcomb Heq]].
  destruct (integerized_combination_backward d qs zs generated HI Hcomb)
    as [generated' [Hgenerated' Hgenerated]].
  exists generated'. split; [exact Hgenerated'|].
  eapply qvec_eq_trans; eauto.
Qed.

Theorem integerize_vcone : forall d (values : list (QVec d)),
    exists integers : list (ZVec d),
      SameSet (qcone_generated values)
        (qcone_generated (List.map zvec_to_qvec integers)).
Proof.
  intros d values. destruct (integerized_list_exists d values) as [zs HI].
  exists zs. intro value. split.
  - apply integerized_cone_forward with (qs := values); exact HI.
  - apply integerized_cone_backward with (zs := zs); exact HI.
Qed.

Fixpoint qlinear_combination {d} (generators : list (QVec d))
    (coefficients : list Q) : QVec d :=
  match generators, coefficients with
  | generator :: generators', coefficient :: coefficients' =>
      qvec_add (qvec_scale coefficient generator)
        (qlinear_combination generators' coefficients')
  | _, _ => qvec_zero d
  end.

Lemma qlinear_combination_zeros : forall d (generators : list (QVec d)),
    QVecEq (qlinear_combination generators (repeat 0 (length generators)))
      (qvec_zero d).
Proof.
  intros d generators. induction generators as [|generator generators IH].
  - apply qvec_eq_refl.
  - cbn. intro index. unfold qvec_add, qvec_scale, qvec_zero in *.
    specialize (IH index). setoid_rewrite IH. ring.
Qed.

Lemma qcone_generated_cons : forall d (head : QVec d) generators value,
    qcone_generated generators value ->
    qcone_generated (head :: generators) value.
Proof.
  intros d head generators value [generated [Hgenerated Heq]].
  exists generated. split.
  - clear value Heq. induction Hgenerated.
    + constructor.
    + constructor; [exact H|now right|exact IHHgenerated].
  - exact Heq.
Qed.

Lemma qlinear_add_at : forall d (generators : list (QVec d))
    (generator : QVec d) coefficient coefficients,
    List.In generator generators -> 0 <= coefficient ->
    length coefficients = length generators ->
    List.Forall (fun q => 0 <= q) coefficients ->
    exists coefficients',
      length coefficients' = length generators /\
      List.Forall (fun q => 0 <= q) coefficients' /\
      QVecEq (qlinear_combination generators coefficients')
        (qvec_add (qvec_scale coefficient generator)
          (qlinear_combination generators coefficients)).
Proof.
  intros d generators. induction generators as [|head generators IH];
    intros generator coefficient coefficients Hin Hcoefficient Hlength Hnonnegative.
  - contradiction.
  - destruct coefficients as [|head_coefficient coefficients];
      [discriminate|].
    inversion Hnonnegative as [|? ? Hhead Htail]; subst.
    cbn in Hlength. injection Hlength as Hlength.
    destruct Hin as [Hequal|Hin].
    + subst generator. exists ((coefficient + head_coefficient) :: coefficients).
      split; [cbn; congruence|]. split.
      * constructor; [|exact Htail].
        setoid_replace 0 with (0 + 0) by ring.
        now apply Qplus_le_compat.
      * intro index. cbn. unfold qvec_add, qvec_scale.
        ring.
    + destruct (IH generator coefficient coefficients Hin Hcoefficient
        Hlength Htail) as [coefficients' [Hlength' [Hnonnegative' Heq]]].
      exists (head_coefficient :: coefficients'). split.
      * cbn. congruence.
      * split; [constructor; assumption|].
        intro index. cbn. unfold qvec_add, qvec_scale in *.
        specialize (Heq index). setoid_rewrite Heq. ring.
Qed.

Lemma qlinear_combination_cone : forall d (generators : list (QVec d))
    coefficients,
    length coefficients = length generators ->
    List.Forall (fun q => 0 <= q) coefficients ->
    qcone_generated generators (qlinear_combination generators coefficients).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength Hnonnegative.
  - destruct coefficients; [apply qcone_generated_zero|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    inversion Hnonnegative as [|? ? Hcoefficient Hcoefficients]; subst.
    cbn in Hlength. injection Hlength as Hlength. cbn.
    apply qcone_generated_add.
    + apply qcone_generated_scale; [exact Hcoefficient|].
      apply qcone_generated_generator. now left.
    + apply qcone_generated_cons. apply IH; assumption.
Qed.

Lemma qcone_combination_aligned_coefficients :
  forall k (W : list (QVec k)) (x : QVec k),
    QConeCombination W x ->
    exists coefficients : list Q,
      length coefficients = length W /\
      List.Forall (fun q => 0 <= q) coefficients /\
      QVecEq x (qlinear_combination W coefficients).
Proof.
  intros k W x Hcombination. induction Hcombination.
  - exists (repeat 0 (length W)). repeat split.
    + apply repeat_length.
    + apply List.Forall_forall. intros q Hin.
      apply repeat_spec in Hin. subst q. unfold Qle; cbn; lia.
    + apply qvec_eq_sym, qlinear_combination_zeros.
  - destruct IHHcombination as
      [coefficients [Hlength [Hnonnegative Htail]]].
    destruct (qlinear_add_at k W generator coefficient coefficients H0 H
      Hlength Hnonnegative) as
      [coefficients' [Hlength' [Hnonnegative' Hcombined]]].
    exists coefficients'. repeat split; try assumption.
    eapply qvec_eq_trans.
    + apply qvec_eq_add; [apply qvec_eq_refl|exact Htail].
    + apply qvec_eq_sym. exact Hcombined.
Qed.

Theorem qcone_generated_aligned_coefficients :
  forall k (W : list (QVec k)) (x : QVec k),
    qcone_generated W x <->
    exists coefficients : list Q,
      length coefficients = length W /\
      List.Forall (fun q => 0 <= q) coefficients /\
      QVecEq x (qlinear_combination W coefficients).
Proof.
  intros k W x. split.
  - intros [generated [Hgenerated Hx]].
    destruct (qcone_combination_aligned_coefficients k W generated Hgenerated)
      as [coefficients [Hlength [Hnonnegative Hgenerated']]].
    exists coefficients. repeat split; try assumption.
    eapply qvec_eq_trans; eauto.
  - intros [coefficients [Hlength [Hnonnegative Heq]]].
    apply (proj2 (qcone_generated_qvec_ext k W _ _ Heq)).
    apply qlinear_combination_cone; assumption.
Qed.

Definition qfloor_nat (q : Q) : nat := Z.to_nat (Qfloor q).
Definition qfraction (q : Q) : Q := q - inject_Z (Qfloor q).

Lemma qfloor_nonnegative : forall q, 0 <= q -> (0 <= Qfloor q)%Z.
Proof.
  intros q Hq. destruct (Z_le_gt_dec 0 (Qfloor q)) as [H|H]; [exact H|].
  exfalso.
  assert (Hnext : (Qfloor q + 1 <= 0)%Z) by lia.
  rewrite Zle_Qle in Hnext.
  apply (Qlt_not_le q 0); [eapply Qlt_le_trans; [apply Qlt_floor|exact Hnext]|exact Hq].
Qed.

Lemma q_of_nat_qfloor : forall q, 0 <= q ->
    q_of_nat (qfloor_nat q) == inject_Z (Qfloor q).
Proof.
  intros q Hq. unfold qfloor_nat, q_of_nat.
  rewrite Z2Nat.id by now apply qfloor_nonnegative. reflexivity.
Qed.

Lemma qfraction_bounds : forall q, 0 <= q ->
    0 <= qfraction q /\ qfraction q < 1.
Proof.
  intros q Hq. unfold qfraction. split.
  - apply (proj1 (Qplus_le_l 0 (q - inject_Z (Qfloor q))
      (inject_Z (Qfloor q)))).
    setoid_replace (0 + inject_Z (Qfloor q))
      with (inject_Z (Qfloor q)) by ring.
    setoid_replace ((q - inject_Z (Qfloor q)) + inject_Z (Qfloor q))
      with q by ring. apply Qfloor_le.
  - apply (proj1 (Qplus_lt_l (q - inject_Z (Qfloor q)) 1
      (inject_Z (Qfloor q)))).
    setoid_replace ((q - inject_Z (Qfloor q)) + inject_Z (Qfloor q))
      with q by ring.
    setoid_replace (1 + inject_Z (Qfloor q))
      with (inject_Z (Qfloor q + 1)) by
      (rewrite inject_Z_plus; cbn; ring).
    apply Qlt_floor.
Qed.

Lemma qfloor_fraction_decompose : forall q, 0 <= q ->
    q == q_of_nat (qfloor_nat q) + qfraction q.
Proof.
  intros q Hq. unfold qfraction.
  setoid_rewrite (q_of_nat_qfloor q Hq). ring.
Qed.

Definition floor_coefficients (coefficients : list Q) : list nat :=
  List.map qfloor_nat coefficients.

Definition fraction_coefficients (coefficients : list Q) : list Q :=
  List.map qfraction coefficients.

Lemma fraction_coefficients_nonnegative : forall coefficients,
    List.Forall (fun q => 0 <= q) coefficients ->
    List.Forall (fun q => 0 <= q /\ q < 1)
      (fraction_coefficients coefficients).
Proof.
  intros coefficients H. induction H; cbn; constructor; auto.
  now apply qfraction_bounds.
Qed.

Lemma qlinear_combination_floor_fraction : forall d
    (generators : list (QVec d)) coefficients,
    length coefficients = length generators ->
    List.Forall (fun q => 0 <= q) coefficients ->
    QVecEq (qlinear_combination generators coefficients)
      (qvec_add
        (qlinear_combination generators
          (List.map q_of_nat (floor_coefficients coefficients)))
        (qlinear_combination generators
          (fraction_coefficients coefficients))).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength Hnonnegative.
  - destruct coefficients; [intro index; cbn; unfold qvec_add, qvec_zero; ring|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    inversion Hnonnegative as [|? ? Hcoefficient Hcoefficients]; subst.
    cbn in Hlength. injection Hlength as Hlength. cbn.
    intro index. unfold qvec_add, qvec_scale.
    specialize (IH coefficients Hlength Hcoefficients index).
    transitivity
      ((q_of_nat (qfloor_nat coefficient) + qfraction coefficient) *
        generator index +
       (qlinear_combination generators
          (List.map q_of_nat (floor_coefficients coefficients)) index +
        qlinear_combination generators
          (fraction_coefficients coefficients) index)).
    + apply Qplus_comp.
      * apply Qmult_comp; [apply qfloor_fraction_decompose; exact Hcoefficient|reflexivity].
      * exact IH.
    + unfold floor_coefficients, fraction_coefficients. ring.
Qed.

Lemma zvec_nsmul_to_qvec : forall d coefficient (value : ZVec d),
    QVecEq (zvec_to_qvec (zvec_nsmul coefficient value))
      (qvec_scale (q_of_nat coefficient) (zvec_to_qvec value)).
Proof.
  intros d coefficient value index.
  unfold zvec_to_qvec, qvec_scale, q_of_nat.
  rewrite nth_zvec_nsmul, inject_Z_mult. reflexivity.
Qed.

Lemma zlinear_combination_to_qvec : forall d
    (generators : list (ZVec d)) coefficients,
    length coefficients = length generators ->
    QVecEq (zvec_to_qvec (zvec_linear_combination generators coefficients))
      (qlinear_combination (List.map zvec_to_qvec generators)
        (List.map q_of_nat coefficients)).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength.
  - destruct coefficients; [intro index; cbn; unfold zvec_to_qvec, qvec_zero, zvec_zero;
      rewrite const_nth; reflexivity|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength. cbn.
    eapply qvec_eq_trans; [apply zvec_to_qvec_add|].
    apply qvec_eq_add.
    + apply zvec_nsmul_to_qvec.
    + apply IH. exact Hlength.
Qed.

Lemma zvec_to_qvec_sub : forall d (left right : ZVec d),
    QVecEq (zvec_to_qvec (zvec_sub left right))
      (fun index => zvec_to_qvec left index - zvec_to_qvec right index).
Proof.
  intros d left right index. unfold zvec_to_qvec, zvec_sub.
  rewrite (nth_map2 Z.sub left right index index index eq_refl eq_refl).
  unfold Z.sub, Qminus. rewrite inject_Z_plus, inject_Z_opp. reflexivity.
Qed.

Definition integer_part {d} (generators : list (ZVec d))
    (coefficients : list Q) : ZVec d :=
  zvec_linear_combination generators (floor_coefficients coefficients).

Definition integer_remainder {d} (point : ZVec d)
    (generators : list (ZVec d)) (coefficients : list Q) : ZVec d :=
  zvec_sub point (integer_part generators coefficients).

Lemma integer_remainder_correct : forall d (generators : list (ZVec d))
    coefficients point,
    length coefficients = length generators ->
    List.Forall (fun q => 0 <= q) coefficients ->
    QVecEq (zvec_to_qvec point)
      (qlinear_combination (List.map zvec_to_qvec generators) coefficients) ->
    QVecEq (zvec_to_qvec (integer_remainder point generators coefficients))
      (qlinear_combination (List.map zvec_to_qvec generators)
        (fraction_coefficients coefficients)).
Proof.
  intros d generators coefficients point Hlength Hnonnegative Hpoint.
  unfold integer_remainder, integer_part.
  eapply qvec_eq_trans; [apply zvec_to_qvec_sub|]. intro index.
  pose proof (qlinear_combination_floor_fraction d
    (List.map zvec_to_qvec generators) coefficients) as Hsplit.
  rewrite length_map in Hsplit.
  specialize (Hsplit Hlength Hnonnegative index).
  pose proof (zlinear_combination_to_qvec d generators
    (floor_coefficients coefficients)) as Hinteger.
  assert (Hfloorlength : length (floor_coefficients coefficients) =
      length generators).
  { unfold floor_coefficients. rewrite length_map. exact Hlength. }
  specialize (Hinteger Hfloorlength index).
  specialize (Hpoint index).
  unfold qvec_add in Hsplit. unfold zvec_to_qvec at 1 2.
  transitivity
    (qlinear_combination (List.map zvec_to_qvec generators) coefficients index -
      qlinear_combination (List.map zvec_to_qvec generators)
        (List.map q_of_nat (floor_coefficients coefficients)) index).
  - apply Qplus_comp; [exact Hpoint|].
    apply Qopp_comp. exact Hinteger.
  - transitivity
      ((qlinear_combination (List.map zvec_to_qvec generators)
          (List.map q_of_nat (floor_coefficients coefficients)) index +
        qlinear_combination (List.map zvec_to_qvec generators)
          (fraction_coefficients coefficients) index) -
       qlinear_combination (List.map zvec_to_qvec generators)
          (List.map q_of_nat (floor_coefficients coefficients)) index).
    + apply Qplus_comp; [exact Hsplit|reflexivity].
    + ring.
Qed.

Definition zcoordinate_bound {d} (generators : list (ZVec d))
    (index : Fin.t d) : Z :=
  List.fold_right Z.add 0%Z (List.map (fun generator =>
    Z.abs (Vector.nth generator index)) generators).

Lemma qabs_inject_Z : forall z,
    Qabs (inject_Z z) == inject_Z (Z.abs z).
Proof.
  intro z. destruct (Z_le_gt_dec 0 z) as [Hnonnegative|Hnegative].
  - transitivity (inject_Z z).
    + apply Qabs_pos. change (inject_Z 0 <= inject_Z z).
      rewrite <- Zle_Qle. exact Hnonnegative.
    + rewrite Z.abs_eq by exact Hnonnegative. reflexivity.
  - assert (Hz : (z <= 0)%Z) by lia.
    transitivity (- inject_Z z).
    + apply Qabs_neg. change (inject_Z z <= inject_Z 0).
      rewrite <- Zle_Qle. exact Hz.
    + rewrite Z.abs_neq by exact Hz. rewrite inject_Z_opp. reflexivity.
Qed.

Lemma qlinear_fraction_coordinate_bound : forall d
    (generators : list (ZVec d)) coefficients index,
    length coefficients = length generators ->
    List.Forall (fun q => 0 <= q /\ q < 1) coefficients ->
    Qabs (qlinear_combination (List.map zvec_to_qvec generators)
      coefficients index) <= inject_Z (zcoordinate_bound generators index).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients index Hlength Hbounds.
  - destruct coefficients;
      [cbn; unfold qvec_zero, Qabs, Qle; cbn; lia|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    inversion Hbounds as [|? ? [Hnonnegative Hlt] Htail]; subst.
    cbn in Hlength. injection Hlength as Hlength.
    change
      (Qabs (coefficient * inject_Z (Vector.nth generator index) +
        qlinear_combination (List.map zvec_to_qvec generators)
          coefficients index) <=
       inject_Z (Z.abs (Vector.nth generator index) +
         zcoordinate_bound generators index)).
    eapply Qle_trans; [apply Qabs_triangle|].
    rewrite inject_Z_plus.
    apply Qplus_le_compat.
    + setoid_rewrite Qabs_Qmult.
      setoid_rewrite (Qabs_pos coefficient Hnonnegative).
      setoid_rewrite qabs_inject_Z.
      eapply Qle_trans.
      * apply Qmult_le_compat_r.
        -- apply Qlt_le_weak. exact Hlt.
        -- change (inject_Z 0 <=
             inject_Z (Z.abs (Vector.nth generator index))).
           rewrite <- Zle_Qle. apply Z.abs_nonneg.
      * setoid_replace (1 * inject_Z (Z.abs (Vector.nth generator index)))
          with (inject_Z (Z.abs (Vector.nth generator index))) by ring.
        apply Qle_refl.
    + apply IH; assumption.
Qed.

Lemma integer_remainder_coordinate_bound : forall d
    (generators : list (ZVec d)) coefficients point,
    length coefficients = length generators ->
    List.Forall (fun q => 0 <= q) coefficients ->
    QVecEq (zvec_to_qvec point)
      (qlinear_combination (List.map zvec_to_qvec generators) coefficients) ->
    forall index,
      (Z.abs (Vector.nth (integer_remainder point generators coefficients) index)
        <= zcoordinate_bound generators index)%Z.
Proof.
  intros d generators coefficients point Hlength Hnonnegative Hpoint index.
  rewrite Zle_Qle. rewrite <- qabs_inject_Z.
  pose proof (integer_remainder_correct d generators coefficients point
    Hlength Hnonnegative Hpoint index) as Heq.
  setoid_rewrite (Qabs_wd _ _ Heq).
  apply qlinear_fraction_coordinate_bound.
  - unfold fraction_coefficients. rewrite length_map. exact Hlength.
  - now apply fraction_coefficients_nonnegative.
Qed.

Definition zinterval (bound : nat) : list Z :=
  List.map Z.of_nat (seq 0 (S bound)) ++
  List.map (fun value => (- Z.of_nat value)%Z) (seq 1 bound).

Lemma zinterval_complete : forall bound value,
    (Z.abs value <= Z.of_nat bound)%Z -> List.In value (zinterval bound).
Proof.
  intros bound value Hbound. unfold zinterval.
  destruct (Z_le_gt_dec 0 value) as [Hnonnegative|Hnegative].
  - apply in_or_app. left. apply in_map_iff.
    exists (Z.to_nat value). split.
    + apply Z2Nat.id. exact Hnonnegative.
    + apply in_seq. split; [lia|].
      rewrite Z.abs_eq in Hbound by exact Hnonnegative.
      apply Nat.lt_succ_r.
      apply Nat2Z.inj_le. rewrite Z2Nat.id by exact Hnonnegative.
      exact Hbound.
  - assert (Hpositive : (0 < - value)%Z) by lia.
    apply in_or_app. right. apply in_map_iff.
    exists (Z.to_nat (- value)). split.
    + rewrite Z2Nat.id by lia. lia.
    + apply in_seq. split.
      * apply (proj2 (Nat2Z.inj_le 1 (Z.to_nat (- value)))).
        rewrite Z2Nat.id by lia. lia.
      * assert (Habs : Z.abs value = (- value)%Z) by
          (apply Z.abs_neq; lia).
        rewrite Habs in Hbound.
        apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
        lia.
Qed.

Fixpoint zvec_box (d : nat) : (Fin.t d -> nat) -> list (ZVec d) :=
  match d as dimension return (Fin.t dimension -> nat) -> list (ZVec dimension) with
  | O => fun _ => [@Vector.nil Z]
  | S dimension => fun bounds =>
      List.flat_map (fun head =>
        List.map (fun tail => @Vector.cons Z head dimension tail)
          (zvec_box dimension (fun index => bounds (Fin.FS index))))
        (zinterval (bounds Fin.F1))
  end.

Lemma zvec_box_complete : forall d (bounds : Fin.t d -> nat)
    (value : ZVec d),
    (forall index, (Z.abs (Vector.nth value index) <=
      Z.of_nat (bounds index))%Z) ->
    List.In value (zvec_box d bounds).
Proof.
  intros d. induction d as [|d IH]; intros bounds value Hbound.
  - refine (Vector.case0 (fun value => List.In value (zvec_box 0 bounds)) _ value).
    cbn. now left.
  - refine (Vector.caseS' value (fun value =>
      (forall index, (Z.abs (Vector.nth value index) <=
        Z.of_nat (bounds index))%Z) ->
      List.In value (zvec_box (S d) bounds)) _ Hbound).
    intros head tail Hall.
    change (List.In (@Vector.cons Z head d tail)
      (List.flat_map (fun head' =>
        List.map (fun tail' => @Vector.cons Z head' d tail')
          (zvec_box d (fun index => bounds (Fin.FS index))))
        (zinterval (bounds Fin.F1)))).
    apply in_flat_map. exists head. split.
    + apply zinterval_complete. specialize (Hall Fin.F1). exact Hall.
    + apply in_map_iff. exists tail. split; [reflexivity|].
      apply IH. intro index. specialize (Hall (Fin.FS index)). exact Hall.
Qed.

Lemma zcoordinate_bound_nonnegative : forall d
    (generators : list (ZVec d)) index,
    (0 <= zcoordinate_bound generators index)%Z.
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intro index.
  - change (0 <= 0)%Z. lia.
  - change (0 <= Z.abs (Vector.nth generator index) +
      zcoordinate_bound generators index)%Z.
    pose proof (Z.abs_nonneg (Vector.nth generator index)).
    pose proof (IH index). lia.
Qed.

Definition cone_box {d} (generators : list (ZVec d)) : list (ZVec d) :=
  zvec_box d (fun index => Z.to_nat (zcoordinate_bound generators index)).

Lemma cone_box_complete : forall d (generators : list (ZVec d)) value,
    (forall index, (Z.abs (Vector.nth value index) <=
      zcoordinate_bound generators index)%Z) ->
    List.In value (cone_box generators).
Proof.
  intros d generators value Hbound. unfold cone_box.
  apply zvec_box_complete. intro index.
  rewrite Z2Nat.id by apply zcoordinate_bound_nonnegative.
  apply Hbound.
Qed.

Lemma finite_sublist : forall (A : Type) (values : list A) (P : A -> Prop),
    exists selected : list A,
      forall value, List.In value selected <-> List.In value values /\ P value.
Proof.
  intros A values. induction values as [|value values IH]; intro P.
  - exists []. intro x. cbn. tauto.
  - destruct (IH P) as [selected Hselected].
    destruct (classic (P value)) as [Hvalue|Hvalue].
    + exists (value :: selected). intro x. cbn. split.
      * intros [Heq|Hin].
        -- subst x. split; [now left|exact Hvalue].
        -- apply Hselected in Hin. destruct Hin as [Hin HP].
           split; [now right|exact HP].
      * intros [[Heq|Hin] HP].
        -- now left.
        -- right. apply Hselected. auto.
    + exists selected. intro x. rewrite Hselected. cbn. split.
      * intros [Hin HP]. split; [now right|exact HP].
      * intros [[<-|Hin] HP]; [contradiction|auto].
Qed.

Definition IntegerCone {d} (generators : list (ZVec d)) : ZSet d :=
  fun value => qcone_generated (List.map zvec_to_qvec generators)
    (zvec_to_qvec value).

Lemma zvec_to_qvec_zero_v : forall d,
    QVecEq (zvec_to_qvec (zvec_zero d)) (qvec_zero d).
Proof.
  intros d index. unfold zvec_to_qvec, zvec_zero, qvec_zero.
  rewrite const_nth. reflexivity.
Qed.

Lemma integer_cone_periodic : forall d (generators : list (ZVec d)),
    Periodic (IntegerCone generators).
Proof.
  intros d generators. constructor.
  - unfold IntegerCone. apply (proj2 (qcone_generated_qvec_ext d _ _ _
      (zvec_to_qvec_zero_v d))). apply qcone_generated_zero.
  - intros left right Hleft Hright. unfold IntegerCone in *.
    apply (proj2 (qcone_generated_qvec_ext d _ _ _
      (zvec_to_qvec_add d left right))).
    now apply qcone_generated_add.
Qed.

Lemma finite_cone_remainders : forall d (generators : list (ZVec d)),
    exists remainders : list (ZVec d),
      forall value, List.In value remainders <->
        List.In value (cone_box generators) /\ IntegerCone generators value.
Proof.
  intros. apply finite_sublist.
Qed.

Lemma zvec_generated_list_coefficients : forall d
    (generators : list (ZVec d)) coefficients,
    length coefficients = length generators ->
    zvec_generated generators
      (zvec_linear_combination generators coefficients).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength.
  - destruct coefficients; [exists (@Vector.nil nat); reflexivity|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    destruct (IH coefficients Hlength) as [tail Htail].
    exists (@Vector.cons nat coefficient _ tail).
    change (zvec_add (zvec_nsmul coefficient generator)
      (zvec_linear_combination generators (Vector.to_list tail)) =
      zvec_add (zvec_nsmul coefficient generator)
        (zvec_linear_combination generators coefficients)).
    now rewrite Htail.
Qed.

Lemma integer_part_generated : forall d (generators : list (ZVec d))
    coefficients,
    length coefficients = length generators ->
    zvec_generated generators (integer_part generators coefficients).
Proof.
  intros d generators coefficients Hlength. unfold integer_part.
  apply zvec_generated_list_coefficients. unfold floor_coefficients.
  rewrite length_map. exact Hlength.
Qed.

Lemma integer_remainder_in_cone : forall d
    (generators : list (ZVec d)) coefficients point,
    length coefficients = length generators ->
    List.Forall (fun q => 0 <= q) coefficients ->
    QVecEq (zvec_to_qvec point)
      (qlinear_combination (List.map zvec_to_qvec generators) coefficients) ->
    IntegerCone generators (integer_remainder point generators coefficients).
Proof.
  intros d generators coefficients point Hlength Hnonnegative Hpoint.
  unfold IntegerCone.
  pose proof (integer_remainder_correct d generators coefficients point
    Hlength Hnonnegative Hpoint) as Heq.
  apply (proj2 (qcone_generated_qvec_ext d _ _ _ Heq)).
  apply qlinear_combination_cone.
  - unfold fraction_coefficients. rewrite !length_map. exact Hlength.
  - apply List.Forall_forall. intros fraction Hin.
    apply in_map_iff in Hin. destruct Hin as [coefficient [<- Hin]].
    apply List.Forall_forall with (x := coefficient) in Hnonnegative;
      [|exact Hin].
    apply qfraction_bounds in Hnonnegative. tauto.
Qed.

Theorem integer_points_integer_vcone_finitely_generated :
  forall d (generators : list (ZVec d)),
    FinitelyGeneratedPeriodic (IntegerCone generators).
Proof.
  intros d generators.
  destruct (finite_cone_remainders d generators) as
    [remainders Hremainders].
  exists (generators ++ remainders). split.
  - intros generator Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + unfold IntegerCone. apply qcone_generated_generator.
      apply in_map. exact Hin.
    + apply Hremainders in Hin. tauto.
  - intro point. split.
    + intro Hpoint.
      apply qcone_generated_aligned_coefficients in Hpoint.
      destruct Hpoint as [coefficients [Hlength [Hnonnegative Hpoint]]].
      set (part := integer_part generators coefficients).
      set (remainder := integer_remainder point generators coefficients).
      assert (Hpart : zvec_generated (generators ++ remainders) part).
      { apply generated_append_left. unfold part.
        apply integer_part_generated. now rewrite length_map in Hlength. }
      assert (Hremainder_cone : IntegerCone generators remainder).
      { unfold remainder. apply integer_remainder_in_cone;
          try assumption. now rewrite length_map in Hlength. }
      assert (Hremainder_box : List.In remainder (cone_box generators)).
      { apply cone_box_complete. intro index. unfold remainder.
        apply integer_remainder_coordinate_bound;
          try assumption. now rewrite length_map in Hlength. }
      assert (Hremainder : List.In remainder remainders).
      { apply Hremainders. auto. }
      assert (Hremainder_generated :
          zvec_generated (generators ++ remainders) remainder).
      { apply generated_append_right, generated_generator. exact Hremainder. }
      replace point with (zvec_add part remainder).
      * now apply generated_add.
      * unfold part, remainder, integer_remainder.
        apply zvec_sub_add_cancel.
    + intro Hgenerated.
      eapply generated_in_periodic; [apply integer_cone_periodic| |exact Hgenerated].
      intros generator Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      * unfold IntegerCone. apply qcone_generated_generator.
        apply in_map. exact Hin.
      * apply Hremainders in Hin. tauto.
Qed.

Lemma finitely_generated_periodic_ext : forall d (P Q : ZSet d),
    SameSet P Q -> FinitelyGeneratedPeriodic P ->
    FinitelyGeneratedPeriodic Q.
Proof.
  intros d P Q Heq [generators [Hgenerators Hgenerated]].
  exists generators. split.
  - intros generator Hin. apply (proj1 (Heq generator)). now apply Hgenerators.
  - intro value. rewrite <- Hgenerated. symmetry. apply Heq.
Qed.

Theorem integer_points_vcone_finitely_generated :
  forall k (W : list (QVec k)),
    FinitelyGeneratedPeriodic
      (fun z : ZVec k =>
        qcone_generated W (zvec_to_qvec z)).
Proof.
  intros k W. destruct (integerize_vcone k W) as [integers Hcones].
  eapply (finitely_generated_periodic_ext k (IntegerCone integers)
    (fun z : ZVec k => qcone_generated W (zvec_to_qvec z))).
  - intro value. unfold IntegerCone. symmetry. apply Hcones.
  - apply integer_points_integer_vcone_finitely_generated.
Qed.
