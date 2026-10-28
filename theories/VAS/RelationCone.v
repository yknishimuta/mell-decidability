From Coq Require Import Fin Lia List QArith Qring Vector VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Geometry Require Import ClosedLinearization Cone LatticeGordanPullback LatticeGordanV
  MathCompBridge Periodic QConeCore RationalDefinability RationalHToV.
From Mell.Order Require Import PeriodicOrder.
From Mell.VAS Require Import Transformer.

Open Scope Z_scope.
Open Scope Q_scope.

Definition ZRelation (d : nat) := ZVec d -> ZVec d -> Prop.

Definition ZRelSubset {d} (R S : ZRelation d) : Prop :=
  forall input output, R input output -> S input output.

Definition ZRelSame {d} (R S : ZRelation d) : Prop :=
  forall input output, R input output <-> S input output.

Definition ZRelIdentity {d} : ZRelation d := fun input output => input = output.

Definition ZRelCompose {d} (R S : ZRelation d) : ZRelation d :=
  fun input output => exists middle, R input middle /\ S middle output.

Definition zpair_pack {d} (left right : ZVec d) : ZVec (d + d) :=
  Vector.append left right.

Definition zpair_left {d} (value : ZVec (d + d)) : ZVec d :=
  fst (Vector.splitat d value).

Definition zpair_right {d} (value : ZVec (d + d)) : ZVec d :=
  snd (Vector.splitat d value).

Lemma zpair_left_pack : forall d (left right : ZVec d),
    zpair_left (zpair_pack left right) = left.
Proof. intros; unfold zpair_left, zpair_pack; now rewrite VectorSpec.splitat_append. Qed.

Lemma zpair_right_pack : forall d (left right : ZVec d),
    zpair_right (zpair_pack left right) = right.
Proof. intros; unfold zpair_right, zpair_pack; now rewrite VectorSpec.splitat_append. Qed.

Lemma zpair_pack_split : forall d (value : ZVec (d + d)),
    zpair_pack (zpair_left value) (zpair_right value) = value.
Proof.
  intros d value. unfold zpair_pack, zpair_left, zpair_right.
  destruct (Vector.splitat d value) as [left right] eqn:Hsplit.
  now apply VectorSpec.append_splitat in Hsplit.
Qed.

Lemma zpair_pack_injective : forall d
    (left1 right1 left2 right2 : ZVec d),
    zpair_pack left1 right1 = zpair_pack left2 right2 ->
    left1 = left2 /\ right1 = right2.
Proof.
  intros d left1 right1 left2 right2 Heq. split.
  - pose proof (f_equal (@zpair_left d) Heq) as Hleft.
    now rewrite !zpair_left_pack in Hleft.
  - pose proof (f_equal (@zpair_right d) Heq) as Hright.
    now rewrite !zpair_right_pack in Hright.
Qed.

Lemma vector_map2_append : forall A B C (operation : A -> B -> C)
    left_length right_length
    (left1 : Vector.t A left_length) (right1 : Vector.t A right_length)
    (left2 : Vector.t B left_length) (right2 : Vector.t B right_length),
    Vector.map2 operation (Vector.append left1 right1)
      (Vector.append left2 right2) =
    Vector.append (Vector.map2 operation left1 left2)
      (Vector.map2 operation right1 right2).
Proof.
  intros A B C operation left_length right_length left1.
  induction left1 as [|head length tail IH]; intros right1 left2 right2.
  - refine (Vector.case0 (fun left2 => _) _ left2). reflexivity.
  - refine (Vector.caseS' left2 (fun left2 => _) _).
    intros head2 tail2. cbn. f_equal. apply IH.
Qed.

Lemma zpair_pack_add : forall d (left1 right1 left2 right2 : ZVec d),
    zvec_add (zpair_pack left1 right1) (zpair_pack left2 right2) =
    zpair_pack (zvec_add left1 left2) (zvec_add right1 right2).
Proof.
  intros d left1 right1 left2 right2.
  unfold zvec_add, zpair_pack. apply vector_map2_append.
Qed.

Lemma vector_append_const : forall A (value : A) left_length right_length,
    Vector.append (Vector.const value left_length)
      (Vector.const value right_length) =
    Vector.const value (left_length + right_length).
Proof.
  intros A value left_length. induction left_length as [|left_length IH];
    intro right_length; cbn; [reflexivity|].
  now rewrite IH.
Qed.

Lemma zpair_pack_zero : forall d,
    zpair_pack (zvec_zero d) (zvec_zero d) = zvec_zero (d + d).
Proof.
  intro d. unfold zpair_pack, zvec_zero. apply vector_append_const.
Qed.

Lemma zpair_pack_nsmul : forall d coefficient (left right : ZVec d),
    zvec_nsmul coefficient (zpair_pack left right) =
    zpair_pack (zvec_nsmul coefficient left) (zvec_nsmul coefficient right).
Proof.
  intros d coefficient. induction coefficient as [|coefficient IH];
    intros left right.
  - symmetry. apply zpair_pack_zero.
  - cbn [zvec_nsmul]. rewrite IH. apply zpair_pack_add.
Qed.

Definition ZRelationPairs {d} (R : ZRelation d) : ZSet (d + d) :=
  fun pair => R (zpair_left pair) (zpair_right pair).

Lemma zrelation_pairs_pack : forall d (R : ZRelation d) input output,
    ZRelationPairs R (zpair_pack input output) <-> R input output.
Proof. intros; unfold ZRelationPairs; now rewrite zpair_left_pack, zpair_right_pack. Qed.

Lemma zrelation_same_pairs : forall d (R S : ZRelation d),
    ZRelSame R S <-> SameSet (ZRelationPairs R) (ZRelationPairs S).
Proof.
  intros d R S. split.
  - intros H pair. unfold ZRelationPairs. apply H.
  - intros H input output. specialize (H (zpair_pack input output)).
    now rewrite !zrelation_pairs_pack in H.
Qed.

Definition qpair_pack {d} (left right : QVec d) : QVec (d + d) :=
  qvec_join left right.

Definition qpair_left {d} (value : QVec (d + d)) : QVec d :=
  qvec_left (n := d) (m := d) value.
Definition qpair_right {d} (value : QVec (d + d)) : QVec d :=
  qvec_right (n := d) (m := d) value.

Lemma qpair_left_pack : forall d (left right : QVec d),
    QVecEq (qpair_left (qpair_pack left right)) left.
Proof. intros; apply qvec_join_left. Qed.

Lemma qpair_right_pack : forall d (left right : QVec d),
    QVecEq (qpair_right (qpair_pack left right)) right.
Proof. intros; apply qvec_join_right. Qed.

Lemma qpair_pack_split : forall d (value : QVec (d + d)),
    QVecEq value (qpair_pack (qpair_left value) (qpair_right value)).
Proof. intros d value. exact (qvec_join_split d d value). Qed.

Lemma qpair_pack_ext : forall d
    (left1 right1 left2 right2 : QVec d),
    QVecEq left1 left2 -> QVecEq right1 right2 ->
    QVecEq (qpair_pack left1 right1) (qpair_pack left2 right2).
Proof.
  intros d left1 right1 left2 right2 Hleft Hright index.
  refine (Fin.case_L_R' (fun index =>
    (qpair_pack left1 right1) index == (qpair_pack left2 right2) index)
    index _ _); intros component.
  - unfold qpair_pack, qvec_join, qvec_of_vector.
    rewrite !VectorSpec.nth_append_L, !qvec_to_vector_nth. apply Hleft.
  - unfold qpair_pack, qvec_join, qvec_of_vector.
    rewrite !VectorSpec.nth_append_R, !qvec_to_vector_nth. apply Hright.
Qed.

Lemma qpair_pack_components : forall d
    (left1 right1 left2 right2 : QVec d),
    QVecEq (qpair_pack left1 right1) (qpair_pack left2 right2) ->
    QVecEq left1 left2 /\ QVecEq right1 right2.
Proof.
  intros d left1 right1 left2 right2 Heq. split; intro index.
  - specialize (Heq (Fin.L d index)).
    unfold qpair_pack, qvec_join, qvec_of_vector in Heq.
    rewrite !VectorSpec.nth_append_L, !qvec_to_vector_nth in Heq. exact Heq.
  - specialize (Heq (Fin.R d index)).
    unfold qpair_pack, qvec_join, qvec_of_vector in Heq.
    rewrite !VectorSpec.nth_append_R, !qvec_to_vector_nth in Heq. exact Heq.
Qed.

Lemma qpair_pack_scale : forall d coefficient (left right : QVec d),
    QVecEq (qvec_scale coefficient (qpair_pack left right))
      (qpair_pack (qvec_scale coefficient left) (qvec_scale coefficient right)).
Proof.
  intros d coefficient left right index.
  refine (Fin.case_L_R' (fun index =>
    qvec_scale coefficient (qpair_pack left right) index ==
      qpair_pack (qvec_scale coefficient left)
        (qvec_scale coefficient right) index) index _ _); intros component.
  - unfold qpair_pack, qvec_join, qvec_of_vector, qvec_scale.
    repeat rewrite VectorSpec.nth_append_L.
    repeat rewrite qvec_to_vector_nth. reflexivity.
  - unfold qpair_pack, qvec_join, qvec_of_vector, qvec_scale.
    repeat rewrite VectorSpec.nth_append_R.
    repeat rewrite qvec_to_vector_nth. reflexivity.
Qed.

Lemma qpair_pack_add_q : forall d
    (left1 right1 left2 right2 : QVec d),
    QVecEq
      (qvec_add (qpair_pack left1 right1) (qpair_pack left2 right2))
      (qpair_pack (qvec_add left1 left2) (qvec_add right1 right2)).
Proof.
  intros d left1 right1 left2 right2 index.
  refine (Fin.case_L_R' (fun index =>
    qvec_add (qpair_pack left1 right1) (qpair_pack left2 right2) index ==
      qpair_pack (qvec_add left1 left2) (qvec_add right1 right2) index)
    index _ _); intros component;
    unfold qpair_pack, qvec_join, qvec_of_vector, qvec_add.
  - repeat first [rewrite VectorSpec.nth_append_L |
      rewrite qvec_to_vector_nth]. reflexivity.
  - repeat first [rewrite VectorSpec.nth_append_R |
      rewrite qvec_to_vector_nth]. reflexivity.
Qed.

Lemma qpair_pack_zero_q : forall d,
    QVecEq (qpair_pack (qvec_zero d) (qvec_zero d)) (qvec_zero (d + d)).
Proof.
  intro d. intro index.
  refine (Fin.case_L_R' (fun index =>
    qpair_pack (qvec_zero d) (qvec_zero d) index == qvec_zero (d + d) index)
    index _ _); intros component;
    unfold qpair_pack, qvec_join, qvec_of_vector, qvec_zero.
  - rewrite VectorSpec.nth_append_L, qvec_to_vector_nth. reflexivity.
  - rewrite VectorSpec.nth_append_R, qvec_to_vector_nth. reflexivity.
Qed.

Lemma zpair_pack_to_qvec : forall d (left right : ZVec d),
    QVecEq (zvec_to_qvec (zpair_pack left right))
      (qpair_pack (zvec_to_qvec left) (zvec_to_qvec right)).
Proof.
  intros d left right index.
  refine (Fin.case_L_R' (fun index =>
    zvec_to_qvec (zpair_pack left right) index ==
      qpair_pack (zvec_to_qvec left) (zvec_to_qvec right) index)
    index _ _); intros component.
  - unfold zvec_to_qvec, qpair_pack, qvec_join, qvec_of_vector, zpair_pack.
    rewrite !VectorSpec.nth_append_L, qvec_to_vector_nth. reflexivity.
  - unfold zvec_to_qvec, qpair_pack, qvec_join, qvec_of_vector, zpair_pack.
    rewrite !VectorSpec.nth_append_R, qvec_to_vector_nth. reflexivity.
Qed.

Definition PeriodicZRelation {d} (R : ZRelation d) : Prop :=
  R (zvec_zero d) (zvec_zero d) /\
  forall x1 y1 x2 y2,
    R x1 y1 -> R x2 y2 ->
    R (zvec_add x1 x2) (zvec_add y1 y2).

Theorem periodic_zrelation_pairs_iff : forall d (R : ZRelation d),
    PeriodicZRelation R <-> Periodic (ZRelationPairs R).
Proof.
  intros d R. split.
  - intros [Hzero Hadd]. split.
    + rewrite <- zpair_pack_zero, zrelation_pairs_pack. exact Hzero.
    + intros left right Hleft Hright.
      rewrite <- (zpair_pack_split d left), <- (zpair_pack_split d right).
      rewrite zpair_pack_add, zrelation_pairs_pack.
      unfold ZRelationPairs in Hleft, Hright. now apply Hadd.
  - intros [Hzero Hadd]. split.
    + apply (proj1 (zrelation_pairs_pack d R _ _)).
      rewrite zpair_pack_zero. exact Hzero.
    + intros x1 y1 x2 y2 H1 H2.
      apply (proj1 (zrelation_pairs_pack d R _ _)).
      rewrite <- zpair_pack_add. apply Hadd;
        now apply (proj2 (zrelation_pairs_pack d R _ _)).
Qed.

Theorem periodic_zrelation_compose : forall d (R S : ZRelation d),
    PeriodicZRelation R -> PeriodicZRelation S ->
    PeriodicZRelation (ZRelCompose R S).
Proof.
  intros d R S [HRzero HRadd] [HSzero HSadd]. split.
  - exists (zvec_zero d). auto.
  - intros x1 z1 x2 z2 [y1 [HR1 HS1]] [y2 [HR2 HS2]].
    exists (zvec_add y1 y2). split; [eapply HRadd|eapply HSadd]; eauto.
Qed.

Definition ZVecNonnegative {d} (value : ZVec d) : Prop :=
  forall index, (0 <= Vector.nth value index)%Z.

Definition NRelationAsZ {d} (R : NRelation d) : ZRelation d :=
  fun input output =>
    exists ninput noutput,
      input = nvec_to_zvec ninput /\ output = nvec_to_zvec noutput /\
      R ninput noutput.

Lemma nvec_to_zvec_injective_relation : forall d (left right : NVec d),
    nvec_to_zvec left = nvec_to_zvec right -> left = right.
Proof.
  intros d left right Heq. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index other <-.
  pose proof (f_equal (fun value => Vector.nth value index) Heq) as Hcoord.
  unfold nvec_to_zvec in Hcoord.
  repeat rewrite (nth_map Z.of_nat _ index index eq_refl) in Hcoord. lia.
Qed.

Lemma nrelation_as_z_nonnegative : forall d (R : NRelation d) input output,
    NRelationAsZ R input output ->
    ZVecNonnegative input /\ ZVecNonnegative output.
Proof.
  intros d R input output [ninput [noutput [-> [-> _]]]]. split;
    intro index; unfold nvec_to_zvec;
    rewrite (nth_map Z.of_nat _ index index eq_refl); lia.
Qed.

Lemma nrelation_as_z_witness_unique : forall d (R : NRelation d)
    (input output : ZVec d)
    (ninput1 noutput1 ninput2 noutput2 : NVec d),
    input = nvec_to_zvec ninput1 -> output = nvec_to_zvec noutput1 ->
    input = nvec_to_zvec ninput2 -> output = nvec_to_zvec noutput2 ->
    ninput1 = ninput2 /\ noutput1 = noutput2.
Proof.
  intros d R input output ninput1 noutput1 ninput2 noutput2
    Hin1 Hout1 Hin2 Hout2. split; apply nvec_to_zvec_injective_relation.
  - now rewrite <- Hin1, <- Hin2.
  - now rewrite <- Hout1, <- Hout2.
Qed.

Lemma nrelation_as_z_compose : forall d (R S : NRelation d),
    ZRelSame (NRelationAsZ (NRelCompose R S))
      (ZRelCompose (NRelationAsZ R) (NRelationAsZ S)).
Proof.
  intros d R S input output. split.
  - intros [ninput [noutput [-> [-> [middle [HR HS]]]]]].
    exists (nvec_to_zvec middle). split.
    + exists ninput, middle. auto.
    + exists middle, noutput. auto.
  - intros [middle [[ninput [nmid1 [Hin [Hmid1 HR]]]]
      [nmid2 [noutput [Hmid2 [Hout HS]]]]]].
    assert (nmid1 = nmid2) as ->.
    { apply nvec_to_zvec_injective_relation. now rewrite <- Hmid1, <- Hmid2. }
    exists ninput, noutput. repeat split; try assumption. now exists nmid2.
Qed.

Theorem periodic_nrelation_as_z : forall d (R : NRelation d),
    PeriodicNRelation R -> PeriodicZRelation (NRelationAsZ R).
Proof.
  intros d R [Hzero Hadd]. split.
  - exists (nvec_zero d), (nvec_zero d). repeat split; try exact Hzero.
    + apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index other <-.
      unfold zvec_zero, nvec_zero, nvec_to_zvec.
      rewrite const_nth, (nth_map Z.of_nat _ index index eq_refl), const_nth.
      reflexivity.
    + apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index other <-.
      unfold zvec_zero, nvec_zero, nvec_to_zvec.
      rewrite const_nth, (nth_map Z.of_nat _ index index eq_refl), const_nth.
      reflexivity.
  - intros x1 y1 x2 y2
      [nx1 [ny1 [-> [-> HR1]]]] [nx2 [ny2 [-> [-> HR2]]]].
    exists (nvec_add nx1 nx2), (nvec_add ny1 ny2). repeat split.
    + symmetry. apply nvec_to_zvec_add.
    + symmetry. apply nvec_to_zvec_add.
    + now apply Hadd.
Qed.

Definition RationalRelationCone {d} (R : ZRelation d)
    (input output : QVec d) : Prop :=
  Cone (ZRelationPairs R) (qpair_pack input output).

Lemma cone_qvec_ext_relation : forall d (set : ZSet d) left right,
    QVecEq left right -> (Cone set left <-> Cone set right).
Proof.
  intros d set left right Heq. split;
    intros [generated [Hgenerated Hpoint]]; exists generated; split;
    [exact Hgenerated| |exact Hgenerated|].
  - eapply qvec_eq_trans; [apply qvec_eq_sym; exact Heq|exact Hpoint].
  - eapply qvec_eq_trans; [exact Heq|exact Hpoint].
Qed.

Lemma cone_contains_zero_generated : forall d (set : ZSet d),
    Cone set (qvec_zero d).
Proof.
  intros d set. exists (qvec_zero d). split; [constructor|apply qvec_eq_refl].
Qed.

Lemma cone_closed_add_generated : forall d (set : ZSet d) left right,
    Cone set left -> Cone set right -> Cone set (qvec_add left right).
Proof.
  intros d set left right [left_generated [Hleft Hleft_eq]]
    [right_generated [Hright Hright_eq]].
  destruct (cone_gen_plus d set left_generated right_generated Hleft Hright)
    as [sum [Hsum Hsum_eq]].
  exists sum. split; [exact Hsum|]. intro index.
  transitivity (qvec_add left_generated right_generated index).
  - unfold qvec_add. apply Qplus_comp; [apply Hleft_eq|apply Hright_eq].
  - symmetry. apply Hsum_eq.
Qed.

Lemma cone_closed_scale_generated : forall d (set : ZSet d) coefficient value,
    (0 <= coefficient)%Q ->
    Cone set value -> Cone set (qvec_scale coefficient value).
Proof.
  intros d set coefficient value Hcoefficient
    [generated [Hgenerated Hvalue]].
  destruct (cone_gen_scale d set generated coefficient Hgenerated Hcoefficient)
    as [scaled [Hscaled Hscaled_eq]].
  exists scaled. split; [exact Hscaled|]. intro index.
  transitivity (qvec_scale coefficient generated index).
  - unfold qvec_scale. apply Qmult_comp; [reflexivity|apply Hvalue].
  - symmetry. apply Hscaled_eq.
Qed.

Lemma rational_relation_cone_zero : forall d (R : ZRelation d),
    RationalRelationCone R (qvec_zero d) (qvec_zero d).
Proof.
  intros d R. unfold RationalRelationCone.
  apply (proj2 (cone_qvec_ext_relation (d + d) (ZRelationPairs R)
    (qpair_pack (qvec_zero d) (qvec_zero d)) (qvec_zero (d + d))
    (qpair_pack_zero_q d))).
  apply cone_contains_zero_generated.
Qed.

Lemma rational_relation_cone_add : forall d (R : ZRelation d)
    input1 output1 input2 output2,
    RationalRelationCone R input1 output1 ->
    RationalRelationCone R input2 output2 ->
    RationalRelationCone R (qvec_add input1 input2) (qvec_add output1 output2).
Proof.
  intros d R input1 output1 input2 output2 Hleft Hright.
  unfold RationalRelationCone in *. apply (proj1 (cone_qvec_ext_relation
    (d + d) (ZRelationPairs R)
    (qvec_add (qpair_pack input1 output1) (qpair_pack input2 output2)) _
    (qpair_pack_add_q d input1 output1 input2 output2))).
  now apply cone_closed_add_generated.
Qed.

Lemma rational_relation_cone_scale : forall d (R : ZRelation d)
    coefficient input output,
    (0 <= coefficient)%Q ->
    RationalRelationCone R input output ->
    RationalRelationCone R (qvec_scale coefficient input)
      (qvec_scale coefficient output).
Proof.
  intros d R coefficient input output Hcoefficient Hmember.
  unfold RationalRelationCone in *. apply (proj1 (cone_qvec_ext_relation
    (d + d) (ZRelationPairs R)
    (qvec_scale coefficient (qpair_pack input output)) _
    (qpair_pack_scale d coefficient input output))).
  now apply cone_closed_scale_generated.
Qed.

Lemma rational_relation_cone_member : forall d (R : ZRelation d) input output,
    R input output ->
    RationalRelationCone R (zvec_to_qvec input) (zvec_to_qvec output).
Proof.
  intros d R input output HR. unfold RationalRelationCone.
  apply (proj1 (cone_qvec_ext_relation (d + d) (ZRelationPairs R)
    (zvec_to_qvec (zpair_pack input output)) _
    (zpair_pack_to_qvec d input output))).
  exists (qvec_add (qvec_scale 1 (zvec_to_qvec (zpair_pack input output)))
    (qvec_zero (d + d))). split.
  - apply cone_add.
    + unfold Qle. cbn. lia.
    + now apply (proj2 (zrelation_pairs_pack d R input output)).
    + constructor.
  - intro index. unfold qvec_add, qvec_scale, qvec_zero. ring.
Qed.

Theorem periodic_cone_positive_multiple_iff : forall k (set : ZSet k) point,
    Periodic set ->
    (Cone set point <->
      exists multiplier : nat, exists integer_point : ZVec k,
        (0 < multiplier)%nat /\ set integer_point /\
        QVecEq (qvec_scale (q_of_nat multiplier) point)
          (zvec_to_qvec integer_point)).
Proof.
  intros k set point Hperiodic.
  rewrite periodic_standard_cone_denominator_clearing by exact Hperiodic.
  split.
  - intros [multiplier [integer_point
      [Hpositive [Hmember Hpoint]]]].
    exists multiplier, integer_point. repeat split; try assumption.
    intro index. transitivity
      (q_of_nat multiplier *
        (/ q_of_nat multiplier * zvec_to_qvec integer_point index)).
    + apply Qmult_comp; [reflexivity|apply Hpoint].
    + unfold q_of_nat. field. intro Hzero.
      apply (proj1 (inject_Z_injective (Z.of_nat multiplier) 0%Z)) in Hzero.
      lia.
  - intros [multiplier [integer_point
      [Hpositive [Hmember Hpoint]]]].
    exists multiplier, integer_point. repeat split; try assumption.
    intro index. transitivity
      (/ q_of_nat multiplier *
        (q_of_nat multiplier * point index)).
    + unfold q_of_nat. field. intro Hzero.
      apply (proj1 (inject_Z_injective (Z.of_nat multiplier) 0%Z)) in Hzero.
      lia.
    + apply Qmult_comp; [reflexivity|apply Hpoint].
Qed.

Lemma qpair_positive_multiple_components : forall d multiplier
    (input output : QVec d) (integer_pair : ZVec (d + d)),
    QVecEq
      (qvec_scale (q_of_nat multiplier) (qpair_pack input output))
      (zvec_to_qvec integer_pair) ->
    QVecEq (qvec_scale (q_of_nat multiplier) input)
      (zvec_to_qvec (zpair_left integer_pair)) /\
    QVecEq (qvec_scale (q_of_nat multiplier) output)
      (zvec_to_qvec (zpair_right integer_pair)).
Proof.
  intros d multiplier input output integer_pair Hpoint.
  assert (Hpacked : QVecEq
      (qpair_pack (qvec_scale (q_of_nat multiplier) input)
        (qvec_scale (q_of_nat multiplier) output))
      (qpair_pack (zvec_to_qvec (zpair_left integer_pair))
        (zvec_to_qvec (zpair_right integer_pair)))).
  { eapply qvec_eq_trans.
    - apply qvec_eq_sym, qpair_pack_scale.
    - eapply qvec_eq_trans; [exact Hpoint|].
      eapply qvec_eq_trans with (y := zvec_to_qvec
        (zpair_pack (zpair_left integer_pair) (zpair_right integer_pair))).
      + rewrite zpair_pack_split. apply qvec_eq_refl.
      + apply zpair_pack_to_qvec. }
  now apply qpair_pack_components in Hpacked.
Qed.

Lemma qpair_positive_multiple_intro : forall d multiplier
    (input output : QVec d) (integer_input integer_output : ZVec d),
    QVecEq (qvec_scale (q_of_nat multiplier) input)
      (zvec_to_qvec integer_input) ->
    QVecEq (qvec_scale (q_of_nat multiplier) output)
      (zvec_to_qvec integer_output) ->
    QVecEq
      (qvec_scale (q_of_nat multiplier) (qpair_pack input output))
      (zvec_to_qvec (zpair_pack integer_input integer_output)).
Proof.
  intros d multiplier input output integer_input integer_output Hinput Houtput.
  eapply qvec_eq_trans; [apply qpair_pack_scale|].
  eapply qvec_eq_trans.
  - apply qpair_pack_ext; [exact Hinput|exact Houtput].
  - apply qvec_eq_sym, zpair_pack_to_qvec.
Qed.

Theorem periodic_relation_cone_positive_multiple_iff : forall d
    (R : ZRelation d) input output,
    PeriodicZRelation R ->
    (RationalRelationCone R input output <->
      exists multiplier integer_input integer_output,
        (0 < multiplier)%nat /\ R integer_input integer_output /\
        QVecEq (qvec_scale (q_of_nat multiplier) input)
          (zvec_to_qvec integer_input) /\
        QVecEq (qvec_scale (q_of_nat multiplier) output)
          (zvec_to_qvec integer_output)).
Proof.
  intros d R input output Hperiodic.
  unfold RationalRelationCone.
  rewrite periodic_cone_positive_multiple_iff.
  2: { now apply (proj1 (periodic_zrelation_pairs_iff d R)). }
  split.
  - intros [multiplier [integer_pair
      [Hpositive [Hmember Hpoint]]]].
    apply qpair_positive_multiple_components in Hpoint as [Hinput Houtput].
    exists multiplier, (zpair_left integer_pair), (zpair_right integer_pair).
    split; [exact Hpositive|]. split; [exact Hmember|].
    split; [exact Hinput|exact Houtput].
  - intros [multiplier [integer_input [integer_output
      [Hpositive [Hmember [Hinput Houtput]]]]]].
    exists multiplier, (zpair_pack integer_input integer_output).
    repeat split; try assumption.
    + now apply (proj2 (zrelation_pairs_pack d R integer_input integer_output)).
    + now apply qpair_positive_multiple_intro.
Qed.

Lemma qvec_scale_nat_product : forall d left right (value : QVec d),
    QVecEq
      (qvec_scale (q_of_nat (left * right)) value)
      (qvec_scale (q_of_nat left) (qvec_scale (q_of_nat right) value)).
Proof.
  intros d left right value index. unfold qvec_scale, q_of_nat.
  rewrite Nat2Z.inj_mul, inject_Z_mult. ring.
Qed.

Lemma zvec_nsmul_to_qvec_nat : forall d coefficient (value : ZVec d),
    QVecEq (zvec_to_qvec (zvec_nsmul coefficient value))
      (qvec_scale (q_of_nat coefficient) (zvec_to_qvec value)).
Proof.
  intros d coefficient value. apply zvec_nsmul_to_qvec.
Qed.

Lemma periodic_zrelation_nsmul : forall d (R : ZRelation d),
    PeriodicZRelation R -> forall coefficient input output,
      R input output ->
      R (zvec_nsmul coefficient input) (zvec_nsmul coefficient output).
Proof.
  intros d R [Hzero Hadd] coefficient. induction coefficient as [|coefficient IH];
    intros input output Hmember; cbn [zvec_nsmul].
  - exact Hzero.
  - apply Hadd; [exact Hmember|now apply IH].
Qed.

Theorem periodic_relation_cone_compose : forall d (R S : ZRelation d),
    PeriodicZRelation R -> PeriodicZRelation S ->
    forall input output : QVec d,
      (RationalRelationCone (ZRelCompose R S) input output <->
       exists middle : QVec d,
         RationalRelationCone R input middle /\
         RationalRelationCone S middle output).
Proof.
  intros d R S HRperiodic HSperiodic input output. split.
  - intro Hcompose.
    apply (proj1 (periodic_relation_cone_positive_multiple_iff d
      (ZRelCompose R S) input output
      (periodic_zrelation_compose d R S HRperiodic HSperiodic))) in Hcompose.
    destruct Hcompose as [multiplier [integer_input [integer_output
      [Hpositive [[integer_middle [HR HS]] [Hinput Houtput]]]]]].
    exists (qvec_scale (/ q_of_nat multiplier)
      (zvec_to_qvec integer_middle)). split.
    + apply (proj2 (periodic_relation_cone_positive_multiple_iff d R _ _
        HRperiodic)).
      exists multiplier, integer_input, integer_middle.
      repeat split; try assumption.
      intro index. unfold qvec_scale, q_of_nat. field.
      intro Hzero. apply (proj1
        (inject_Z_injective (Z.of_nat multiplier) 0%Z)) in Hzero. lia.
    + apply (proj2 (periodic_relation_cone_positive_multiple_iff d S _ _
        HSperiodic)).
      exists multiplier, integer_middle, integer_output.
      repeat split; try assumption.
      intro index. unfold qvec_scale, q_of_nat. field.
      intro Hzero. apply (proj1
        (inject_Z_injective (Z.of_nat multiplier) 0%Z)) in Hzero. lia.
  - intros [middle [HRcone HScone]].
    apply (proj1 (periodic_relation_cone_positive_multiple_iff d R _ _
      HRperiodic)) in HRcone.
    apply (proj1 (periodic_relation_cone_positive_multiple_iff d S _ _
      HSperiodic)) in HScone.
    destruct HRcone as [left_multiplier [integer_input [left_middle
      [Hleft_positive [HR [Hinput Hleft_middle]]]]]].
    destruct HScone as [right_multiplier [right_middle [integer_output
      [Hright_positive [HS [Hright_middle Houtput]]]]]].
    assert (Hmiddle :
      zvec_nsmul right_multiplier left_middle =
      zvec_nsmul left_multiplier right_middle).
    { apply zvec_to_qvec_injective. intro index.
      transitivity (qvec_scale (q_of_nat right_multiplier)
        (zvec_to_qvec left_middle) index).
      - apply zvec_nsmul_to_qvec_nat.
      transitivity
        (q_of_nat right_multiplier *
          (q_of_nat left_multiplier * middle index)).
      - unfold qvec_scale.
        apply Qmult_comp; [reflexivity|]. symmetry. apply Hleft_middle.
      - transitivity
          (q_of_nat left_multiplier *
            (q_of_nat right_multiplier * middle index)); [ring|].
        transitivity (qvec_scale (q_of_nat left_multiplier)
          (zvec_to_qvec right_middle) index).
        + unfold qvec_scale.
          apply Qmult_comp; [reflexivity|apply Hright_middle].
        + symmetry. apply zvec_nsmul_to_qvec_nat. }
    apply (proj2 (periodic_relation_cone_positive_multiple_iff d
      (ZRelCompose R S) input output
      (periodic_zrelation_compose d R S HRperiodic HSperiodic))).
    exists (left_multiplier * right_multiplier)%nat,
      (zvec_nsmul right_multiplier integer_input),
      (zvec_nsmul left_multiplier integer_output).
    repeat split.
    + nia.
    + exists (zvec_nsmul right_multiplier left_middle). split.
      * now apply (periodic_zrelation_nsmul d R HRperiodic).
      * rewrite Hmiddle.
        now apply (periodic_zrelation_nsmul d S HSperiodic).
    + eapply qvec_eq_trans; [apply qvec_scale_nat_product|].
      intro index. unfold qvec_scale.
      transitivity
        (q_of_nat right_multiplier *
          (q_of_nat left_multiplier * input index)); [ring|].
      transitivity
        (q_of_nat right_multiplier * zvec_to_qvec integer_input index).
      * apply Qmult_comp; [reflexivity|apply Hinput].
      * symmetry. apply zvec_nsmul_to_qvec_nat.
    + eapply qvec_eq_trans; [apply qvec_scale_nat_product|].
      eapply qvec_eq_trans.
      * intro index. unfold qvec_scale.
        apply Qmult_comp; [reflexivity|apply Houtput].
      * apply qvec_eq_sym, zvec_nsmul_to_qvec_nat.
Qed.
