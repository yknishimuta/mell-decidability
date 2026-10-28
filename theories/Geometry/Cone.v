From Coq Require Import List Vector VectorSpec ZArith QArith Qring Lia.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge Periodic.

Open Scope Z_scope.
Open Scope Q_scope.

Record PositiveRat : Type := {
  positive_num : nat;
  positive_den : nat;
  positive_num_nonzero : (0 < positive_num)%nat;
  positive_den_nonzero : (0 < positive_den)%nat
}.

Definition positive_value (coefficient : PositiveRat) : Q :=
  q_of_nat (positive_num coefficient) / q_of_nat (positive_den coefficient).

Definition cleared_point {d} (denominator : nat) (value : ZVec d) : QVec d :=
  qvec_scale (/ q_of_nat denominator) (zvec_to_qvec value).

Definition ClearedCone {d} (set : ZVec d -> Prop) (point : QVec d) : Prop :=
  exists denominator value,
    (0 < denominator)%nat /\ set value /\
    qvec_eq point (cleared_point denominator value).

Definition RayCone {d} (set : ZVec d -> Prop) (point : QVec d) : Prop :=
  exists coefficient value,
    set value /\
    qvec_eq point
      (qvec_scale (positive_value coefficient) (zvec_to_qvec value)).

Lemma q_of_nat_nonzero : forall value, (0 < value)%nat -> ~ q_of_nat value == 0.
Proof.
  intros value Hpositive Heq.
  unfold q_of_nat in Heq.
  assert (Z.of_nat value = 0%Z) as Hzero.
  { apply (proj1 (inject_Z_injective (Z.of_nat value) 0%Z)). exact Heq. }
  lia.
Qed.

Lemma q_of_nat_one : q_of_nat 1 == 1.
Proof. reflexivity. Qed.

Inductive ConeGen {d} (set : ZVec d -> Prop) : QVec d -> Prop :=
| cone_zero : ConeGen set (qvec_zero d)
| cone_add : forall coefficient value tail,
    0 <= coefficient -> set value -> ConeGen set tail ->
    ConeGen set (qvec_add
      (qvec_scale coefficient (zvec_to_qvec value)) tail).

Definition Cone {d} (set : ZVec d -> Prop) (point : QVec d) : Prop :=
  exists generated, ConeGen set generated /\ qvec_eq point generated.

Theorem periodic_ray_denominator_clearing : forall d
    (set : ZVec d -> Prop) point,
    Periodic set -> RayCone set point <-> ClearedCone set point.
Proof.
  intros d set point Hperiodic; split.
  - intros [coefficient [value [Hvalue Hpoint]]].
    destruct coefficient as [numerator denominator Hnumerator Hdenominator].
    exists denominator, (zvec_nsmul numerator value).
    repeat split; try assumption.
    + apply periodic_nsmul with (set := set); assumption.
    + intro index. transitivity
        ((q_of_nat numerator / q_of_nat denominator) *
          inject_Z (Vector.nth value index)).
      * apply Hpoint.
      * unfold cleared_point, qvec_scale, zvec_to_qvec, positive_value.
        rewrite nth_zvec_nsmul, inject_Z_mult.
        change ((q_of_nat numerator / q_of_nat denominator) *
          inject_Z (Vector.nth value index) ==
          / q_of_nat denominator *
          (q_of_nat numerator * inject_Z (Vector.nth value index))).
        field; apply q_of_nat_nonzero; assumption.
  - intros [denominator [value [Hdenominator [Hvalue Hpoint]]]].
    exists {| positive_num := 1; positive_den := denominator;
      positive_num_nonzero := Nat.lt_0_succ 0;
      positive_den_nonzero := Hdenominator |}, value.
    split; [exact Hvalue |]. intro index.
    transitivity (cleared_point denominator value index); [apply Hpoint |].
    unfold cleared_point, qvec_scale, positive_value.
    change (/ q_of_nat denominator * inject_Z (Vector.nth value index) ==
      (q_of_nat 1 / q_of_nat denominator) *
        inject_Z (Vector.nth value index)).
    setoid_rewrite q_of_nat_one.
    apply Qmult_comp; [symmetry; apply Qmult_1_l | reflexivity].
Qed.

Lemma cone_gen_cleared : forall d (set : ZVec d -> Prop) generated,
    Periodic set -> ConeGen set generated -> ClearedCone set generated.
Proof.
  intros d set generated Hperiodic Hcone; induction Hcone.
  - exists 1%nat, (zvec_zero d). repeat split.
    + lia.
    + exact (proj1 Hperiodic).
    + intro index. unfold qvec_zero, cleared_point, qvec_scale,
        zvec_to_qvec, zvec_zero.
      rewrite (const_nth Z 0%Z d index); reflexivity.
  - destruct IHHcone as [tail_den [tail_value
      [Htail_den [Htail_value Htail]]]].
    destruct coefficient as [numerator denominator].
    assert (Hnumerator : (0 <= numerator)%Z).
    { cbv [Qle] in H; cbn in H; lia. }
    set (numerator_nat := Z.to_nat numerator).
    set (denominator_nat := Pos.to_nat denominator).
    set (combined := zvec_add
      (zvec_nsmul (numerator_nat * tail_den) value)
      (zvec_nsmul denominator_nat tail_value)).
    exists (denominator_nat * tail_den)%nat, combined.
    repeat split.
    + pose proof (Pos2Nat.is_pos denominator); nia.
    + unfold combined. apply (proj2 Hperiodic).
      * apply periodic_nsmul with (set := set); assumption.
      * apply periodic_nsmul with (set := set); assumption.
    + intro index. unfold qvec_add, qvec_scale.
      transitivity
        ((inject_Z numerator / inject_Z (Z.pos denominator)) *
           inject_Z (Vector.nth value index) +
         (/ q_of_nat tail_den) * inject_Z (Vector.nth tail_value index)).
      * transitivity
          ((numerator # denominator) * inject_Z (Vector.nth value index) +
           (/ q_of_nat tail_den) * inject_Z (Vector.nth tail_value index)).
        -- apply Qplus_comp; [reflexivity | apply Htail].
        -- apply Qplus_comp; [|reflexivity].
           apply Qmult_comp; [apply Qmake_Qdiv | reflexivity].
      * unfold cleared_point, qvec_scale, zvec_to_qvec, combined, zvec_add.
        rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl).
        repeat rewrite nth_zvec_nsmul.
        rewrite inject_Z_plus.
        unfold numerator_nat, denominator_nat, q_of_nat.
        repeat rewrite Nat2Z.inj_mul.
        rewrite Z2Nat.id by exact Hnumerator.
        rewrite positive_nat_Z.
        repeat rewrite inject_Z_mult.
        field. split.
        -- apply q_of_nat_nonzero. exact Htail_den.
        -- change (~ inject_Z (Z.pos denominator) == 0).
           intros Hzero.
           apply (proj1 (inject_Z_injective (Z.pos denominator) 0%Z)) in Hzero.
           discriminate.
Qed.

Lemma cleared_cone_gen : forall d (set : ZVec d -> Prop) point,
    ClearedCone set point -> Cone set point.
Proof.
  intros d set point [denominator [value
    [Hdenominator [Hvalue Hpoint]]]].
  exists (qvec_add
    (qvec_scale (/ q_of_nat denominator) (zvec_to_qvec value))
    (qvec_zero d)). split.
  - constructor.
    + apply Qinv_le_0_compat.
      unfold q_of_nat, Qle; cbn; lia.
    + exact Hvalue.
    + constructor.
  - intro index. transitivity (cleared_point denominator value index).
    + apply Hpoint.
    + unfold cleared_point, qvec_add, qvec_scale, qvec_zero.
      symmetry; apply Qplus_0_r.
Qed.

Theorem periodic_standard_cone_denominator_clearing : forall d
    (set : ZVec d -> Prop) point,
    Periodic set -> Cone set point <-> ClearedCone set point.
Proof.
  intros d set point Hperiodic; split.
  - intros [generated [Hgenerated Hpoint]].
    destruct (cone_gen_cleared d set generated Hperiodic Hgenerated)
      as [denominator [value [Hd [Hv Hg]]]].
    exists denominator, value. repeat split; try assumption.
    intro index. transitivity (generated index); [apply Hpoint | apply Hg].
  - apply cleared_cone_gen.
Qed.

Definition Component (d : nat) := (ZVec d * (ZVec d -> Prop))%type.

Definition Decomposes {d} (set : ZVec d -> Prop)
    (components : list (Component d)) : Prop :=
  forall value, set value <->
    exists base period_set, List.In (base, period_set) components /\
    exists period, period_set period /\ value = zvec_add base period.

Definition StrictConeUnion {d} (components : list (Component d))
    (point : QVec d) : Prop :=
  qvec_eq point (qvec_zero d) \/
  exists base period_set,
    List.In (base, period_set) components /\
    exists coefficient remainder,
      ClearedCone period_set remainder /\
      qvec_eq point
        (qvec_add
          (qvec_scale (positive_value coefficient) (zvec_to_qvec base))
          remainder).

Lemma component_periodic : forall d (components : list (Component d))
    base period_set,
    List.Forall (fun component => Periodic (snd component)) components ->
    List.In (base, period_set) components -> Periodic period_set.
Proof.
  intros d components base period_set Hall Hin.
  rewrite List.Forall_forall in Hall. specialize (Hall _ Hin); exact Hall.
Qed.

Theorem cleared_cone_union_strict : forall d (set : ZVec d -> Prop)
    (components : list (Component d)),
    Periodic set ->
    List.Forall (fun component => Periodic (snd component)) components ->
    Decomposes set components ->
    forall point, ClearedCone set point <-> StrictConeUnion components point.
Proof.
  intros d set components Hset Hcomponents Hdecomposes point; split.
  - intros [denominator [value [Hdenominator [Hvalue Hpoint]]]].
    destruct (proj1 (Hdecomposes value) Hvalue)
      as [base [period_set [Hin [period [Hperiod Hvalue_eq]]]]].
    right. exists base, period_set. split; [exact Hin |].
    exists {| positive_num := 1; positive_den := denominator;
      positive_num_nonzero := Nat.lt_0_succ 0;
      positive_den_nonzero := Hdenominator |},
      (cleared_point denominator period).
    split.
    + exists denominator, period; repeat split; assumption || apply qvec_eq_refl.
    + intro index. transitivity (cleared_point denominator value index).
      * apply Hpoint.
      * subst value. unfold cleared_point, qvec_scale, qvec_add,
          positive_value, zvec_to_qvec, zvec_add.
        rewrite (nth_map2 Z.add base period index index index eq_refl eq_refl),
          inject_Z_plus.
        setoid_rewrite q_of_nat_one. setoid_rewrite Qmult_1_l.
        apply Qmult_plus_distr_r.
  - intros [Hzero | [base [period_set [Hin
      [coefficient [remainder [Hremainder Hpoint]]]]]]].
    + exists 1%nat, (zvec_zero d). repeat split.
      * lia.
      * exact (proj1 Hset).
      * intro index. transitivity (qvec_zero d index); [apply Hzero |].
        unfold qvec_zero, cleared_point, qvec_scale, zvec_to_qvec, zvec_zero.
        rewrite (const_nth Z 0%Z d index). reflexivity.
    + destruct coefficient as [numerator denominator Hnumerator Hdenominator].
      destruct Hremainder as [clear_den [period
        [Hclear_den [Hperiod Hremainder]]]].
      pose proof (component_periodic d components base period_set
        Hcomponents Hin) as Hperiodic.
      assert (Hbase : set base).
      { apply (proj2 (Hdecomposes base)). exists base, period_set.
        split; [exact Hin |]. exists (zvec_zero d). split.
        - exact (proj1 Hperiodic).
        - apply (proj1 (Vector.eq_nth_iff Z d _ _)).
          intros i j Hij; subst j. unfold zvec_add, zvec_zero.
          rewrite (nth_map2 Z.add base (Vector.const 0%Z d) i i i eq_refl eq_refl),
            (const_nth Z 0%Z d i). lia. }
      assert (Hshift : set (zvec_add base (zvec_nsmul denominator period))).
      { apply (proj2 (Hdecomposes _)). exists base, period_set.
        split; [exact Hin |]. exists (zvec_nsmul denominator period).
        split; [apply periodic_nsmul with (set := period_set); assumption |
          reflexivity]. }
      set (combined := zvec_add
        (zvec_nsmul (numerator * clear_den - 1) base)
        (zvec_add base (zvec_nsmul denominator period))).
      assert (Hcombined : set combined).
      { unfold combined. apply (proj2 Hset).
        - apply periodic_nsmul with (set := set); assumption.
        - exact Hshift. }
      exists (denominator * clear_den)%nat, combined.
      repeat split.
      * nia.
      * exact Hcombined.
      * intro index.
        transitivity
          ((q_of_nat numerator / q_of_nat denominator) *
             inject_Z (Vector.nth base index) + remainder index).
        -- apply Hpoint.
        -- transitivity
          ((q_of_nat numerator / q_of_nat denominator) *
             inject_Z (Vector.nth base index) +
           (/ q_of_nat clear_den) * inject_Z (Vector.nth period index)).
           ++ apply Qplus_comp; [reflexivity | apply Hremainder].
           ++ unfold cleared_point, qvec_scale, zvec_to_qvec, combined,
                zvec_add, q_of_nat.
              repeat rewrite (nth_map2 Z.add _ _ index index index
                eq_refl eq_refl).
              repeat rewrite nth_zvec_nsmul.
              repeat rewrite inject_Z_plus.
              repeat rewrite inject_Z_mult.
              assert (Hproduct :
                (Z.of_nat (numerator * clear_den - 1) + 1 =
                Z.of_nat (numerator * clear_den))%Z) by
                (rewrite Nat2Z.inj_sub, Nat2Z.inj_mul; nia).
              assert (HQproduct :
                inject_Z (Z.of_nat (numerator * clear_den - 1)) + 1 ==
                inject_Z (Z.of_nat numerator) *
                  inject_Z (Z.of_nat clear_den)).
              { change (inject_Z (Z.of_nat (numerator * clear_den - 1)) +
                    inject_Z 1%Z ==
                  inject_Z (Z.of_nat numerator) *
                    inject_Z (Z.of_nat clear_den)).
                rewrite <- inject_Z_plus, Hproduct, Nat2Z.inj_mul,
                  inject_Z_mult; reflexivity. }
              assert (Hinner :
                inject_Z (Z.of_nat (numerator * clear_den - 1)) *
                    inject_Z (Vector.nth base index) +
                  (inject_Z (Vector.nth base index) +
                   inject_Z (Z.of_nat denominator) *
                    inject_Z (Vector.nth period index)) ==
                (inject_Z (Z.of_nat numerator) *
                    inject_Z (Z.of_nat clear_den)) *
                    inject_Z (Vector.nth base index) +
                  inject_Z (Z.of_nat denominator) *
                    inject_Z (Vector.nth period index)).
              { setoid_rewrite <- HQproduct.
                setoid_rewrite Qmult_plus_distr_l.
                setoid_rewrite Qmult_1_l.
                apply Qplus_assoc. }
              rewrite Nat2Z.inj_mul, inject_Z_mult.
              transitivity
                (/ (inject_Z (Z.of_nat denominator) *
                    inject_Z (Z.of_nat clear_den)) *
                 ((inject_Z (Z.of_nat numerator) *
                    inject_Z (Z.of_nat clear_den)) *
                    inject_Z (Vector.nth base index) +
                  inject_Z (Z.of_nat denominator) *
                    inject_Z (Vector.nth period index))).
              { field. split; apply q_of_nat_nonzero; assumption. }
              apply Qmult_comp; [reflexivity | symmetry; exact Hinner].
Qed.

Theorem periodic_cone_union_strict : forall d (set : ZVec d -> Prop)
    (components : list (Component d)),
    Periodic set ->
    List.Forall (fun component => Periodic (snd component)) components ->
    Decomposes set components ->
    forall point, Cone set point <-> StrictConeUnion components point.
Proof.
  intros d set components Hset Hcomponents Hdecomposes point.
  transitivity (ClearedCone set point).
  - apply periodic_standard_cone_denominator_clearing; exact Hset.
  - apply cleared_cone_union_strict; assumption.
Qed.
