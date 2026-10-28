From Coq Require Import List QArith Qring Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Center CenterAbsorption
  CenterCharacterization ClosedLinearization ClosedLinearizationL2
  MathCompBridge Periodic RationalSpan.
From Mell.Order Require Import PeriodicOrder.

Open Scope Z_scope.
Open Scope Q_scope.

Theorem center_anchor : forall d (set : ZSet d),
    Periodic set ->
    exists anchor : ZVec d, set anchor /\ Center set anchor.
Proof.
  intros d set Hperiodic.
  destruct (finite_p_spanning d set Hperiodic) as
    [generators [Hgenerators Hspan]].
  set (anchor := zvec_rsum generators).
  assert (Hanchor : set anchor).
  { unfold anchor. now apply periodic_rsum. }
  exists anchor. split; [exact Hanchor|].
  apply (proj2 (center_characterization d set anchor Hperiodic)). split.
  - now apply periodic_member_in_difference.
  - exists generators. split; [exact Hgenerators|]. split.
    + exact Hspan.
    + exists (Vector.const 1 (length generators)). split.
      * apply vector_forall_const_positive. reflexivity.
      * eapply qvec_eq_trans with
          (y := qvec_scale 1 (zvec_to_qvec anchor)).
        -- intro index. unfold qvec_scale. ring.
        -- unfold anchor. apply qvec_eq_sym, qgroup_combination_const.
Qed.

Theorem closed_linearization_push_in_offset :
  forall d (set : ZSet d),
    Periodic set ->
    exists anchor : ZVec d,
      set anchor /\
      forall offset q : ZVec d,
        Difference set offset ->
        ClosedLinearization set q ->
        exists radius : nat, forall n : nat,
          set
            (zvec_add offset
              (zvec_nsmul (radius + n)%nat
                (zvec_add anchor q))).
Proof.
  intros d set Hperiodic.
  destruct (center_anchor d set Hperiodic) as
    [anchor [Hanchor Hcenter]].
  exists anchor. split; [exact Hanchor|].
  intros offset q Hoffset Hclosed.
  pose proof (center_add_closed_linearization d set anchor q
    Hperiodic Hcenter Hclosed) as Habsorbed.
  exact (Habsorbed offset Hoffset).
Qed.

Theorem closed_linearization_push_in :
  forall d (set : ZSet d),
    Periodic set -> NonnegativeSet set ->
    exists anchor : ZVec d, set anchor /\
      forall offset point : ZVec d,
        Difference set offset ->
        ClosedLinearization set (zvec_sub point anchor) ->
        exists radius : nat, forall n : nat,
          set (zvec_add offset (zvec_nsmul (radius + n)%nat point)).
Proof.
  intros d set Hperiodic _.
  destruct (closed_linearization_push_in_offset d set Hperiodic) as
    [anchor [Hanchor Htail]].
  exists anchor. split; [exact Hanchor|].
  intros offset point Hoffset Hclosed.
  destruct (Htail offset (zvec_sub point anchor) Hoffset Hclosed) as
    [radius Hradius].
  exists radius. intro n. specialize (Hradius n).
  rewrite zvec_sub_add_cancel in Hradius. exact Hradius.
Qed.
