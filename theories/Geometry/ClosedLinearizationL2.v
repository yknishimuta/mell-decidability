From Coq Require Import Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone
  LatticeGordanInterface LatticeGordanMain MathCompBridge Periodic QConeCore
  RationalClosure RationalConeAssembly RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Open Scope Z_scope.

Definition NonnegativeSet {d} (set : ZSet d) : Prop :=
  forall value, set value -> forall index, (0 <= Vector.nth value index)%Z.

Lemma qclosure_is_rational_cone : forall d (cone : QSet d),
    IsCone cone -> RationalCone (QClosure cone).
Proof.
  intros d cone Hcone. constructor.
  - now apply qclosure_is_cone.
  - intros left right Heq.
    now apply qclosure_qvec_extensional.
Qed.

Lemma closed_linearization_periodic : forall d (set : ZSet d),
    Periodic set -> Periodic (ClosedLinearization set).
Proof.
  intros d set Hperiodic. split.
  - split.
    + now apply difference_zero.
    + apply qclosure_extensive.
      apply cone_contains_source. exact (proj1 Hperiodic).
  - intros left right [Hleft_difference Hleft_closure]
      [Hright_difference Hright_closure]. split.
    + now apply difference_add.
    + apply (proj2 (qclosure_qvec_extensional d (Cone set)
        (zvec_to_qvec (zvec_add left right))
        (qvec_add (zvec_to_qvec left) (zvec_to_qvec right))
        (zvec_to_qvec_add d left right))).
      apply qclosure_add with (set := Cone set); try assumption.
      apply cone_is_cone.
Qed.

Theorem closed_linearization_full : forall d (set : ZSet d),
    Periodic set -> FullPeriodic (ClosedLinearization set).
Proof.
  intros d set Hperiodic. split.
  - now apply closed_linearization_periodic.
  - exists (Difference set), (QClosure (Cone set)). split.
    + now apply difference_is_integer_additive_group.
    + split.
      * apply qclosure_is_rational_cone, cone_is_cone.
      * intro value. reflexivity.
Qed.

Theorem closed_linearization_finitely_generated :
  forall d (set : ZSet d),
    Periodic set -> NonnegativeSet set -> AsymptoticallyDefinable set ->
    FinitelyGeneratedPeriodic (ClosedLinearization set).
Proof.
  intros d set Hperiodic _ Hasymptotic.
  unfold ClosedLinearization.
  apply lattice_gordan.
  - now apply difference_group_finitely_generated.
  - apply rational_closed_cone_is_polyhedral.
    + now apply qclosure_qdefinable.
    + apply qclosure_is_cone, cone_is_cone.
    + apply qclosure_topologically_closed.
Qed.
