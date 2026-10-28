From Coq Require Import Fin Lia List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization ClosedLinearizationL2 Cone
  MathCompBridge Periodic QConeCore RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Set Printing Implicit.

Check @NonnegativeSet.
Check @qclosure_is_rational_cone.
Check @closed_linearization_periodic.
Check @closed_linearization_full.
Check @closed_linearization_finitely_generated.

Print NonnegativeSet.
Print FullPeriodic.
Print ClosedLinearization.

Definition l2_zero_periodic : ZSet 0 :=
  @zvec_generated 0 (@List.nil (ZVec 0)).

Example l2_dimension_zero_full :
    FullPeriodic (ClosedLinearization l2_zero_periodic).
Proof.
  apply closed_linearization_full, generated_periodic.
Qed.

Lemma l2_zero_periodic_nonnegative : NonnegativeSet l2_zero_periodic.
Proof.
  intros value _ index.
  exact (Fin.case0 (fun index => (0 <= Vector.nth value index)%Z) index).
Qed.

Lemma l2_zero_periodic_asymptotically_definable :
    AsymptoticallyDefinable l2_zero_periodic.
Proof.
  exists QFTop. split; [reflexivity|]. intro point. split.
  - intros _. exact I.
  - intros _. exists (qvec_zero 0). split; [constructor|].
    intro index.
    exact (Fin.case0
      (fun index => point index == qvec_zero 0 index) index).
Qed.

Example l2_dimension_zero_finitely_generated :
    FinitelyGeneratedPeriodic (ClosedLinearization l2_zero_periodic).
Proof.
  apply closed_linearization_finitely_generated.
  - apply generated_periodic.
  - exact l2_zero_periodic_nonnegative.
  - exact l2_zero_periodic_asymptotically_definable.
Qed.

Example l2_finite_generation_contract : forall d (set : ZSet d),
    Periodic set -> NonnegativeSet set -> AsymptoticallyDefinable set ->
    FinitelyGeneratedPeriodic (ClosedLinearization set).
Proof.
  exact closed_linearization_finitely_generated.
Qed.

Print Assumptions closed_linearization_full.
Print Assumptions closed_linearization_finitely_generated.
