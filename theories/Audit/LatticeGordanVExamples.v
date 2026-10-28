From Coq Require Import Lia List Vector ZArith QArith Qring.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore LatticeGordanV.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.
Set Printing Implicit.

Check @integer_points_vcone_finitely_generated.
Check @qcone_generated_aligned_coefficients.

Definition g1q (q : Q) : QVec 1 :=
  fun _ => q.

Example vcone_two_contains_one :
    qcone_generated [g1q 2]
      (zvec_to_qvec (@Vector.cons Z 1%Z 0 (@Vector.nil Z))).
Proof.
  exists (qvec_add (qvec_scale (1#2) (g1q 2)) (qvec_zero 1)). split.
  - eapply qcone_combination_add with
      (coefficient := (1#2)) (generator := g1q 2) (tail := qvec_zero 1).
    + unfold Qle; cbn; lia.
    + now left.
    + constructor.
  - intro index. refine (Fin.caseS' index (fun index => _) _ _); cbn.
    * unfold qvec_add, qvec_scale, qvec_zero, g1q, zvec_to_qvec. cbn. ring.
    * intro impossible. inversion impossible.
Qed.

Example vcone_opposite_generators :
    FinitelyGeneratedPeriodic
      (fun z : ZVec 1 =>
        qcone_generated [g1q 1; g1q (-1)] (zvec_to_qvec z)).
Proof. apply integer_points_vcone_finitely_generated. Qed.

Example vcone_dimension_zero :
    FinitelyGeneratedPeriodic
      (fun z : ZVec 0 =>
        qcone_generated [] (zvec_to_qvec z)).
Proof. apply integer_points_vcone_finitely_generated. Qed.

Example vcone_empty_generators :
    FinitelyGeneratedPeriodic
      (fun z : ZVec 1 => qcone_generated [] (zvec_to_qvec z)).
Proof. apply integer_points_vcone_finitely_generated. Qed.

Example vcone_zero_generator :
    FinitelyGeneratedPeriodic
      (fun z : ZVec 1 => qcone_generated [g1q 0] (zvec_to_qvec z)).
Proof. apply integer_points_vcone_finitely_generated. Qed.

Example vcone_negative_generator :
    FinitelyGeneratedPeriodic
      (fun z : ZVec 1 => qcone_generated [g1q (-1)] (zvec_to_qvec z)).
Proof. apply integer_points_vcone_finitely_generated. Qed.

Example vcone_noninteger_generator :
    FinitelyGeneratedPeriodic
      (fun z : ZVec 1 => qcone_generated [g1q (1#2)] (zvec_to_qvec z)).
Proof. apply integer_points_vcone_finitely_generated. Qed.

Example vcone_lineality :
    FinitelyGeneratedPeriodic
      (fun z : ZVec 1 =>
        qcone_generated [g1q (1#2); g1q (-1#3)] (zvec_to_qvec z)).
Proof. apply integer_points_vcone_finitely_generated. Qed.

Print Assumptions qcone_generated_aligned_coefficients.
Print Assumptions integer_points_vcone_finitely_generated.
