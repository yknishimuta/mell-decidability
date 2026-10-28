From Coq Require Import List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore
  RationalHToV LatticeGordanH LatticeGordanPullback.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.
Set Printing Implicit.

Check @F_Z.
Check @F_Q.
Check @F_Z_add.
Check @F_Z_scale.
Check @F_Q_of_Z.
Check @F_Q_add.
Check @F_Q_scale.
Check @F_Q_linear_combination.
Check @vcone_pullback_finitely_generated.

Definition pullback_q1 (q : Q) : QVec 1 := fun _ => q.
Definition pullback_z1 (z : Z) : ZVec 1 :=
  @Vector.cons Z z 0 (@Vector.nil Z).

Example pullback_empty_v_is_kernel :
    exists U : list (QVec 2),
      forall z : QVec 2,
        qcone_generated U z <->
        qcone_generated [] (F_Q [pullback_z1 1; pullback_z1 1] z).
Proof.
  apply (vcone_pullback_finitely_generated 1
    [pullback_z1 1; pullback_z1 1] (@List.nil (QVec 1))).
Qed.

Example pullback_empty_group :
    exists U : list (QVec 0),
      forall z : QVec 0,
        qcone_generated U z <->
        qcone_generated [pullback_q1 1] (F_Q [] z).
Proof.
  apply (vcone_pullback_finitely_generated 1 (@List.nil (ZVec 1))
    [pullback_q1 1]).
Qed.

Example pullback_lineality :
    exists U : list (QVec 1),
      forall z : QVec 1,
        qcone_generated U z <->
        qcone_generated [pullback_q1 1; pullback_q1 (-1)]
          (F_Q [pullback_z1 1] z).
Proof.
  apply (vcone_pullback_finitely_generated 1 [pullback_z1 1]
    [pullback_q1 1; pullback_q1 (-1)]).
Qed.

Definition kernel_coefficients : QVec 2 :=
  fun index => Fin.caseS' index (fun _ => Q) 1 (fun _ => -1).

Example pullback_empty_v_keeps_nonzero_kernel_point :
    qcone_generated (@List.nil (QVec 1))
      (F_Q [pullback_z1 1; pullback_z1 1] kernel_coefficients).
Proof.
  exists (qvec_zero 1). split; [constructor|].
  intro index. refine (Fin.caseS' index (fun index => _) _ _).
  - cbn [F_Q kernel_coefficients pullback_z1 qgroup_combination
      qvec_to_vector qvec_add qvec_scale qvec_zero zvec_to_qvec]. reflexivity.
  - intro impossible. inversion impossible.
Qed.

Example pullback_dimension_zero :
    exists U : list (QVec 0),
      forall z : QVec 0,
        qcone_generated U z <->
        qcone_generated (@List.nil (QVec 0)) (F_Q (@List.nil (ZVec 0)) z).
Proof.
  apply (vcone_pullback_finitely_generated 0 (@List.nil (ZVec 0))
    (@List.nil (QVec 0))).
Qed.

Example pullback_zero_map :
    exists U : list (QVec 1),
      forall z : QVec 1,
        qcone_generated U z <->
        qcone_generated [pullback_q1 0] (F_Q [pullback_z1 0] z).
Proof.
  apply (vcone_pullback_finitely_generated 1 [pullback_z1 0]
    [pullback_q1 0]).
Qed.

Example pullback_duplicate_dependent_generators :
    exists U : list (QVec 3),
      forall z : QVec 3,
        qcone_generated U z <->
        qcone_generated [pullback_q1 1; pullback_q1 1]
          (F_Q [pullback_z1 1; pullback_z1 2; pullback_z1 1] z).
Proof.
  apply (vcone_pullback_finitely_generated 1
    [pullback_z1 1; pullback_z1 2; pullback_z1 1]
    [pullback_q1 1; pullback_q1 1]).
Qed.

Print Assumptions vcone_pullback_finitely_generated.
