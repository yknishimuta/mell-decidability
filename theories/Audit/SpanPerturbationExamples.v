From Coq Require Import Fin Lia List QArith Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import LatticeGordanH MathCompBridge QConeCore
  RationalSpan SpanPerturbation.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.
Set Printing Implicit.

Check @qspan_uniform_small_coefficients.

Definition UniformSmallCoefficients {d} (generators : list (ZVec d))
    (positive : Vector.t Q (length generators)) : Prop :=
  exists epsilon : Q,
    0 < epsilon /\
    forall w : QVec d,
      QSpan generators w ->
      (forall index : Fin.t d,
        - epsilon < w index /\ w index < epsilon) ->
      exists delta : Vector.t Q (length generators),
        QVecEq w (qgroup_combination generators delta) /\
        forall index : Fin.t (length generators),
          - Vector.nth positive index < Vector.nth delta index /\
          Vector.nth delta index < Vector.nth positive index.

Definition perturb_z1 (value : Z) : ZVec 1 :=
  @Vector.cons Z value 0 (@Vector.nil Z).

Definition perturb_z2 (first second : Z) : ZVec 2 :=
  @Vector.cons Z first 1
    (@Vector.cons Z second 0 (@Vector.nil Z)).

Example perturbation_dimension_zero :
    UniformSmallCoefficients ([] : list (ZVec 0)) (@Vector.nil Q).
Proof.
  apply qspan_uniform_small_coefficients. constructor.
Qed.

Example perturbation_empty_generators_dimension_one :
    UniformSmallCoefficients ([] : list (ZVec 1)) (@Vector.nil Q).
Proof.
  apply qspan_uniform_small_coefficients. constructor.
Qed.

Example perturbation_zero_generator :
    UniformSmallCoefficients [perturb_z1 0]
      (@Vector.cons Q 1 0 (@Vector.nil Q)).
Proof.
  apply qspan_uniform_small_coefficients. repeat constructor.
Qed.

Example perturbation_nonpointed_pair :
    UniformSmallCoefficients [perturb_z1 1; perturb_z1 (-1)]
      (@Vector.cons Q 1 1
        (@Vector.cons Q 1 0 (@Vector.nil Q))).
Proof.
  apply qspan_uniform_small_coefficients. repeat constructor.
Qed.

Example perturbation_rank_one_in_dimension_two :
    UniformSmallCoefficients [perturb_z2 1 0; perturb_z2 2 0]
      (@Vector.cons Q 1 1
        (@Vector.cons Q (1#2) 0 (@Vector.nil Q))).
Proof.
  apply qspan_uniform_small_coefficients. repeat constructor.
Qed.

Example perturbation_duplicate_more_than_dimension :
    UniformSmallCoefficients
      [perturb_z1 1; perturb_z1 1; perturb_z1 (-1)]
      (@Vector.cons Q 1 2
        (@Vector.cons Q 1 1
          (@Vector.cons Q 1 0 (@Vector.nil Q)))).
Proof.
  apply qspan_uniform_small_coefficients. repeat constructor.
Qed.

Example perturbation_tiny_positive_bound :
    UniformSmallCoefficients [perturb_z1 1]
      (@Vector.cons Q (1#1000000) 0 (@Vector.nil Q)).
Proof.
  apply qspan_uniform_small_coefficients. repeat constructor.
Qed.

Example perturbation_noncanonical_positive_bound :
    UniformSmallCoefficients [perturb_z1 1]
      (@Vector.cons Q (2#4) 0 (@Vector.nil Q)).
Proof.
  apply qspan_uniform_small_coefficients. repeat constructor.
Qed.

Example negative_direction_is_in_span :
    QSpan [perturb_z1 1] (fun _ => -(1#2)).
Proof.
  exists (@Vector.cons Q (-(1#2)) 0 (@Vector.nil Q)).
  intro index. refine (Fin.caseS' index (fun index => _) _ _).
  - change (-(1#2) == -(1#2) * inject_Z 1 + 0). ring.
  - intro tail_index. exact (Fin.case0 (fun index =>
      (fun _ : Fin.t 1 => -(1#2)) (Fin.FS index) ==
      qgroup_combination [perturb_z1 1]
        (@Vector.cons Q (-(1#2)) 0 (@Vector.nil Q)) (Fin.FS index))
      tail_index).
Qed.

Print qspan_uniform_small_coefficients.
Print Assumptions qspan_uniform_small_coefficients.
