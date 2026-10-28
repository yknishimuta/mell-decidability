From Coq Require Import List Vector ZArith.
From Mell.Core Require Import Vector.
From Mell.BVASS Require Import Stateful FiniteSaturation.

Import ListNotations.

Check saturation_configs.
Check saturation_decide.
Check saturation_decide_sound.

Definition saturation_d0_initial : SBVAS 0 1 :=
  {| initial_configs := [(Fin.F1, nvec_zero 0)];
     stateful_rules := [] |}.

Definition saturation_d0_empty : SBVAS 0 1 :=
  {| initial_configs := [];
     stateful_rules := [] |}.

Example saturation_initial_yes :
  saturation_decide saturation_d0_initial Fin.F1 (nvec_zero 0) 0 =
    Some true.
Proof. reflexivity. Qed.

Example saturation_empty_no :
  saturation_decide saturation_d0_empty Fin.F1 (nvec_zero 0) 1 =
    Some false.
Proof. reflexivity. Qed.

Print Assumptions saturation_decide_sound.
