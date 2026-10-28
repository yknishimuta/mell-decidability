From Coq Require Import List.
From Mell.Logic Require Import Syntax.
From Mell.Audit Require Import DecisionPathAudit.

Import ListNotations.

Check traced_mell_decide_result.
Check decision_path_unit_guard.
Check decision_path_weight_guard.
Check decision_path_goal_saturation_guard.
Check decision_path_full_saturation_guard.
Check decision_path_fallback_guard.
Check traced_mell_decide_sound.
Check mell_fallback_stage_sound_true.
Check mell_fallback_stage_sound_false.
Check mell_fallback_stage_eventual.
Check mell_fallback_search_fuel_sound_true.
Check mell_fallback_search_fuel_sound_false.
Check mell_fallback_search_halts.
Check mell_fallback_decide_true_iff.
Check mell_fallback_decide_false_iff.
Check mell_fallback_decide_agrees.
Check mell_fallback_search_fuel_agrees.
Check Mell.Decision.MELL.mell_search_fuel_agrees.
Check Mell.Decision.MELL.mell_saturation_decide_sound.
Check Mell.Decision.MELL.mell_goal_saturation_decide_sound.
Check Mell.Decision.MELL.mell_full_saturation_decide_sound.
Check Mell.Decision.MELL.mell_search_halts.
Check Mell.Decision.Stage.bvas_stage_sound.
Check Mell.Decision.Stage.bvas_stage_reachable_hit.
Check Mell.Decision.Stage.bvas_stage_invariant_hit.

Example decision_path_unit_observed :
  mell_decision_path [One] = UnitPath.
Proof. reflexivity. Qed.

Example decision_path_weight_observed :
  mell_decision_path [] = WeightPath.
Proof. reflexivity. Qed.

Example decision_path_goal_saturation_observed :
  mell_decision_path [Atom 0; CoAtom 0] = GoalSaturationPath.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions traced_mell_decide_result.
Print Assumptions decision_path_unit_guard.
Print Assumptions decision_path_weight_guard.
Print Assumptions decision_path_goal_saturation_guard.
Print Assumptions decision_path_full_saturation_guard.
Print Assumptions decision_path_fallback_guard.
Print Assumptions traced_mell_decide_sound.
Print Assumptions mell_fallback_stage_sound_true.
Print Assumptions mell_fallback_stage_sound_false.
Print Assumptions mell_fallback_stage_eventual.
Print Assumptions mell_fallback_search_fuel_sound_true.
Print Assumptions mell_fallback_search_fuel_sound_false.
Print Assumptions mell_fallback_search_halts.
Print Assumptions mell_fallback_decide_true_iff.
Print Assumptions mell_fallback_decide_false_iff.
Print Assumptions mell_fallback_decide_agrees.
Print Assumptions mell_fallback_search_fuel_agrees.
Print Assumptions Mell.Logic.UnitFragment.unit_sequent_provableb_sound.
Print Assumptions Mell.Logic.MultiplicativeWeight.multiplicative_weight_refutes_sound.
Print Assumptions Mell.Decision.MELL.mell_goal_saturation_decide_sound.
Print Assumptions Mell.Decision.MELL.mell_full_saturation_decide_sound.
Print Assumptions Mell.Decision.MELL.mell_saturation_decide_sound.
Print Assumptions Mell.Decision.MELL.mell_search_fuel_sound_true.
Print Assumptions Mell.Decision.MELL.mell_search_fuel_sound_false.
Print Assumptions Mell.Decision.MELL.mell_search_fuel_agrees.
