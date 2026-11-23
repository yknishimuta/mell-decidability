From Mell.Decision Require Import BVAS MELL.

Check bvas_decide.
Check bvas_decide_true_iff.
Check bvas_decide_false_iff.
Check mell_decide.
Check mell_decide_true_iff.
Check mell_decide_false_iff.
Check mell_decide_with_cut.
Check mell_stage.
Check mell_stage_sound_true.
Check mell_stage_sound_false.
Check mell_search_fuel.
Check mell_search_fuel_sound_true.
Check mell_search_fuel_sound_false.
Check mell_search_halts.
Check mell_search_fuel_agrees.
Check decode_encode_sequent.
Check decide_code.
Check decide_code_correct.

Goal True. idtac "MELL_AUDIT_BEGIN proved_singleton_separator". exact I. Qed.
Print Assumptions proved_singleton_separator.
Goal True. idtac "MELL_AUDIT_END proved_singleton_separator". exact I. Qed.
Goal True. idtac "MELL_AUDIT_BEGIN bvas_decide_true_iff". exact I. Qed.
Print Assumptions bvas_decide_true_iff.
Goal True. idtac "MELL_AUDIT_END bvas_decide_true_iff". exact I. Qed.
Goal True. idtac "MELL_AUDIT_BEGIN bvas_decide_false_iff". exact I. Qed.
Print Assumptions bvas_decide_false_iff.
Goal True. idtac "MELL_AUDIT_END bvas_decide_false_iff". exact I. Qed.
Goal True. idtac "MELL_AUDIT_BEGIN mell_decide_true_iff". exact I. Qed.
Print Assumptions mell_decide_true_iff.
Goal True. idtac "MELL_AUDIT_END mell_decide_true_iff". exact I. Qed.
Goal True. idtac "MELL_AUDIT_BEGIN mell_decide_false_iff". exact I. Qed.
Print Assumptions mell_decide_false_iff.
Goal True. idtac "MELL_AUDIT_END mell_decide_false_iff". exact I. Qed.
Goal True. idtac "MELL_AUDIT_BEGIN mell_decide_with_cut". exact I. Qed.
Print Assumptions mell_decide_with_cut.
Goal True. idtac "MELL_AUDIT_END mell_decide_with_cut". exact I. Qed.
Goal True. idtac "MELL_AUDIT_BEGIN mell_search_halts". exact I. Qed.
Print Assumptions mell_search_halts.
Goal True. idtac "MELL_AUDIT_END mell_search_halts". exact I. Qed.
Goal True. idtac "MELL_AUDIT_BEGIN decide_code_correct". exact I. Qed.
Print Assumptions decide_code_correct.
Goal True. idtac "MELL_AUDIT_END decide_code_correct". exact I. Qed.
