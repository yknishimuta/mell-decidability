From Coq Require Import List Vector Bool Arith.Cantor.
From Mell.Core Require Import Code Vector.
From Mell.Logic Require Import Syntax Calculus Code YallaBridge.
From Mell.BVAS Require Import System.
From Mell.Reduction Require Import ILZ MELLToABVASS
  MELLToABVASSCompleteness ZeroTest Main.

Import ListNotations.

Check translate_mell.
Check mell_ilz_iff.
Check ilz_subformulas.
Check ilz_subformulas_sound.
Check ilz_subformulas_complete.
Check ilz_subformulas_nodup.
Check FullZeroBVASS.
Check FullZeroReach.
Check compile_ilz_machine.
Check ilz_machine_correct.
Check ilz_machine_fork_free.
Check remove_zero_tests_correct.
Check store_context_reach_frame.
Check layered_test_rule_shape.
Check remove_zero_tests_lower_zero_mut.
Check remove_zero_tests_backward.
Check ilz_plain_machine_correct.
Check reduce_mell_correct.
Check decode_reach_instance_encode.
Check reduce_mell_code_correct.
Check reduce_mell_many_one.

Example mell_ilz_one :
  ILZProvable (translate_mell [One]).
Proof.
  apply (proj1 (mell_ilz_iff [One])).
  constructor. constructor.
Qed.

Example reach_instance_code_round_trip_one :
  decode_reach_instance (encode_reach_instance (reduce_mell [One])) =
    Some (reduce_mell [One]).
Proof. apply decode_reach_instance_encode. Qed.

Example reduction_code_round_trip_identity :
  reduce_mell_code (encode_sequent [CoAtom 0; Atom 0]) =
    Some (encode_reach_instance (reduce_mell [CoAtom 0; Atom 0])).
Proof. apply reduce_mell_code_correct. Qed.

Example reduction_accepts_one : Holds (reduce_mell [One]).
Proof. apply (proj1 (reduce_mell_correct [One])), provable_one. Qed.

Example reduction_accepts_identity :
  Holds (reduce_mell [CoAtom 3; Atom 3]).
Proof. apply (proj1 (reduce_mell_correct [CoAtom 3; Atom 3])).
  apply provable_atom_identity.
Qed.

Example reduction_accepts_tensor_units :
  Holds (reduce_mell [Tensor One One]).
Proof.
  apply (proj1 (reduce_mell_correct [Tensor One One])). constructor.
  eapply tensor_rule with (Gamma := []) (Delta := []); constructor.
Qed.

Example reduction_accepts_par_identity :
  Holds (reduce_mell [Par (CoAtom 4) (Atom 4)]).
Proof.
  apply (proj1 (reduce_mell_correct [Par (CoAtom 4) (Atom 4)])). constructor.
  apply par_rule, identity_rule.
Qed.

Example reduction_accepts_promotion : Holds (reduce_mell [Bang One]).
Proof.
  apply (proj1 (reduce_mell_correct [Bang One])). constructor.
  exact (promotion_rule One [] one_rule).
Qed.

Example reduction_accepts_exponential_weakening :
  Holds (reduce_mell [WhyNot (Atom 7); One]).
Proof.
  apply (proj1 (reduce_mell_correct [WhyNot (Atom 7); One])). constructor.
  apply weakening_rule. constructor.
Qed.

Example reduction_accepts_exponential_contraction :
  Holds (reduce_mell [WhyNot (Atom 7); One]).
Proof.
  apply (proj1 (reduce_mell_correct [WhyNot (Atom 7); One])). constructor.
  apply contraction_rule. apply weakening_rule. apply weakening_rule. constructor.
Qed.

Example reduction_rejects_empty : ~ Holds (reduce_mell []).
Proof. intro H. apply not_provable_empty.
  now apply (proj2 (reduce_mell_correct [])).
Qed.

Example reduction_rejects_two_units : ~ Holds (reduce_mell [One; One]).
Proof. intro H. apply not_provable_two_ones.
  now apply (proj2 (reduce_mell_correct [One; One])).
Qed.

Example malformed_integer_tag_is_rejected :
  decode_integer (pair_encode nat_codec nat_codec (3, 7)) = None.
Proof. unfold decode_integer. now rewrite pair_decode_encode. Qed.

Example zero_positive_magnitude_is_rejected :
  decode_integer (pair_encode nat_codec nat_codec (1, 0)) = None.
Proof. unfold decode_integer. now rewrite pair_decode_encode. Qed.

Example zero_action_arity_is_rejected : forall d (offset : ZVec d),
  decode_action d (pair_encode nat_codec (zvector_codec d) (0, offset)) = None.
Proof. intros. unfold decode_action. now rewrite pair_decode_encode. Qed.

Definition empty_system_zero : IBVAS 0 :=
  {| initial_vectors := []; system_actions := [] |}.

Example malformed_instance_target_is_rejected :
  decode_reach_instance
    (Cantor.to_nat (0, Cantor.to_nat (encode_ibvas empty_system_zero, 1))) = None.
Proof.
  unfold decode_reach_instance. rewrite !Cantor.cancel_of_to,
    decode_ibvas_encode. reflexivity.
Qed.

Definition changing_zero_rule : FullZeroRule bool :=
  {| full_zero_source := false; full_zero_target := true |}.

Definition changing_zero_test : FullZeroBVASS 0 bool :=
  {| full_zero_leaves := [true];
     full_zero_unary_rules := [];
     full_zero_split_rules := [];
     full_zero_test_rules := [changing_zero_rule] |}.

Example changing_zero_test_reaches_source :
  FullZeroReach changing_zero_test false (@Vector.nil nat).
Proof.
  change (FullZeroReach changing_zero_test false (nvec_zero 0)).
  eapply full_zero_reach_test with (rule := changing_zero_rule).
  - now left.
  - constructor. now left.
Qed.

Example changing_zero_test_is_preserved :
  Stateful.SReach (remove_zero_tests Bool.bool_dec changing_zero_test)
    (zero_test_root_state Bool.bool_dec changing_zero_test false)
    (zero_test_root_counters changing_zero_test (@Vector.nil nat)).
Proof.
  assert (Hin : List.In false (full_zero_states changing_zero_test)).
  { cbn. auto. }
  apply (proj1 (remove_zero_tests_correct 0 bool Bool.bool_dec
    changing_zero_test false (@Vector.nil nat) Hin)).
  apply changing_zero_test_reaches_source.
Qed.

Example encoded_reduction_accepts_one :
  encoded_reachability (encode_reach_instance (reduce_mell [One])).
Proof. apply (proj1 (reduce_mell_many_one [One])), provable_one. Qed.

Print Assumptions ilz_plain_machine_correct.
Print Assumptions mell_ilz_iff.
Print Assumptions store_context_reach_frame.
Print Assumptions ilz_machine_correct.
Print Assumptions remove_zero_tests_correct.
Print Assumptions ilz_subformulas_sound.
Print Assumptions ilz_subformulas_complete.
Print Assumptions reduce_mell_correct.
Print Assumptions decode_reach_instance_encode.
Print Assumptions reduce_mell_code_correct.
Print Assumptions reduce_mell_many_one.
