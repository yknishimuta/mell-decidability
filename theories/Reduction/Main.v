From Coq Require Import List Vector ZArith Lia Arith.Cantor Classical_Prop.
From Mell.Core Require Import Vector Code.
From Mell.Logic Require Import Syntax Calculus Code.
From Mell.BVAS Require Import System Runs Code.
From Mell.BVASS Require Import Stateful.
From Mell.Reduction Require Import ILZ ILZRuntime MELLToABVASSRuntime
  MELLToABVASS
  MELLToABVASSCompleteness ZeroTest ZeroTestFree StateErasure.

Import ListNotations.
Module IF := Yalla.iformulas.

Definition ilz_machine_state_eq_dec : forall left right : ILZMachineState,
    {left = right} + {left <> right}.
Proof.
  decide equality;
    try apply Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec;
    apply list_eq_dec;
    apply Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec.
Defined.

Inductive ClosedTranslationShape : IF.iformula -> Prop :=
| closed_translation_var : forall atom,
    ClosedTranslationShape (IF.ivar atom)
| closed_translation_lmap : forall left right,
    ClosedTranslationShape (IF.ilmap left right).

Lemma close_ilz_context_shape : forall context conclusion,
  ClosedTranslationShape conclusion ->
  ClosedTranslationShape (close_ilz_context context conclusion).
Proof.
  induction context as [|head tail IH]; intros conclusion Hshape; cbn.
  - exact Hshape.
  - apply IH. constructor.
Qed.

Lemma translate_mell_root_shape : forall Gamma,
  ClosedTranslationShape (snd (translate_mell Gamma)).
Proof.
  intro Gamma. unfold translate_mell; cbn.
  apply close_ilz_context_shape. constructor.
Qed.

Lemma translate_mell_empty_support : forall Gamma,
  List.In [] (ilz_supports (translate_mell Gamma)).
Proof.
  intro Gamma. apply ilz_supports_complete.
  - constructor.
  - intros formula H. contradiction.
Qed.

Lemma translate_mell_root_unary_rule : forall Gamma,
  exists rule,
    List.In rule
      (full_zero_unary_rules (compile_ilz_machine (translate_mell Gamma))) /\
    unary_zero_source _ _ rule =
      ilz_machine_sequent [] (snd (translate_mell Gamma)).
Proof.
  intro Gamma.
  pose proof (translate_mell_empty_support Gamma) as Hsupport.
  pose proof (translate_mell_conclusion_in Gamma) as Hformula.
  pose proof (translate_mell_root_shape Gamma) as Hshape.
  unfold translate_mell in Hformula; cbn in Hformula.
  inversion Hshape as [atom|left right]; subst.
  - set (rule := mk_unary
      (ilz_machine_sequent [] (IF.ivar atom))
      (formula_remove (ilz_subformulas (translate_mell Gamma)) (IF.ivar atom))
      ilz_machine_leaf).
    exists rule. split.
    change (List.In rule
      (ilz_initial_rules (translate_mell Gamma) ++
       ilz_store_rules (translate_mell Gamma) ++
       ilz_logical_unary_rules (translate_mell Gamma) ++
       ilz_lmap_split_unary_rules (translate_mell Gamma))).
    apply in_or_app. left. unfold ilz_initial_rules.
    apply in_flat_map. exists []; split; [exact Hsupport|].
    apply in_flat_map. exists (IF.ivar atom). split;
      [rewrite H; exact Hformula|].
    cbn. now left.
    + unfold rule. cbn. f_equal. exact H.
  - set (rule := mk_unary
      (ilz_machine_sequent [] (IF.ilmap left right))
      (formula_add (ilz_subformulas (translate_mell Gamma)) left)
      (ilz_machine_sequent [] right)).
    exists rule. split.
    change (List.In rule
      (ilz_initial_rules (translate_mell Gamma) ++
       ilz_store_rules (translate_mell Gamma) ++
       ilz_logical_unary_rules (translate_mell Gamma) ++
       ilz_lmap_split_unary_rules (translate_mell Gamma))).
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    unfold ilz_logical_unary_rules.
    apply in_flat_map.
    exists (ilz_machine_sequent [] (IF.ilmap left right)). split.
    + apply ilz_sequent_state_in; [exact Hsupport|].
      rewrite H. exact Hformula.
    + apply in_flat_map. exists (IF.ilmap left right).
      split; [rewrite H; exact Hformula|]. cbn. now left.
    + unfold rule. cbn. f_equal. exact H.
Qed.

Lemma translate_mell_root_in_states : forall Gamma,
  List.In (ilz_machine_sequent [] (snd (translate_mell Gamma)))
    (full_zero_states (compile_ilz_machine (translate_mell Gamma))).
Proof.
  intro Gamma. destruct (translate_mell_root_unary_rule Gamma)
    as [rule [Hrule Hsource]].
  rewrite <- Hsource. now apply unary_zero_source_in_states with (rule := rule).
Qed.

Definition compile_ilz_runtime_goal (Gamma : sequent) :=
  Mell.Reduction.MELLToABVASSRuntime.compile_ilz_machine
    (Mell.Reduction.ILZRuntime.translate_mell_runtime Gamma).

Definition compile_ilz_plain (Gamma : sequent) :=
  remove_zero_tests ilz_machine_state_eq_dec
    (compile_ilz_runtime_goal Gamma).

Definition ilz_plain_root_state (Gamma : sequent) :=
  zero_test_root_state ilz_machine_state_eq_dec
    (compile_ilz_runtime_goal Gamma)
    (ilz_machine_sequent []
      (snd (Mell.Reduction.ILZRuntime.translate_mell_runtime Gamma))).

Definition ilz_plain_root_counters (Gamma : sequent) :=
  zero_test_root_counters (compile_ilz_runtime_goal Gamma)
    (nvec_zero (length
      (Mell.Reduction.ILZRuntime.runtime_ilz_subformulas
        (Mell.Reduction.ILZRuntime.translate_mell_runtime Gamma)))).

Theorem ilz_plain_machine_correct : forall Gamma,
  Provable Gamma <->
  SReach (compile_ilz_plain Gamma) (ilz_plain_root_state Gamma)
    (ilz_plain_root_counters Gamma).
Proof.
  intro Gamma. rewrite mell_ilz_iff, ilz_machine_correct.
  unfold ilz_machine_accepts, compile_ilz_plain,
    ilz_plain_root_state, ilz_plain_root_counters,
    compile_ilz_runtime_goal.
  apply remove_zero_tests_correct. apply translate_mell_root_in_states.
Qed.

Record ReachInstance : Type := {
  reach_dimension : nat;
  reach_system : IBVAS reach_dimension;
  reach_target : NVec reach_dimension
}.

Definition Holds (instance : ReachInstance) : Prop :=
  Reach (reach_system instance) (reach_target instance).

Definition erase_stateful_reach_instance {d q}
    (system : SBVAS d q) (state : Fin.t q) (counters : NVec d) :
    ReachInstance :=
  {| reach_dimension := d + q + length (stateful_rules system);
     reach_system := erase_states system;
     reach_target := encode_state_config system state counters |}.

Definition reduce_mell_reference (Gamma : sequent) : ReachInstance :=
  let system := compile_ilz_plain Gamma in
  erase_stateful_reach_instance system
    (ilz_plain_root_state Gamma) (ilz_plain_root_counters Gamma).

Theorem reduce_mell_reference_correct : forall Gamma : sequent,
  Provable Gamma <-> Holds (reduce_mell_reference Gamma).
Proof.
  intro Gamma. rewrite ilz_plain_machine_correct.
  change (SReach (compile_ilz_plain Gamma) (ilz_plain_root_state Gamma)
      (ilz_plain_root_counters Gamma) <->
    Reach (erase_states (compile_ilz_plain Gamma))
      (encode_state_config (compile_ilz_plain Gamma)
        (ilz_plain_root_state Gamma) (ilz_plain_root_counters Gamma))).
  apply erase_states_correct.
Qed.

Definition compile_ilz_direct (Gamma : sequent) :=
  direct_bottom_up ilz_machine_state_eq_dec (compile_ilz_runtime_goal Gamma).

Definition ilz_direct_root_state (Gamma : sequent) :=
  direct_root_state ilz_machine_state_eq_dec
    (compile_ilz_runtime_goal Gamma)
    (ilz_machine_sequent []
      (snd (Mell.Reduction.ILZRuntime.translate_mell_runtime Gamma))).

Definition ilz_direct_root_counters (Gamma : sequent) :=
  nvec_zero (length
    (Mell.Reduction.ILZRuntime.runtime_ilz_subformulas
      (Mell.Reduction.ILZRuntime.translate_mell_runtime Gamma))).

Theorem ilz_direct_machine_correct : forall Gamma,
  zero_test_freeb (compile_ilz_runtime_goal Gamma) = true ->
  (Provable Gamma <->
   SReach (compile_ilz_direct Gamma) (ilz_direct_root_state Gamma)
     (ilz_direct_root_counters Gamma)).
Proof.
  intros Gamma Hfree. rewrite mell_ilz_iff, ilz_machine_correct.
  unfold ilz_machine_accepts, compile_ilz_direct,
    ilz_direct_root_state, ilz_direct_root_counters,
    compile_ilz_runtime_goal.
  apply direct_zero_test_free_correct; [exact Hfree|].
  apply translate_mell_root_in_states.
Qed.

Definition reduce_mell_direct (Gamma : sequent) : ReachInstance :=
  let system := compile_ilz_direct Gamma in
  erase_stateful_reach_instance system
    (ilz_direct_root_state Gamma) (ilz_direct_root_counters Gamma).

Definition reduce_mell (Gamma : sequent) : ReachInstance :=
  let translated := Mell.Reduction.ILZRuntime.translate_mell_runtime Gamma in
  let machine :=
    Mell.Reduction.MELLToABVASSRuntime.compile_ilz_machine translated in
  let root := ilz_machine_sequent [] (snd translated) in
  match full_zero_test_rules machine with
  | [] =>
      let system := direct_bottom_up ilz_machine_state_eq_dec machine in
      erase_stateful_reach_instance system
        (direct_root_state ilz_machine_state_eq_dec machine root)
        (nvec_zero (length
          (Mell.Reduction.ILZRuntime.runtime_ilz_subformulas translated)))
  | _ :: _ =>
      let system := remove_zero_tests ilz_machine_state_eq_dec machine in
      erase_stateful_reach_instance system
        (zero_test_root_state ilz_machine_state_eq_dec machine root)
        (zero_test_root_counters machine
          (nvec_zero (length
            (Mell.Reduction.ILZRuntime.runtime_ilz_subformulas translated))))
  end.

Theorem reduce_mell_correct : forall Gamma : sequent,
  Provable Gamma <-> Holds (reduce_mell Gamma).
Proof.
  intro Gamma.
  destruct (full_zero_test_rules (compile_ilz_runtime_goal Gamma))
    as [|test tests] eqn:Htests.
  all: unfold compile_ilz_runtime_goal in Htests.
  - assert (Hreduce : reduce_mell Gamma = reduce_mell_direct Gamma).
    { unfold reduce_mell, reduce_mell_direct, compile_ilz_direct,
        ilz_direct_root_state, ilz_direct_root_counters,
        compile_ilz_runtime_goal.
      rewrite Htests. reflexivity. }
    rewrite Hreduce.
    rewrite (ilz_direct_machine_correct Gamma).
    + change (SReach (compile_ilz_direct Gamma) (ilz_direct_root_state Gamma)
        (ilz_direct_root_counters Gamma) <->
      Reach (erase_states (compile_ilz_direct Gamma))
        (encode_state_config (compile_ilz_direct Gamma)
          (ilz_direct_root_state Gamma) (ilz_direct_root_counters Gamma))).
      apply erase_states_correct.
    + unfold zero_test_freeb, compile_ilz_runtime_goal.
      rewrite Htests. reflexivity.
  - assert (Hreduce : reduce_mell Gamma = reduce_mell_reference Gamma).
    { unfold reduce_mell, reduce_mell_reference, compile_ilz_plain,
        ilz_plain_root_state, ilz_plain_root_counters,
        compile_ilz_runtime_goal.
      rewrite Htests. reflexivity. }
    rewrite Hreduce.
    apply reduce_mell_reference_correct.
Qed.

Theorem reduce_mell_optimized_correct_reference : forall Gamma,
  Holds (reduce_mell Gamma) <-> Holds (reduce_mell_reference Gamma).
Proof.
  intro Gamma. rewrite <- reduce_mell_correct,
    <- reduce_mell_reference_correct. reflexivity.
Qed.

(** A concrete Gödel coding of the generated plain reachability instance. *)
Definition integer_pair (value : Z) : nat * nat :=
  match value with
  | Z0 => (0, 0)
  | Zpos positive => (1, Pos.to_nat positive)
  | Zneg positive => (2, Pos.to_nat positive)
  end.

Definition integer_unpair (value : nat * nat) : option Z :=
  match value with
  | (0, 0) => Some 0%Z
  | (1, S magnitude) => Some (Z.of_nat (S magnitude))
  | (2, S magnitude) => Some (Z.opp (Z.of_nat (S magnitude)))
  | _ => None
  end.

Definition encode_integer (value : Z) : nat :=
  pair_encode nat_codec nat_codec (integer_pair value).

Definition decode_integer (code : nat) : option Z :=
  match pair_decode nat_codec nat_codec code with
  | Some value => integer_unpair value
  | None => None
  end.

Lemma integer_pair_cancel : forall value,
  integer_unpair (integer_pair value) = Some value.
Proof.
  intros [|positive|positive]; cbn; [reflexivity| |].
  - destruct (Pos.to_nat positive) eqn:Hmagnitude.
    + pose proof (Pos2Nat.is_pos positive). lia.
    + change (Some (Z.of_nat (S n)) = Some (Z.pos positive)).
      rewrite <- Hmagnitude, positive_nat_Z. reflexivity.
  - destruct (Pos.to_nat positive) eqn:Hmagnitude.
    + pose proof (Pos2Nat.is_pos positive). lia.
    + change (Some (Z.opp (Z.of_nat (S n))) = Some (Z.neg positive)).
      rewrite <- Hmagnitude, positive_nat_Z. reflexivity.
Qed.

Lemma decode_integer_encode : forall value,
  decode_integer (encode_integer value) = Some value.
Proof.
  intro value. unfold decode_integer, encode_integer.
  rewrite pair_decode_encode. apply integer_pair_cancel.
Qed.

Definition integer_codec : Codec Z :=
  {| encode := encode_integer;
     decode := decode_integer;
     decode_encode := decode_integer_encode |}.

Fixpoint encode_zvector {d} (value : ZVec d) : nat :=
  match value with
  | Vector.nil => 0
  | Vector.cons head tail =>
      S (Cantor.to_nat (encode integer_codec head, encode_zvector tail))
  end.

Fixpoint decode_zvector (d code : nat) : option (ZVec d) :=
  match d, code with
  | 0, 0 => Some (@Vector.nil Z)
  | 0, S _ => None
  | S d', 0 => None
  | S d', S packed =>
      let '(head_code, tail_code) := Cantor.of_nat packed in
      match decode integer_codec head_code, decode_zvector d' tail_code with
      | Some head, Some tail => Some (@Vector.cons Z head d' tail)
      | _, _ => None
      end
  end.

Lemma decode_zvector_encode : forall d (value : ZVec d),
  decode_zvector d (encode_zvector value) = Some value.
Proof.
  intros d value. induction value as [|head d tail IH].
  - reflexivity.
  - change (decode_zvector (S d)
      (S (Cantor.to_nat (encode integer_codec head, encode_zvector tail))) =
      Some (@Vector.cons Z head d tail)).
    cbn [decode_zvector].
    rewrite Cantor.cancel_of_to, decode_encode, IH. reflexivity.
Qed.

Definition zvector_codec (d : nat) : Codec (ZVec d) :=
  {| encode := @encode_zvector d;
     decode := decode_zvector d;
     decode_encode := decode_zvector_encode d |}.

Definition encode_action {d} (action : Action d) : nat :=
  pair_encode nat_codec (zvector_codec d)
    (action_arity action, action_offset action).

Definition decode_action (d code : nat) : option (Action d) :=
  match pair_decode nat_codec (zvector_codec d) code with
  | Some (arity, offset) =>
      match lt_dec 0 arity with
      | left positive => Some {| action_arity := arity;
          action_arity_positive := positive; action_offset := offset |}
      | right _ => None
      end
  | None => None
  end.

Lemma decode_action_encode : forall d (action : Action d),
  decode_action d (encode_action action) = Some action.
Proof.
  intros d [arity positive offset]. unfold decode_action, encode_action.
  rewrite pair_decode_encode. cbn.
  destruct (lt_dec 0 arity) as [proof|bad].
  - assert (proof = positive) by apply proof_irrelevance.
    subst proof. reflexivity.
  - contradiction.
Qed.

Definition action_codec (d : nat) : Codec (Action d) :=
  {| encode := @encode_action d;
     decode := decode_action d;
     decode_encode := decode_action_encode d |}.

Definition encode_ibvas {d} (system : IBVAS d) : nat :=
  pair_encode (list_codec (nvec_codec d)) (list_codec (action_codec d))
    (initial_vectors system, system_actions system).

Definition decode_ibvas (d code : nat) : option (IBVAS d) :=
  match pair_decode (list_codec (nvec_codec d))
      (list_codec (action_codec d)) code with
  | Some (initials, actions) => Some {| initial_vectors := initials;
      system_actions := actions |}
  | None => None
  end.

Lemma decode_ibvas_encode : forall d (system : IBVAS d),
  decode_ibvas d (encode_ibvas system) = Some system.
Proof.
  intros d [initials actions]. unfold decode_ibvas, encode_ibvas.
  rewrite pair_decode_encode. reflexivity.
Qed.

Definition encode_reach_instance (instance : ReachInstance) : nat :=
  Cantor.to_nat (reach_dimension instance,
    Cantor.to_nat (encode_ibvas (reach_system instance),
      encode_nvec (reach_target instance))).

Definition decode_reach_instance (code : nat) : option ReachInstance :=
  let '(dimension, payload) := Cantor.of_nat code in
  let '(system_code, target_code) := Cantor.of_nat payload in
  match decode_ibvas dimension system_code, decode_nvec dimension target_code with
  | Some system, Some target => Some {| reach_dimension := dimension;
      reach_system := system; reach_target := target |}
  | _, _ => None
  end.

Lemma decode_reach_instance_encode : forall instance,
  decode_reach_instance (encode_reach_instance instance) = Some instance.
Proof.
  intros [dimension system target]. unfold decode_reach_instance,
    encode_reach_instance. rewrite !Cantor.cancel_of_to,
    decode_ibvas_encode, decode_nvec_encode. reflexivity.
Qed.

Definition encoded_reachability (code : nat) : Prop :=
  exists instance, decode_reach_instance code = Some instance /\ Holds instance.

Definition reduce_mell_code (code : nat) : option nat :=
  match decode_sequent code with
  | Some Gamma => Some (encode_reach_instance (reduce_mell Gamma))
  | None => None
  end.

Theorem reduce_mell_code_correct : forall Gamma,
  reduce_mell_code (encode_sequent Gamma) =
    Some (encode_reach_instance (reduce_mell Gamma)).
Proof.
  intro Gamma. unfold reduce_mell_code. now rewrite decode_sequent_encode.
Qed.

Theorem reduce_mell_many_one : forall Gamma,
  Provable Gamma <->
  encoded_reachability (encode_reach_instance (reduce_mell Gamma)).
Proof.
  intro Gamma. rewrite reduce_mell_correct. split.
  - intro H. exists (reduce_mell Gamma). split;
      [apply decode_reach_instance_encode|exact H].
  - intros [instance [Hdecode Hholds]].
    rewrite decode_reach_instance_encode in Hdecode. inversion Hdecode; subst.
    exact Hholds.
Qed.
