From Coq Require Import List.
From Mell.BVAS Require Import System Runs.
From Mell.Semilinear Require Import Closure.
From Mell.Separator Require Import SafetyWitness.
From Mell.Separator Require Import Main.
From Mell.Separator Require Import Singleton.

Import ListNotations.

Check initial_safety_witness_exists.
Check full_orthant_generated_iff_nonnegative.
Check terminal_safety_witness_invariant.
Check every_safety_witness_reaches_terminal.
Check separator_S.
Check singleton_complement_semilinear.
Check singleton_separator.

Print Assumptions initial_safety_witness_exists.
Print Assumptions terminal_safety_witness_invariant.
Print Assumptions every_safety_witness_reaches_terminal.
Print Assumptions separator_S.
Print Assumptions singleton_complement_semilinear.
Print Assumptions singleton_separator.

Example initial_safety_witness_dimension_zero :
  forall (system : IBVAS 0) (safe : NSet 0),
    Semilinear safe ->
    (forall value, Reach system value -> safe value) ->
    exists witness : SafetyWitness system safe,
      SameSet (witness_attractor witness) (fun _ => False).
Proof.
  intros system safe Hsafe Hreach.
  now apply initial_safety_witness_exists.
Qed.

Example singleton_complement_dimension_zero :
  forall target : Vector.NVec 0,
    Semilinear (fun value => value <> target).
Proof. exact (singleton_complement_semilinear 0). Qed.

Example separator_contract_dimension_zero :
  forall (system : IBVAS 0) (safe : NSet 0),
    Semilinear safe ->
    (forall value, Reach system value -> safe value) ->
    exists J : NSet 0,
      Semilinear J /\
      Invariant.InitialIncluded system J /\
      Invariant.Closed system J /\
      (forall value, J value -> safe value).
Proof. exact (separator_S 0). Qed.

Example terminal_empty_nodes_regression :
  forall d (system : IBVAS d) (safe : NSet d)
      (witness : SafetyWitness system safe),
    witness_nodes witness = [] ->
    Invariant.InitialIncluded system (witness_attractor witness) /\
    Invariant.Closed system (witness_attractor witness).
Proof.
  intros d system safe witness Hempty.
  destruct (terminal_safety_witness_invariant d system safe witness Hempty)
    as [_ [Hinitial [Hclosed _]]].
  now split.
Qed.

Example singleton_separator_dimension_zero :
  forall (system : IBVAS 0) (target : Vector.NVec 0),
    ~ Reach system target ->
    exists code : Presentation.SemiCode 0,
      Invariant.InitialIncluded system (Presentation.denote code) /\
      Invariant.Closed system (Presentation.denote code) /\
      ~ Presentation.denote code target.
Proof. exact (singleton_separator 0). Qed.
