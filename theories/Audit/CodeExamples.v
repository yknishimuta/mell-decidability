From Mell.Core Require Import Vector FiniteTree Code.
From Mell.Logic Require Import Syntax Code.
From Mell.BVAS Require Import Runs Code.
From Mell.Semilinear Require Import Presentation Code.

From Coq Require Import List Vector.

Import ListNotations.

Check decode_encode.
Check decode_sequent_encode.
Check decode_run_encode.
Check decode_semi_encode.

Definition v00 : NVec 2 := Vector.of_list [0; 0].
Definition v12 : NVec 2 := Vector.of_list [1; 2].
Definition v34 : NVec 2 := Vector.of_list [3; 4].

Example formula_code_is_not_reject_all :
    decode_formula (encode_formula (Tensor (Atom 7) (WhyNot One))) =
      Some (Tensor (Atom 7) (WhyNot One)).
Proof. apply decode_formula_encode. Qed.

Example sequent_round_trip :
    decode_sequent (encode_sequent [Bang (CoAtom 3); Bottom]) =
      Some [Bang (CoAtom 3); Bottom].
Proof. apply decode_sequent_encode. Qed.

Example invalid_formula_tree_is_rejected :
    decode_formula (tree_encode (tree_node 99 forest_nil)) = None.
Proof. reflexivity. Qed.

Example invalid_vector_length_is_rejected :
    decode_nvec 2 (list_encode nat_codec [7]) = None.
Proof. reflexivity. Qed.

Definition sample_run : RawRun :=
  tree_node 4 (forest_cons (tree_leaf 2)
    (forest_cons (tree_node 1 forest_nil) forest_nil)).

Example run_round_trip :
    decode_run (encode_run sample_run) = Some sample_run.
Proof. apply decode_run_encode. Qed.

Example empty_union_denotes_nothing : ~ denote ([] : SemiCode 2) v12.
Proof. apply denote_empty. Qed.

Example singleton_empty_periods_denotes_base :
    denote [(v12, [])] v12.
Proof.
  exists (v12, []); split; [now left |].
  exists [], v00; split; reflexivity.
Qed.

Example zero_period_is_allowed :
    denote [(v12, [v00])] v12.
Proof.
  exists (v12, [v00]); split; [now left |].
  exists [37], v00; split; reflexivity.
Qed.

Example duplicate_components_are_preserved :
    decode_semi 2 (encode_semi [(v12, [v34]); (v12, [v34])]) =
      Some [(v12, [v34]); (v12, [v34])].
Proof. apply decode_semi_encode. Qed.

Example dimension_zero_round_trip :
    decode_semi 0 (encode_semi [(@Vector.nil nat, [])]) =
      Some [(@Vector.nil nat, [])].
Proof. apply decode_semi_encode. Qed.

Eval compute in decode_formula (encode_formula (Par One Bottom)).
Eval compute in decode_nvec 2 (list_encode nat_codec [9]).
Eval compute in decode_run (encode_run sample_run).

Print Assumptions decode_sequent_encode.
Print Assumptions decode_nvec_encode.
Print Assumptions decode_run_encode.
Print Assumptions decode_semi_encode.
