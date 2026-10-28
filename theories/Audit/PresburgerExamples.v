From Mell.Presburger Require Import Syntax Semantics QE Decide.

From Coq Require Import ZArith.

Open Scope Z_scope.

Definition successor_sentence : sentence :=
  close_sentence
    (Forall (Exists (Eq (Var 0) (Plus (Var 1) (Num 1)))))
    eq_refl.

Definition even_only_sentence : sentence :=
  close_sentence
    (Forall (Exists (Eq (Scale 2 (Var 0)) (Var 1))))
    eq_refl.

Definition parity_sentence : sentence :=
  close_sentence
    (Forall
      (Exists
        (Or
          (Eq (Var 1) (Scale 2 (Var 0)))
          (Eq (Var 1) (Plus (Scale 2 (Var 0)) (Num 1))))))
    eq_refl.

Definition contradictory_sentence : sentence :=
  close_sentence
    (Exists
      (ANd
        (Le (Num 0) (Var 0))
        (Eq (Var 0) (Num (-1)))))
    eq_refl.

Definition negative_integer_sentence : sentence :=
  close_sentence (Exists (Eq (Var 0) (Num (-1)))) eq_refl.

Fail Definition free_variable_sentence : sentence :=
  close_sentence (Eq (Var 0) (Num 0)) eq_refl.

Example successor_computes_true : presburger_decide successor_sentence = true.
Proof. reflexivity. Qed.

Example even_only_computes_false : presburger_decide even_only_sentence = false.
Proof. reflexivity. Qed.

Example parity_computes_true : presburger_decide parity_sentence = true.
Proof. reflexivity. Qed.

Example contradictory_computes_false :
    presburger_decide contradictory_sentence = false.
Proof. reflexivity. Qed.

Example negative_integer_computes_true :
    presburger_decide negative_integer_sentence = true.
Proof. reflexivity. Qed.

Example nested_negation_is_supported :
    presburger_decide
      (close_sentence
        (Not (Exists (Forall (Not (Eq (Var 0) (Var 0))))))
        eq_refl) = true.
Proof. reflexivity. Qed.

Check presburger_decide_correct.
Check sentence_environment_independent.
Print Assumptions presburger_decide_correct.

Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory "docs/review/extraction/presburger".
Separate Extraction presburger_decide.
