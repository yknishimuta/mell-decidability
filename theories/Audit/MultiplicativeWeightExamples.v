From Coq Require Import List ZArith.
From Mell.Logic Require Import Syntax Calculus MultiplicativeWeight.

Import ListNotations.

Check multiplicative_derivation_weight.
Check multiplicative_weight_refutes_sound.

Example multiplicative_weight_accepts_one_invariant :
  multiplicative_weight_refutes [One] = false.
Proof. reflexivity. Qed.

Example multiplicative_weight_refutes_two_ones :
  multiplicative_weight_refutes [One; One] = true.
Proof. reflexivity. Qed.

Example multiplicative_weight_refutes_empty :
  multiplicative_weight_refutes [] = true.
Proof. reflexivity. Qed.

Example multiplicative_weight_does_not_claim_exponential_fragment :
  multiplicative_weight_refutes [Bang One] = false.
Proof. reflexivity. Qed.

Print Assumptions multiplicative_derivation_weight.
Print Assumptions multiplicative_weight_refutes_sound.
