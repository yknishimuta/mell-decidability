From Coq Require Import List.
From Mell.Logic Require Import Syntax UnitFragment.

Import ListNotations.

Example unit_fragment_one : unit_sequent_provableb [One] = true.
Proof. reflexivity. Qed.

Example unit_fragment_bang_one : unit_sequent_provableb [Bang One] = true.
Proof. reflexivity. Qed.

Example unit_fragment_nested :
  unit_sequent_provableb [Bang (Tensor One (Bang One))] = true.
Proof. reflexivity. Qed.

Example unit_fragment_rejects_empty : unit_sequent_provableb [] = false.
Proof. reflexivity. Qed.

Example unit_fragment_rejects_atoms :
  unit_sequent_provableb [Atom 0] = false.
Proof. reflexivity. Qed.

Check unit_formula_provableb_sound.
Check unit_sequent_provableb_sound.
Print Assumptions unit_formula_provableb_sound.
Print Assumptions unit_sequent_provableb_sound.
