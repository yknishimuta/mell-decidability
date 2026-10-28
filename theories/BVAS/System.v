From Coq Require Import List Arith.PeanoNat.
From Mell.Core Require Import Vector.

Record Action (d : nat) : Type := {
  action_arity : nat;
  action_arity_positive : 0 < action_arity;
  action_offset : ZVec d
}.

Record IBVAS (d : nat) : Type := {
  initial_vectors : list (NVec d);
  system_actions : list (Action d)
}.

Arguments action_arity {d} _.
Arguments action_arity_positive {d} _.
Arguments action_offset {d} _.
Arguments initial_vectors {d} _.
Arguments system_actions {d} _.

Definition apply_action {d} (a : Action d)
    (children : list (NVec d)) : option (NVec d) :=
  if Nat.eqb (length children) (action_arity a)
  then add_displacement (action_offset a) children
  else None.
