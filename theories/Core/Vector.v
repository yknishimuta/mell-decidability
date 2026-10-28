From Coq Require Import List Vector ZArith Bool.

Import ListNotations.

Definition Vec (A : Type) (d : nat) := Vector.t A d.
Definition NVec (d : nat) := Vec nat d.
Definition ZVec (d : nat) := Vec Z d.

Definition nvec_zero (d : nat) : NVec d := Vector.const 0 d.
Definition zvec_zero (d : nat) : ZVec d := Vector.const 0%Z d.

Definition nvec_add {d} (x y : NVec d) : NVec d :=
  Vector.map2 Nat.add x y.

Definition zvec_add {d} (x y : ZVec d) : ZVec d :=
  Vector.map2 Z.add x y.

Definition nvec_to_zvec {d} (x : NVec d) : ZVec d :=
  Vector.map Z.of_nat x.

Definition zvec_nonnegative {d} (x : ZVec d) : bool :=
  forallb (fun z => Z.geb z 0) (Vector.to_list x).

Definition zvec_to_nvec {d} (x : ZVec d) : option (NVec d) :=
  if zvec_nonnegative x
  then Some (Vector.map Z.to_nat x)
  else None.

Definition nvec_sum {d} (xs : list (NVec d)) : NVec d :=
  List.fold_left nvec_add xs (nvec_zero d).

Definition add_displacement {d} (offset : ZVec d)
    (xs : list (NVec d)) : option (NVec d) :=
  zvec_to_nvec (zvec_add offset (nvec_to_zvec (nvec_sum xs))).

Definition nvec_eq_dec {d} : forall x y : NVec d, {x = y} + {x <> y}.
Proof.
  apply Vector.eq_dec with (A_beq := Nat.eqb).
  apply Nat.eqb_eq.
Defined.
