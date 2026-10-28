From Coq Require Import List Vector.
From Mell.Core Require Import Vector.

Import ListNotations.

Definition LinearComponent (d : nat) := (NVec d * list (NVec d))%type.
Definition SemiCode (d : nat) := list (LinearComponent d).

Definition nvec_scale {d} (coefficient : nat) (value : NVec d) : NVec d :=
  Vector.map (Nat.mul coefficient) value.

Fixpoint weighted_sum {d} (coefficients : list nat)
    (periods : list (NVec d)) : option (NVec d) :=
  match coefficients, periods with
  | List.nil, List.nil => Some (nvec_zero d)
  | List.cons coefficient coefficients', List.cons period periods' =>
      match weighted_sum coefficients' periods' with
      | Some tail => Some (nvec_add (nvec_scale coefficient period) tail)
      | None => None
      end
  | _, _ => None
  end.

Definition linear_denote {d} (component : LinearComponent d)
    (value : NVec d) : Prop :=
  exists coefficients contribution,
    weighted_sum coefficients (snd component) = Some contribution /\
    value = nvec_add (fst component) contribution.

Definition denote {d} (code : SemiCode d) (value : NVec d) : Prop :=
  exists component, List.In component code /\ linear_denote component value.

Lemma denote_empty : forall d (value : NVec d),
    ~ denote (List.nil : SemiCode d) value.
Proof. intros d value [component [Hin _]]; exact Hin. Qed.

Lemma weighted_sum_empty : forall d,
    weighted_sum List.nil (List.nil : list (NVec d)) = Some (nvec_zero d).
Proof. reflexivity. Qed.
