From Mell.Core Require Import Search Vector.
From Mell.BVAS Require Import System Runs.
From Mell.Decision Require Import Invariant Stage BVASOfSeparator.
From Mell.Separator Require Import Singleton.

(** The separation theorem supplies exactly the negative certificates expected by
    the alternating executable search.  This lemma is deliberately transparent:
    it is a proof bridge, not a selector used by the extracted program. *)
Theorem proved_singleton_separator : Mell.Decision.Stage.singleton_separator.
Proof.
  intros d system target Hunreachable.
  destruct (Mell.Separator.Singleton.singleton_separator
    d system target Hunreachable) as [code [Hinitial [Hclosed Hexcluded]]].
  exists code. repeat split; assumption.
Qed.
Definition bvas_decide {d} (system : IBVAS d) (target : NVec d) : bool :=
  bvas_decide_of_separator proved_singleton_separator system target.

Theorem bvas_decide_true_iff : forall d (system : IBVAS d) target,
  bvas_decide system target = true <-> Reach system target.
Proof.
  intros. apply bvas_decide_of_separator_correct.
Qed.

Theorem bvas_decide_false_iff : forall d (system : IBVAS d) target,
  bvas_decide system target = false <-> ~ Reach system target.
Proof.
  intros. apply bvas_decide_of_separator_false.
Qed.

Definition bvas_search_fuel {d} (system : IBVAS d) (target : NVec d)
    (fuel : nat) : option bool :=
  search_fuel bvas_instance_stage (system, target) fuel.

Theorem bvas_search_fuel_sound : forall d (system : IBVAS d) target fuel answer,
  bvas_search_fuel system target fuel = Some answer ->
  if answer then Reach system target else ~ Reach system target.
Proof.
  intros d system target fuel answer Hfuel.
  unfold bvas_search_fuel in Hfuel.
  destruct (search_fuel_sound bvas_instance_stage (system, target)
    fuel answer Hfuel) as [stage [_ Hstage]].
  exact (bvas_stage_sound d system target stage answer Hstage).
Qed.

Theorem bvas_search_halts : forall d (system : IBVAS d) target,
  exists fuel answer, bvas_search_fuel system target fuel = Some answer.
Proof.
  intros d system target.
  destruct (bvas_stage_eventual_of_separator proved_singleton_separator
    d system target) as [stage Hstage].
  destruct (bvas_stage system target stage) as [answer|] eqn:Hanswer.
  - destruct (search_fuel_eventually_hits bvas_instance_stage
      (system, target) stage answer Hanswer) as [result Hresult].
    exists (S stage), result. exact Hresult.
  - exfalso. apply Hstage. reflexivity.
Qed.

Theorem bvas_decide_stage_spec : forall d (system : IBVAS d) target,
  exists stage,
    bvas_stage system target stage = Some (bvas_decide system target).
Proof.
  intros. apply bvas_decide_of_separator_spec.
Qed.
