From Coq Require Import Arith.PeanoNat Lia Logic.ConstructiveEpsilon.

Section FiniteSearch.

Context {X : Type}.
Variable stage : X -> nat -> option bool.

Fixpoint search_fuel (x : X) (fuel : nat) : option bool :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match search_fuel x fuel' with
      | Some answer => Some answer
      | None => stage x fuel'
      end
  end.

Theorem search_fuel_sound : forall x fuel answer,
    search_fuel x fuel = Some answer ->
    exists n, n < fuel /\ stage x n = Some answer.
Proof.
  intros x fuel; induction fuel as [|fuel IH]; simpl.
  - discriminate.
  - destruct (search_fuel x fuel) as [earlier|] eqn:Hprefix.
    + intros answer Hanswer. inversion Hanswer; subst.
      destruct (IH answer eq_refl) as [n [Hlt Hstage]].
      exists n; split; [lia | exact Hstage].
    + destruct (stage x fuel) as [current|] eqn:Hstage; [|discriminate].
      intros answer Hanswer. inversion Hanswer; subst.
      exists fuel; split; [lia | exact Hstage].
Qed.

Theorem search_fuel_none : forall x fuel,
    search_fuel x fuel = None ->
    forall n, n < fuel -> stage x n = None.
Proof.
  intros x fuel; induction fuel as [|fuel IH]; simpl.
  - intros _ n Hlt; lia.
  - destruct (search_fuel x fuel) as [earlier|] eqn:Hprefix;
      [discriminate |].
    intros Hcurrent n Hlt.
    destruct (Nat.eq_dec n fuel) as [-> | Hneq].
    + exact Hcurrent.
    + apply (IH eq_refl n); lia.
Qed.

Theorem search_fuel_first : forall x fuel answer,
    search_fuel x fuel = Some answer ->
    exists n,
      n < fuel /\
      stage x n = Some answer /\
      forall m, m < n -> stage x m = None.
Proof.
  intros x fuel; induction fuel as [|fuel IH]; simpl.
  - discriminate.
  - destruct (search_fuel x fuel) as [earlier|] eqn:Hprefix.
    + intros answer Hanswer. inversion Hanswer; subst.
      destruct (IH answer eq_refl) as [n [Hlt [Hstage Hfirst]]].
      exists n; repeat split; try lia; assumption.
    + destruct (stage x fuel) as [current|] eqn:Hstage; [|discriminate].
      intros answer Hanswer. inversion Hanswer; subst.
      exists fuel; repeat split; try lia; try assumption.
      intros m Hlt. exact (search_fuel_none x fuel Hprefix m Hlt).
Qed.

Theorem search_fuel_eventually_hits : forall x n answer,
    stage x n = Some answer ->
    exists result, search_fuel x (S n) = Some result.
Proof.
  intros x n answer Hstage; simpl.
  destruct (search_fuel x n) as [earlier|] eqn:Hprefix.
  - exists earlier; reflexivity.
  - rewrite Hstage. exists answer; reflexivity.
Qed.

Definition stage_hit (x : X) (n : nat) : Prop := stage x n <> None.

Definition stage_hit_dec (x : X) (n : nat) :
    {stage_hit x n} + {~ stage_hit x n}.
Proof.
  unfold stage_hit.
  destruct (stage x n) as [answer|] eqn:Hstage.
  - left; discriminate.
  - right; intro H; apply H; reflexivity.
Defined.

Definition eventual_witness
    (eventual : forall x, exists n, stage_hit x n) (x : X) :
    {n : nat | stage_hit x n} :=
  @constructive_indefinite_ground_description_nat
    (stage_hit x) (stage_hit_dec x) (eventual x).

Definition stage_answer (x : X) (n : nat) (hit : stage_hit x n) :
    {answer : bool | stage x n = Some answer}.
Proof.
  destruct (stage x n) as [answer|] eqn:Hstage.
  - exists answer; reflexivity.
  - exfalso; exact (hit Hstage).
Defined.

Definition answer_at_hit (x : X) (witness : {n : nat | stage_hit x n}) : bool :=
  proj1_sig (stage_answer x (proj1_sig witness) (proj2_sig witness)).

Lemma answer_at_hit_spec : forall x witness,
    stage x (proj1_sig witness) = Some (answer_at_hit x witness).
Proof.
  intros x witness.
  exact (proj2_sig
    (stage_answer x (proj1_sig witness) (proj2_sig witness))).
Qed.

Definition search_of_eventual
    (eventual : forall x, exists n, stage x n <> None) (x : X) : bool :=
  answer_at_hit x (eventual_witness eventual x).

Theorem search_of_eventual_spec :
    forall (eventual : forall x, exists n, stage x n <> None) x,
    exists n, stage x n = Some (search_of_eventual eventual x).
Proof.
  intros eventual x.
  exists (proj1_sig (eventual_witness eventual x)).
  unfold search_of_eventual.
  apply answer_at_hit_spec.
Qed.

Theorem search_of_eventual_sound :
    forall (Correct : X -> bool -> Prop)
      (stage_sound : forall x n answer,
        stage x n = Some answer -> Correct x answer)
      (eventual : forall x, exists n, stage x n <> None) x,
    Correct x (search_of_eventual eventual x).
Proof.
  intros Correct stage_sound eventual x.
  destruct (search_of_eventual_spec eventual x) as [n Hstage].
  exact (stage_sound x n _ Hstage).
Qed.

End FiniteSearch.

Arguments search_fuel {X} stage x fuel.
Arguments search_of_eventual {X} stage eventual x.
