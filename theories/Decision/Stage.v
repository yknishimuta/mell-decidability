From Coq Require Import List Arith Lia Classical_Prop.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Certificates Code.
From Mell.Semilinear Require Import Presentation Code.
From Mell.Decision Require Import Invariant.

Fixpoint split_stage (stage : nat) : bool * nat :=
  match stage with
  | O => (true, 0)
  | S O => (false, 0)
  | S (S stage') =>
      let '(is_run, index) := split_stage stage' in
      (is_run, S index)
  end.

Lemma split_stage_two_step : forall stage,
    split_stage (S (S stage)) =
    let '(is_run, index) := split_stage stage in (is_run, S index).
Proof. reflexivity. Qed.

Lemma split_stage_even : forall index,
    split_stage (2 * index) = (true, index).
Proof.
  induction index as [|index IH].
  - reflexivity.
  - replace (2 * S index)%nat with (S (S (2 * index))) by lia.
    rewrite split_stage_two_step, IH. reflexivity.
Qed.

Lemma split_stage_odd : forall index,
    split_stage (2 * index + 1) = (false, index).
Proof.
  induction index as [|index IH].
  - reflexivity.
  - replace (2 * S index + 1)%nat with (S (S (2 * index + 1))) by lia.
    rewrite split_stage_two_step, IH. reflexivity.
Qed.

Definition bvas_stage {d} (S : IBVAS d) (target : NVec d)
    (stage : nat) : option bool :=
  let '(is_run, index) := split_stage stage in
  if is_run then
    match decode_run index with
    | Some run =>
        match eval_run S run with
        | Some value => if nvec_eq_dec value target then Some true else None
        | None => None
        end
    | None => None
    end
  else
    match decode_semi d index with
    | Some code => if check_invariantP S code target then Some false else None
    | None => None
    end.

Theorem bvas_stage_sound : forall d (S : IBVAS d) target stage answer,
    bvas_stage S target stage = Some answer ->
    if answer then Reach S target else ~ Reach S target.
Proof.
  intros d S target stage answer Hstage. unfold bvas_stage in Hstage.
  destruct (split_stage stage) as [is_run index]. destruct is_run.
  - destruct (decode_run index) as [run|] eqn:Hrun; [|discriminate].
    destruct (eval_run S run) as [value|] eqn:Heval; [|discriminate].
    destruct (nvec_eq_dec value target) as [Heq|Hneq]; [|discriminate].
    subst target. inversion Hstage; subst. simpl. eapply eval_run_sound; eauto.
  - destruct (decode_semi d index) as [code|] eqn:Hcode; [|discriminate].
    destruct (check_invariantP S code target) eqn:Hcheck; [|discriminate].
    inversion Hstage; subst. simpl. eapply check_invariant_sound; eauto.
Qed.

Lemma bvas_stage_reachable_hit : forall d (S : IBVAS d) target,
    Reach S target -> exists stage, bvas_stage S target stage = Some true.
Proof.
  intros d S target Hreach.
  destruct (eval_run_complete d S target Hreach) as [run Hrun].
  exists (2 * encode_run run). unfold bvas_stage.
  rewrite split_stage_even, decode_run_encode, Hrun.
  destruct (nvec_eq_dec target target); [reflexivity|contradiction].
Qed.

Lemma bvas_stage_invariant_hit : forall d (S : IBVAS d) target code,
    invariant_obligation S code target ->
    exists stage, bvas_stage S target stage = Some false.
Proof.
  intros d S target code Hinvariant.
  exists (2 * encode_semi code + 1). unfold bvas_stage.
  rewrite split_stage_odd, decode_semi_encode.
  apply check_invariantP_correct in Hinvariant. rewrite Hinvariant. reflexivity.
Qed.

Definition singleton_separator : Prop :=
  forall d (S : IBVAS d) target,
    ~ Reach S target ->
    exists code : SemiCode d, invariant_obligation S code target.

Theorem bvas_stage_eventual_of_separator :
    singleton_separator ->
    forall d (S : IBVAS d) target,
      exists stage, bvas_stage S target stage <> None.
Proof.
  intros Hseparator d S target.
  destruct (classic (Reach S target)) as [Hreach|Hunreachable].
  - destruct (bvas_stage_reachable_hit d S target Hreach) as [stage Hstage].
    exists stage. rewrite Hstage. discriminate.
  - destruct (Hseparator d S target Hunreachable) as [code Hinvariant].
    destruct (bvas_stage_invariant_hit d S target code Hinvariant)
      as [stage Hstage].
    exists stage. rewrite Hstage. discriminate.
Qed.
