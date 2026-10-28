From Coq Require Import Bool.
From Mell.Core Require Import Search Vector.
From Mell.BVAS Require Import System Runs.
From Mell.Decision Require Import Stage.

Definition bvas_instance (d : nat) : Type := (IBVAS d * NVec d)%type.

Definition bvas_instance_stage {d} (instance : bvas_instance d)
    (stage : nat) : option bool :=
  bvas_stage (fst instance) (snd instance) stage.

Definition bvas_decide_of_separator
    (separator : singleton_separator) {d}
    (S : IBVAS d) (target : NVec d) : bool :=
  search_of_eventual bvas_instance_stage
    (fun instance =>
      bvas_stage_eventual_of_separator separator d
        (fst instance) (snd instance))
    (S, target).

Theorem bvas_decide_of_separator_spec :
    forall (separator : singleton_separator) d (S : IBVAS d) target,
      exists stage,
        bvas_stage S target stage =
          Some (bvas_decide_of_separator separator S target).
Proof.
  intros separator d S target.
  unfold bvas_decide_of_separator.
  exact (search_of_eventual_spec bvas_instance_stage
    (fun instance =>
      bvas_stage_eventual_of_separator separator d
        (fst instance) (snd instance))
    (S, target)).
Qed.

Theorem bvas_decide_of_separator_sound :
    forall (separator : singleton_separator) d (S : IBVAS d) target,
      bvas_decide_of_separator separator S target = true ->
      Reach S target.
Proof.
  intros separator d S target Hanswer.
  destruct (bvas_decide_of_separator_spec separator d S target)
    as [stage Hstage].
  rewrite Hanswer in Hstage.
  exact (bvas_stage_sound d S target stage true Hstage).
Qed.

Theorem bvas_decide_of_separator_complete :
    forall (separator : singleton_separator) d (S : IBVAS d) target,
      Reach S target ->
      bvas_decide_of_separator separator S target = true.
Proof.
  intros separator d S target Hreach.
  destruct (bvas_decide_of_separator_spec separator d S target)
    as [stage Hstage].
  destruct (bvas_decide_of_separator separator S target) eqn:Hanswer;
    [reflexivity|].
  pose proof (bvas_stage_sound d S target stage false Hstage) as Hunreachable.
  simpl in Hunreachable. contradiction.
Qed.

Theorem bvas_decide_of_separator_correct :
    forall (separator : singleton_separator) d (S : IBVAS d) target,
      bvas_decide_of_separator separator S target = true <->
      Reach S target.
Proof.
  intros. split.
  - apply bvas_decide_of_separator_sound.
  - apply bvas_decide_of_separator_complete.
Qed.

Theorem bvas_decide_of_separator_false :
    forall (separator : singleton_separator) d (S : IBVAS d) target,
      bvas_decide_of_separator separator S target = false <->
      ~ Reach S target.
Proof.
  intros separator d S target. split.
  - intros Hfalse Hreach.
    apply bvas_decide_of_separator_complete with (separator := separator)
      in Hreach. congruence.
  - intros Hunreachable.
    destruct (bvas_decide_of_separator separator S target) eqn:Hanswer;
      [|reflexivity].
    exfalso. apply Hunreachable.
    eapply bvas_decide_of_separator_sound; eauto.
Qed.
