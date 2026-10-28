From Coq Require Import List.
From Mell.Core Require Import Vector FiniteTree.
From Mell.BVAS Require Import System Runs.

Fixpoint eval_run {d} (S : IBVAS d) (r : RawRun) : option (NVec d) :=
  match r with
  | tree_leaf index => nth_error (initial_vectors S) index
  | tree_node index children =>
      match nth_error (system_actions S) index, eval_runs S children with
      | Some action, Some values => apply_action action values
      | _, _ => None
      end
  end
with eval_runs {d} (S : IBVAS d) (rs : RawRuns) :
    option (list (NVec d)) :=
  match rs with
  | forest_nil => Some nil
  | forest_cons r rs =>
      match eval_run S r, eval_runs S rs with
      | Some value, Some values => Some (value :: values)
      | _, _ => None
      end
  end.

Lemma eval_run_sound_mut : forall d (S : IBVAS d),
    (forall r value, eval_run S r = Some value -> Reach S value) /\
    (forall rs values, eval_runs S rs = Some values -> ReachChildren S values).
Proof.
  intros d S.
  apply (FiniteTree_FiniteForest_ind nat nat
    (fun r => forall value, eval_run S r = Some value -> Reach S value)
    (fun rs => forall values,
      eval_runs S rs = Some values -> ReachChildren S values)); simpl.
  - intros index value Hvalue.
    apply reach_initial with (index := index). exact Hvalue.
  - intros index children IH value Hvalue.
    destruct (nth_error (system_actions S) index) as [action|] eqn:Haction;
      [|discriminate].
    destruct (eval_runs S children) as [values|] eqn:Hvalues; [|discriminate].
    apply reach_action with (index := index) (action := action)
      (children := values).
    + exact Haction.
    + exact (IH values eq_refl).
    + exact Hvalue.
  - intros values Hvalues. inversion Hvalues. constructor.
  - intros r IHr rs IHrs output Houtput.
    destruct (eval_run S r) as [value|] eqn:Hvalue; [|discriminate].
    destruct (eval_runs S rs) as [values|] eqn:Hvalues; [|discriminate].
    inversion Houtput; subst.
    constructor.
    + exact (IHr value eq_refl).
    + exact (IHrs values eq_refl).
Qed.

Theorem eval_run_sound : forall d (S : IBVAS d) r value,
    eval_run S r = Some value -> Reach S value.
Proof.
  intros d S.
  exact (proj1 (eval_run_sound_mut d S)).
Qed.

Lemma eval_run_complete_mut : forall d (S : IBVAS d),
    (forall value, Reach S value ->
      exists r, eval_run S r = Some value) /\
    (forall values, ReachChildren S values ->
      exists rs, eval_runs S rs = Some values).
Proof.
  intros d S.
  apply (Reach_mutind d S
    (fun value _ => exists r, eval_run S r = Some value)
    (fun values _ => exists rs, eval_runs S rs = Some values)).
  - intros index value Hinitial.
    exists (tree_leaf index). exact Hinitial.
  - intros index action children value Haction reaches IHchildren Happly.
    destruct IHchildren as [rs Hrs].
    exists (tree_node index rs).
    simpl. rewrite Haction, Hrs. exact Happly.
  - exists forest_nil. reflexivity.
  - intros value values reach IHvalue reaches IHvalues.
    destruct IHvalue as [r Hr]. destruct IHvalues as [rs Hrs].
    exists (forest_cons r rs). simpl. rewrite Hr, Hrs. reflexivity.
Qed.

Theorem eval_run_complete : forall d (S : IBVAS d) value,
    Reach S value -> exists r, eval_run S r = Some value.
Proof.
  intros d S.
  exact (proj1 (eval_run_complete_mut d S)).
Qed.
