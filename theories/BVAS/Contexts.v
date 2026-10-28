From Coq Require Import List Vector Lia.
From Mell.Core Require Import Vector FiniteTree.
From Mell.BVAS Require Import System Runs Certificates.

Inductive IRun (d : nat) : Type :=
| irun_leaf : NVec d -> IRun d
| irun_node : Action d -> IRuns d -> NVec d -> IRun d
with IRuns (d : nat) : Type :=
| iruns_nil : IRuns d
| iruns_cons : IRun d -> IRuns d -> IRuns d.

Arguments irun_leaf {d} _.
Arguments irun_node {d} _ _ _.
Arguments iruns_nil {d}.
Arguments iruns_cons {d} _ _.

Scheme IRun_ind' := Induction for IRun Sort Prop
with IRuns_ind' := Induction for IRuns Sort Prop.
Combined Scheme IRun_IRuns_ind from IRun_ind', IRuns_ind'.

Definition irun_target {d} (run : IRun d) : NVec d :=
  match run with
  | irun_leaf target => target
  | irun_node _ _ target => target
  end.

Fixpoint iruns_targets {d} (runs : IRuns d) : list (NVec d) :=
  match runs with
  | iruns_nil => List.nil
  | iruns_cons run runs' => irun_target run :: iruns_targets runs'
  end.

Fixpoint interpret_run {d} (S : IBVAS d) (raw : RawRun) : option (IRun d) :=
  match raw with
  | tree_leaf index =>
      match nth_error (initial_vectors S) index with
      | Some value => Some (irun_leaf value)
      | None => None
      end
  | tree_node index children =>
      match nth_error (system_actions S) index, interpret_runs S children with
      | Some action, Some runs =>
          match apply_action action (iruns_targets runs) with
          | Some value => Some (irun_node action runs value)
          | None => None
          end
      | _, _ => None
      end
  end
with interpret_runs {d} (S : IBVAS d) (raws : RawRuns) : option (IRuns d) :=
  match raws with
  | forest_nil => Some iruns_nil
  | forest_cons raw raws' =>
      match interpret_run S raw, interpret_runs S raws' with
      | Some run, Some runs => Some (iruns_cons run runs)
      | _, _ => None
      end
  end.

Inductive ValidIRun {d} (S : IBVAS d) : IRun d -> Prop :=
| valid_irun_leaf : forall value,
    List.In value (initial_vectors S) ->
    ValidIRun S (irun_leaf value)
| valid_irun_node : forall action children target,
    List.In action (system_actions S) ->
    ValidIRuns S children ->
    apply_action action (iruns_targets children) = Some target ->
    ValidIRun S (irun_node action children target)
with ValidIRuns {d} (S : IBVAS d) : IRuns d -> Prop :=
| valid_iruns_nil : ValidIRuns S iruns_nil
| valid_iruns_cons : forall run runs,
    ValidIRun S run -> ValidIRuns S runs ->
    ValidIRuns S (iruns_cons run runs).

Scheme ValidIRun_ind' := Induction for ValidIRun Sort Prop
with ValidIRuns_ind' := Induction for ValidIRuns Sort Prop.

Lemma interpret_run_eval : forall d (S : IBVAS d),
  (forall raw run, interpret_run S raw = Some run ->
    eval_run S raw = Some (irun_target run)) /\
  (forall raws runs, interpret_runs S raws = Some runs ->
    eval_runs S raws = Some (iruns_targets runs)).
Proof.
  intros d S. apply FiniteTree_FiniteForest_ind.
  - intros index run H. cbn in H |- *.
    destruct (nth_error (initial_vectors S) index); inversion H; reflexivity.
  - intros index children IH run H. cbn in H |- *.
    destruct (nth_error (system_actions S) index) as [action |]; [|discriminate].
    destruct (interpret_runs S children) as [runs |] eqn:Hruns; [|discriminate].
    destruct (apply_action action (iruns_targets runs)) as [value |] eqn:Happly;
      inversion H; subst.
    rewrite (IH runs eq_refl), Happly; reflexivity.
  - intros runs H; cbn in H |- *; inversion H; reflexivity.
  - intros raw IHraw raws IHraws runs H; cbn in H |- *.
    destruct (interpret_run S raw) as [run |] eqn:Hrun; [|discriminate].
    destruct (interpret_runs S raws) as [tail |] eqn:Htail; inversion H; subst.
    rewrite (IHraw run eq_refl), (IHraws tail eq_refl); reflexivity.
Qed.

Lemma interpret_run_valid : forall d (S : IBVAS d),
  (forall raw run, interpret_run S raw = Some run -> ValidIRun S run) /\
  (forall raws runs, interpret_runs S raws = Some runs -> ValidIRuns S runs).
Proof.
  intros d S. apply FiniteTree_FiniteForest_ind.
  - intros index run H. cbn in H.
    destruct (nth_error (initial_vectors S) index) as [value |] eqn:Hvalue;
      inversion H; subst.
    apply valid_irun_leaf. exact (nth_error_In _ _ Hvalue).
  - intros index children IH run H. cbn in H.
    destruct (nth_error (system_actions S) index) as [action |] eqn:Haction;
      [|discriminate].
    destruct (interpret_runs S children) as [runs |] eqn:Hruns; [|discriminate].
    destruct (apply_action action (iruns_targets runs)) as [value |] eqn:Happly;
      inversion H; subst.
    apply valid_irun_node.
    + exact (nth_error_In _ _ Haction).
    + exact (IH runs eq_refl).
    + exact Happly.
  - intros runs H; cbn in H; inversion H; constructor.
  - intros raw IHraw raws IHraws runs H; cbn in H.
    destruct (interpret_run S raw) as [run |] eqn:Hrun; [|discriminate].
    destruct (interpret_runs S raws) as [tail |] eqn:Htail; inversion H; subst.
    constructor; [exact (IHraw run eq_refl) | exact (IHraws tail eq_refl)].
Qed.

Fixpoint iruns_append {d} (left right : IRuns d) : IRuns d :=
  match left with
  | iruns_nil => right
  | iruns_cons run left' => iruns_cons run (iruns_append left' right)
  end.

Inductive IContext (d : nat) : Type :=
| context_hole : IContext d
| context_node : Action d -> IRuns d -> IContext d -> IRuns d -> NVec d ->
    IContext d.

Arguments context_hole {d}.
Arguments context_node {d} _ _ _ _ _.

Fixpoint context_plug {d} (context : IContext d) (run : IRun d) : IRun d :=
  match context with
  | context_hole => run
  | context_node action before inner after target =>
      irun_node action
        (iruns_append before
          (iruns_cons (context_plug inner run) after)) target
  end.

Fixpoint context_add {d} (delta : NVec d) (context : IContext d) : IContext d :=
  match context with
  | context_hole => context_hole
  | context_node action before inner after target =>
      context_node action before (context_add delta inner) after
        (nvec_add target delta)
  end.
