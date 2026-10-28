From Coq Require Import List.
From Mell.Core Require Import Vector.
From Mell.VAS Require Import Transformer AsymptoticRelation.

Import ListNotations.

Record AlmostSemilinearNComponent (d : nat) := {
  AlmostBaseInput : NVec d;
  AlmostBaseOutput : NVec d;
  AlmostPeriodRelation : NRelation d
}.

Arguments AlmostBaseInput {d} _.
Arguments AlmostBaseOutput {d} _.
Arguments AlmostPeriodRelation {d} _ _ _.

Definition AlmostSemilinearNRelation {d} (relation : NRelation d) : Prop :=
  exists components : list (AlmostSemilinearNComponent d),
    List.Forall (fun component =>
      AsymptoticallyDefinableNRelation
        (AlmostPeriodRelation component)) components /\
    forall source target,
      relation source target <->
      exists component,
        List.In component components /\
        exists offset_input offset_output,
          AlmostPeriodRelation component offset_input offset_output /\
          source = nvec_add (AlmostBaseInput component) offset_input /\
          target = nvec_add (AlmostBaseOutput component) offset_output.

Lemma almost_semilinear_nrelation_congr : forall d (left right : NRelation d),
    (forall source target, left source target <-> right source target) ->
    AlmostSemilinearNRelation left -> AlmostSemilinearNRelation right.
Proof.
  intros d left right Heq [components [Hasym Hcomponents]].
  exists components. split; [exact Hasym|]. intros source target.
  rewrite <- Heq. apply Hcomponents.
Qed.

Theorem almost_semilinear_nrelation_finite_union : forall d
    (relations : list (NRelation d)),
    List.Forall AlmostSemilinearNRelation relations ->
    AlmostSemilinearNRelation
      (fun source target => exists relation,
        List.In relation relations /\ relation source target).
Proof.
  intros d relations Hrelations. induction Hrelations as
      [|relation relations Hrelation Hrelations IH].
  - exists []. split; [constructor|]. intros source target. cbn. split.
    + intros [relation [Hin _]]. contradiction.
    + intros [component [Hin _]]. contradiction.
  - destruct Hrelation as [head_components [Hhead_asym Hhead]].
    destruct IH as [tail_components [Htail_asym Htail]].
    exists (head_components ++ tail_components). split.
    + now apply List.Forall_app.
    + intros source target. split.
      * intros [selected [[Heq|Hin] Hselected]].
        -- subst selected. apply Hhead in Hselected.
           destruct Hselected as [component [Hin_component Hcomponent]].
           exists component. split; [apply in_or_app; now left|exact Hcomponent].
        -- assert (Hunion : exists selected_relation,
              List.In selected_relation relations /\
              selected_relation source target).
           { exists selected. now split. }
           apply Htail in Hunion.
           destruct Hunion as [component [Hin_component Hcomponent]].
           exists component. split; [apply in_or_app; now right|exact Hcomponent].
      * intros [component [Hin Hcomponent]]. apply in_app_or in Hin as [Hin|Hin].
        -- exists relation. split; [now left|]. apply Hhead.
           now exists component.
        -- assert (Hcomponent_union : exists selected_component,
              List.In selected_component tail_components /\
              exists offset_input offset_output,
                AlmostPeriodRelation selected_component offset_input offset_output /\
                source = nvec_add (AlmostBaseInput selected_component) offset_input /\
                target = nvec_add (AlmostBaseOutput selected_component) offset_output).
           { exists component. now split. }
           apply (proj2 (Htail source target)) in Hcomponent_union.
           destruct Hcomponent_union as [selected [Hin_selected Hselected]].
           exists selected. split; [now right|exact Hselected].
Qed.
