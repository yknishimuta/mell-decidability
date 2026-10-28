From Coq Require Import Classical_Prop Fin Lia List Relations Relation_Operators
  RelationClasses Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import FaceOrder.

Import ListNotations.

Fixpoint finite_vertices (count : nat) : list (Fin.t count) :=
  match count with
  | 0 => []
  | S tail => Fin.F1 :: List.map Fin.FS (finite_vertices tail)
  end.

Lemma finite_vertices_complete : forall count (vertex : Fin.t count),
  List.In vertex (finite_vertices count).
Proof.
  intros count vertex. induction vertex.
  - cbn. now left.
  - cbn. right. now apply in_map.
Qed.

Section FiniteGraph.
Context {vertex : Type} (edge : vertex -> vertex -> Prop).

Inductive GraphReach (source : vertex) : vertex -> Prop :=
| graph_reach_refl : GraphReach source source
| graph_reach_step : forall middle target,
    GraphReach source middle -> edge middle target -> GraphReach source target.

Lemma graph_reach_edge : forall source target,
  edge source target -> GraphReach source target.
Proof. intros; eapply graph_reach_step; [constructor|assumption]. Qed.

Lemma graph_reach_trans : forall source middle target,
  GraphReach source middle -> GraphReach middle target ->
  GraphReach source target.
Proof.
  intros source middle target Hleft Hright. induction Hright.
  - exact Hleft.
  - eapply graph_reach_step; eauto.
Qed.

Definition SameSCC (left right : vertex) : Prop :=
  GraphReach left right /\ GraphReach right left.

Definition BottomSCCRoot (root : vertex) : Prop :=
  forall target, GraphReach root target -> GraphReach target root.

Definition StrictlyDownstream (left right : vertex) : Prop :=
  GraphReach left right /\ ~ GraphReach right left.

Lemma strictly_downstream_irreflexive : Irreflexive StrictlyDownstream.
Proof. intros value [_ Hnot]. apply Hnot. constructor. Qed.

Lemma strictly_downstream_transitive : Transitive StrictlyDownstream.
Proof.
  intros left middle right [Hlm Hnot_ml] [Hmr Hnot_rm]. split.
  - eapply graph_reach_trans; eauto.
  - intro Hrl. apply Hnot_rm. eapply graph_reach_trans; eauto.
Qed.

End FiniteGraph.

Theorem finite_graph_bottom_scc_exists : forall count
    (edge : Fin.t count -> Fin.t count -> Prop),
  count <> 0 ->
  exists root,
    BottomSCCRoot edge root.
Proof.
  intros count edge Hcount.
  assert (Hall_nonempty : finite_vertices count <> []).
  { intro Hempty. destruct count as [|count]; [contradiction|].
    pose proof (@finite_vertices_complete (S count) Fin.F1) as Hin.
    now rewrite Hempty in Hin. }
  destruct (finite_list_has_maximal (Fin.t count)
    (StrictlyDownstream edge)
    (strictly_downstream_irreflexive edge)
    (strictly_downstream_transitive edge)
    (finite_vertices count) Hall_nonempty) as
    [root [remaining [Hperm Hmaximal]]].
  exists root. intros target Hreachable.
  destruct (classic (GraphReach edge target root)) as [Hback|Hnotback];
    [exact Hback|].
  exfalso. apply (Hmaximal target).
  - assert (Hin : List.In target (finite_vertices count))
      by apply finite_vertices_complete.
    apply (Permutation_in target Hperm) in Hin.
    destruct Hin as [Heq|Hin]; [subst target; contradiction|exact Hin].
  - split; assumption.
Qed.

Definition BottomSCC {count} (edge : Fin.t count -> Fin.t count -> Prop)
    (root member : Fin.t count) : Prop :=
  SameSCC edge root member /\ BottomSCCRoot edge root.

Lemma bottom_scc_nonempty : forall count
    (edge : Fin.t count -> Fin.t count -> Prop) root,
  BottomSCCRoot edge root -> BottomSCC edge root root.
Proof. intros; split; [split; constructor|assumption]. Qed.

Lemma bottom_scc_closed : forall count
    (edge : Fin.t count -> Fin.t count -> Prop) root source target,
  BottomSCC edge root source -> edge source target ->
  BottomSCC edge root target.
Proof.
  intros count edge root source target [[Hrs Hsr] Hbottom] Hedge.
  assert (Hrt : GraphReach edge root target).
  { eapply graph_reach_step; eauto. }
  split; [split; [exact Hrt|now apply Hbottom]|exact Hbottom].
Qed.
