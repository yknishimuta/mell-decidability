From Coq Require Import Fin Lia List.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Contexts.
From Mell.Semilinear Require Import Closure.
From Mell.Separator Require Import Attractor DirectedRuns FiniteGraph.

Import ListNotations.

Definition WitnessVertex {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) := Fin.t (length nodes).

Definition witness_vertex_node {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system))
    (vertex : WitnessVertex nodes) (node : DirectedIRun system) : Prop :=
  nth_error nodes (proj1_sig (Fin.to_nat vertex)) = Some node.

Definition WitnessEdge {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system))
    (source target : WitnessVertex nodes) : Prop :=
  exists source_node target_node,
    witness_vertex_node nodes source source_node /\
    witness_vertex_node nodes target target_node /\
    DirectedIRunEdge source_node target_node.

Definition HomogeneousWitnessNodes {d} {system : IBVAS d}
    (nodes : list (DirectedIRun system)) : Prop :=
  forall left right left_node right_node,
    SameSCC (WitnessEdge nodes) left right ->
    witness_vertex_node nodes left left_node ->
    witness_vertex_node nodes right right_node ->
    SameSet (DirectedCone left_node) (DirectedCone right_node).

Record SafetyWitness {d} (system : IBVAS d) (safe : NSet d) : Type := {
  witness_safe_semilinear : Semilinear safe;
  witness_reach_safe : forall value, Reach system value -> safe value;
  witness_attractor : NSet d;
  witness_attractor_semilinear : Semilinear witness_attractor;
  witness_attractor_closed : Attractor system witness_attractor;
  witness_attractor_safe : forall value, witness_attractor value -> safe value;
  witness_nodes : list (DirectedIRun system);
  witness_nodes_homogeneous : HomogeneousWitnessNodes witness_nodes;
  witness_run_coverage : forall run,
    ValidIRun system run ->
    witness_attractor (irun_target run) \/
    exists node,
      List.In node witness_nodes /\ DirectedRunMember node run
}.

Arguments witness_attractor {d system safe} _ _.
Arguments witness_nodes {d system safe} _.

Lemma witness_nodes_nonzero_length : forall d (system : IBVAS d) safe
    (witness : SafetyWitness system safe),
  witness_nodes witness <> [] -> length (witness_nodes witness) <> 0.
Proof.
  intros d system safe witness Hnonempty Hzero.
  apply length_zero_iff_nil in Hzero. contradiction.
Qed.

Definition WitnessBottomSCC {d} {system : IBVAS d} {safe}
    (witness : SafetyWitness system safe)
    (root member : WitnessVertex (witness_nodes witness)) : Prop :=
  BottomSCC (WitnessEdge (witness_nodes witness)) root member.

Theorem safety_witness_bottom_scc_exists : forall d
    (system : IBVAS d) safe (witness : SafetyWitness system safe),
  witness_nodes witness <> [] ->
  exists root,
    BottomSCCRoot (WitnessEdge (witness_nodes witness)) root.
Proof.
  intros d system safe witness Hnonempty.
  apply finite_graph_bottom_scc_exists.
  now apply witness_nodes_nonzero_length.
Qed.

Lemma witness_vertex_node_exists : forall d (system : IBVAS d)
    (nodes : list (DirectedIRun system)) (vertex : WitnessVertex nodes),
  exists node, witness_vertex_node nodes vertex node.
Proof.
  intros d system nodes vertex.
  destruct (nth_error nodes (proj1_sig (Fin.to_nat vertex)))
    as [node|] eqn:Hnode.
  - now exists node.
  - apply nth_error_None in Hnode.
    assert (Hlt : proj1_sig (Fin.to_nat vertex) < length nodes).
    { exact (proj2_sig (Fin.to_nat vertex)). }
    lia.
Qed.

(** Closed-period equality along an SCC is established in [WitnessUpdate]
    by induction over graph paths, using Lemma 3.13 at each edge. *)
