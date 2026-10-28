From Coq Require Import Arith Fin Lia List Sorting.Permutation.
From Mell.Separator Require Import Attractor FiniteGraph SafetyWitness
  RankDecrease WitnessUpdate.

Import ListNotations.

(** Dimension zero still has the rank-zero component, ordered by [lt]. *)
Example safety_rank_dimension_zero : high_rank_less 0 0 1.
Proof. cbn. lia. Qed.

(** The lexicographic order is high-dimension first: arbitrarily many new
    lower-rank nodes do not mask removal of one rank-two node. *)
Example safety_rank_high_dimension_first :
  high_rank_less 2 (0, (100, 1000)) (1, (0, 0)).
Proof.
  cbn. apply Coq.Relations.Relation_Operators.left_slex. lia.
Qed.

(** In particular the total population may grow while the witness rank
    decreases. *)
Example safety_rank_can_decrease_while_size_grows :
  1100 > 1 /\ high_rank_less 2 (0, (100, 1000)) (1, (0, 0)).
Proof. split; [lia|apply safety_rank_high_dimension_first]. Qed.

Definition audit_single_edge (_ _ : Fin.t 1) : Prop := True.

Example safety_single_vertex_bottom_scc :
  BottomSCC audit_single_edge Fin.F1 Fin.F1.
Proof.
  apply bottom_scc_nonempty. intros target _.
  apply graph_reach_edge. exact I.
Qed.

Example safety_empty_vertex_boundary : finite_vertices 0 = [].
Proof. reflexivity. Qed.

Example safety_nonempty_vertex_boundary : finite_vertices 1 = [Fin.F1].
Proof. reflexivity. Qed.

(** The partition lemma acts on occurrences.  Thus duplicate values are
    retained by the permutation even though membership propositions do not
    distinguish them. *)
Example safety_partition_preserves_duplicate_occurrences :
  exists yes no : list nat,
    Permutation [7; 7; 8] (yes ++ no) /\
    count_occ Nat.eq_dec (yes ++ no) 7 = 2.
Proof.
  destruct (finite_predicate_partition_map nat nat [7; 7; 8]
    (fun value => value = 7) (fun value => value)) as
    [yes [no [Hpermutation _]]].
  cbn in Hpermutation.
  exists yes, no. split; [exact Hpermutation|].
  pose proof (proj1 (Permutation_count_occ Nat.eq_dec _ _) Hpermutation 7)
    as Hcount.
  cbn in Hcount. lia.
Qed.

Check Attractor.
Check lemma_3_7_attractor_extension.
Check SafetyWitness.
Check finite_graph_bottom_scc_exists.
Check witness_rank_less_well_founded.
Check lemma_7_2_safety_witness_successors.
Check lemma_7_3_attractor_contact_propagation.
Check lemma_7_4_directed_irun_rebase.
Check lemma_7_5_new_node_edge_direction.
Check lemma_7_1_safety_witness_rank_descent.

Print Assumptions lemma_7_1_safety_witness_rank_descent.
