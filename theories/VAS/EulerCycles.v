From Coq Require Import Arith Fin Lia List Vector ZArith Sorting.Permutation
  Classical_Prop.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import RationalHToV.
From Mell.VAS Require Import Runs Intraproductions ProductionGraph
  ProductionGraphPaths GraphParikh Kirchhoff.

Import ListNotations.
Local Open Scope nat_scope.

Definition GraphPathIn {d} (graph : list (ProductionGraphEdge d))
    (source target : NVec d) (trace : list (ProductionGraphEdge d)) : Prop :=
  GraphEdgeTrace source target trace /\
  List.Forall (fun edge => List.In edge graph) trace.

Definition FiniteDirectedStronglyConnected {d}
    (states : list (NVec d)) (graph : list (ProductionGraphEdge d)) : Prop :=
  forall source target,
    List.In source states -> List.In target states ->
    exists trace, GraphPathIn graph source target trace.

Definition EdgeBagBalance {d} (bag : list (ProductionGraphEdge d)) : Prop :=
  forall state, TraceLeaves state bag = TraceEnters state bag.

Fixpoint remove_one_edge {d} (wanted : ProductionGraphEdge d)
    (bag : list (ProductionGraphEdge d)) : list (ProductionGraphEdge d) :=
  match bag with
  | [] => []
  | edge :: tail =>
      if production_graph_edge_eq_dec wanted edge
      then tail
      else edge :: remove_one_edge wanted tail
  end.

Definition EdgeEndpointsIn {d} (states : list (NVec d))
    (graph : list (ProductionGraphEdge d)) : Prop :=
  forall edge, List.In edge graph ->
    List.In (RunEdgeSource edge) states /\ List.In (RunEdgeTarget edge) states.

Definition TrailPartition {d} (bag : list (ProductionGraphEdge d))
    (source : NVec d) (trace : list (ProductionGraphEdge d))
    (target : NVec d) (rest : list (ProductionGraphEdge d)) : Prop :=
  GraphEdgeTrace source target trace /\ Permutation bag (trace ++ rest).

Lemma bounded_nat_predicate_maximum : forall (predicate : nat -> Prop) (bound : nat),
    (exists value, predicate value) ->
    (forall value, predicate value -> value <= bound) ->
    exists maximum,
      predicate maximum /\
      forall value, predicate value -> value <= maximum.
Proof.
  intros predicate bound. induction bound as [|bound IH]; intros Hex Hbound.
  - destruct Hex as [value Hvalue]. exists 0%nat. split.
    + assert (value = 0%nat) by (pose proof (Hbound value Hvalue); lia).
      now subst value.
    + intros candidate Hcandidate. pose proof (Hbound candidate Hcandidate). lia.
  - destruct (classic (predicate (S bound))) as [Htop|Htop].
    + exists (S bound). split; [exact Htop|intros; now apply Hbound].
    + apply IH; [exact Hex|]. intros value Hvalue.
      pose proof (Hbound value Hvalue) as Hle.
      destruct (Nat.eq_dec value (S bound)) as [->|Hne]; [contradiction|lia].
Qed.

Lemma trail_partition_length_bound : forall d bag source trace target rest,
    @TrailPartition d bag source trace target rest ->
    length trace <= length bag.
Proof.
  intros d bag source trace target rest [_ Hperm].
  apply Permutation_length in Hperm. rewrite app_length in Hperm. lia.
Qed.

Lemma maximal_trail_partition_exists : forall d bag source,
    exists trace target rest,
      @TrailPartition d bag source trace target rest /\
      forall longer other_target other_rest,
        TrailPartition bag source longer other_target other_rest ->
        length longer <= length trace.
Proof.
  intros d bag source.
  set (predicate := fun size => exists trace target rest,
    @TrailPartition d bag source trace target rest /\ length trace = size).
  assert (Hex : exists size, predicate size).
  { exists 0%nat, [], source, bag. split; [split; [constructor|reflexivity]|reflexivity]. }
  assert (Hbound : forall size, predicate size -> size <= length bag).
  { intros size [trace [target [rest [Hpartition <-]]]].
    now apply trail_partition_length_bound with (source := source)
      (target := target) (rest := rest). }
  destruct (bounded_nat_predicate_maximum predicate (length bag) Hex Hbound)
    as [maximum [[trace [target [rest [Hpartition Hlength]]]] Hmaximum]].
  exists trace, target, rest. split; [exact Hpartition|].
  intros longer other_target other_rest Hlonger. rewrite Hlength.
  apply Hmaximum. exists longer, other_target, other_rest. now split.
Qed.

Lemma trace_count_permutation : forall d left right state,
    @Permutation (ProductionGraphEdge d) left right ->
    TraceLeaves state left = TraceLeaves state right /\
    TraceEnters state left = TraceEnters state right.
Proof.
  intros d left right state Hperm. split; unfold TraceLeaves, TraceEnters;
    apply Permutation_count_occ; now apply Permutation_map.
Qed.

Lemma trace_count_app : forall d left right state,
    @TraceLeaves d state (left ++ right) =
      (TraceLeaves state left + TraceLeaves state right)%nat /\
    @TraceEnters d state (left ++ right) =
      (TraceEnters state left + TraceEnters state right)%nat.
Proof.
  intros; split; unfold TraceLeaves, TraceEnters; rewrite map_app, count_occ_app;
    reflexivity.
Qed.

Lemma graph_edge_trace_imbalance : forall d source target trace state,
    @GraphEdgeTrace d source target trace ->
    (TraceLeaves state trace +
      (if nvec_eq_dec target state then 1 else 0) =
     (if nvec_eq_dec source state then 1 else 0) +
      TraceEnters state trace)%nat.
Proof.
  intros d source target trace state Htrace.
  unfold TraceLeaves, TraceEnters.
  pose proof (graph_edge_trace_vertices d source target trace Htrace) as Hvertices.
  apply (f_equal (fun values => count_occ nvec_eq_dec values state)) in Hvertices.
  rewrite count_occ_app in Hvertices. cbn in Hvertices.
  destruct (nvec_eq_dec target state), (nvec_eq_dec source state);
    cbn in Hvertices; lia.
Qed.

Lemma positive_trace_leaves_has_edge : forall d state trace,
    (0 < @TraceLeaves d state trace)%nat ->
    exists edge prefix suffix,
      trace = prefix ++ edge :: suffix /\ RunEdgeSource edge = state.
Proof.
  intros d state trace Hpositive. unfold TraceLeaves in Hpositive.
  apply count_occ_In in Hpositive. apply in_map_iff in Hpositive.
  destruct Hpositive as [edge [Hsource Hin]]. apply in_split in Hin.
  destruct Hin as [prefix [suffix Heq]].
  exists edge, prefix, suffix. split; [exact Heq|exact Hsource].
Qed.

Lemma trail_partition_extend : forall d bag source trace target rest
    edge prefix suffix,
    @TrailPartition d bag source trace target rest ->
    rest = prefix ++ edge :: suffix ->
    RunEdgeSource edge = target ->
    TrailPartition bag source (trace ++ [edge]) (RunEdgeTarget edge)
      (prefix ++ suffix).
Proof.
  intros d bag source trace target rest edge prefix suffix
    [Htrace Hperm] Hrest Hsource. subst rest. split.
  - eapply graph_edge_trace_append; [exact Htrace|].
    rewrite <- Hsource. apply graph_edge_trace_singleton.
  - eapply Permutation_trans; [exact Hperm|].
    eapply Permutation_trans with
      (l' := trace ++ (edge :: prefix ++ suffix)).
    + exact (Permutation_app_head trace
        (Permutation_sym (Permutation_middle prefix suffix edge))).
    + replace ((trace ++ [edge]) ++ prefix ++ suffix)
        with (trace ++ edge :: prefix ++ suffix).
      * apply Permutation_refl.
      * repeat rewrite <- app_assoc. reflexivity.
Qed.

Lemma maximal_balanced_trail_is_cycle : forall d bag source trace target rest,
    @EdgeBagBalance d bag ->
    TrailPartition bag source trace target rest ->
    (forall longer other_target other_rest,
      TrailPartition bag source longer other_target other_rest ->
      length longer <= length trace) ->
    target = source.
Proof.
  intros d bag source trace target rest Hbalance Hpartition Hmax.
  destruct Hpartition as [Htrace Hperm].
  destruct (nvec_eq_dec target source) as [Heq|Hne]; [exact Heq|].
  exfalso.
  destruct (trace_count_permutation d bag (trace ++ rest) target Hperm)
    as [Hleaves_enters Henters_enters].
  destruct (trace_count_app d trace rest target) as [Hleave_app Henter_app].
  pose proof (graph_edge_trace_imbalance d source target trace target Htrace)
    as Hused.
  specialize (Hbalance target).
  destruct (nvec_eq_dec target target) as [_|Hbad]; [|contradiction].
  destruct (nvec_eq_dec source target) as [Hbad|_]; [congruence|].
  assert (Hpositive : (0 < TraceLeaves target rest)%nat) by lia.
  destruct (positive_trace_leaves_has_edge d target rest Hpositive)
    as [edge [prefix [suffix [Hrest Hsource]]]].
  pose proof (trail_partition_extend d bag source trace target rest edge prefix suffix
    (conj Htrace Hperm) Hrest Hsource) as Hextended.
  specialize (Hmax (trace ++ [edge]) (RunEdgeTarget edge) (prefix ++ suffix)
    Hextended). rewrite app_length in Hmax. cbn in Hmax. lia.
Qed.

Lemma balanced_bag_has_cycle_from_source : forall d bag source,
    @EdgeBagBalance d bag ->
    exists trace rest,
      GraphCycle trace source /\ Permutation bag (trace ++ rest).
Proof.
  intros d bag source Hbalance.
  destruct (maximal_trail_partition_exists d bag source)
    as [trace [target [rest [Hpartition Hmax]]]].
  assert (Heq : target = source).
  { eapply maximal_balanced_trail_is_cycle; eauto. }
  subst target.
  exists trace, rest. exact Hpartition.
Qed.

Definition VertexOccursInCycle {d} (root : NVec d)
    (trace : list (ProductionGraphEdge d)) (state : NVec d) : Prop :=
  state = root \/ List.In state (List.map RunEdgeTarget trace).

Lemma trace_edge_target_occurs : forall d root trace edge,
    List.In edge trace ->
    @VertexOccursInCycle d root trace (RunEdgeTarget edge).
Proof. intros; right; apply in_map; assumption. Qed.

Lemma graph_path_reaches_residual_source : forall d graph bag root trace rest target path,
    @GraphCycle d trace root ->
    GraphPathIn graph root target path ->
    (forall edge, List.In edge graph -> List.In edge bag) ->
    Permutation bag (trace ++ rest) ->
    (exists edge, List.In edge rest /\ RunEdgeSource edge = target) ->
    exists state edge,
      VertexOccursInCycle root trace state /\
      List.In edge rest /\ RunEdgeSource edge = state.
Proof.
  intros d graph bag root trace rest target path Hcycle [Hpath Hall]
    Hsupport Hperm [last [Hlast Hlastsource]].
  assert (Hscan : forall current destination suffix,
      GraphEdgeTrace current destination suffix ->
      List.Forall (fun edge => List.In edge graph) suffix ->
      VertexOccursInCycle root trace current ->
      (exists state edge,
        VertexOccursInCycle root trace state /\
        List.In edge rest /\ RunEdgeSource edge = state) \/
      VertexOccursInCycle root trace destination).
  { intros current destination suffix Hsuffix.
    induction Hsuffix; intros Hforall Hcurrent.
    - now right.
    - inversion Hforall; subst.
      destruct (in_dec production_graph_edge_eq_dec edge rest) as [Hinrest|Hnotrest].
      + left. exists (RunEdgeSource edge), edge. repeat split; assumption.
      + apply IHHsuffix; [assumption|].
        apply trace_edge_target_occurs with (edge := edge).
        pose proof (Hsupport edge H1) as HedgeBag.
        assert (HedgeParts : List.In edge (trace ++ rest)).
        { eapply Permutation_in; eauto. }
        apply in_app_or in HedgeParts. destruct HedgeParts;
          [assumption|contradiction]. }
  destruct (Hscan root target path Hpath Hall (or_introl eq_refl)) as [Hfound|Htarget];
    [exact Hfound|].
  exists target, last. repeat split; assumption.
Qed.

Lemma residual_of_cycle_balanced : forall d bag root trace rest,
    @EdgeBagBalance d bag -> GraphCycle trace root ->
    Permutation bag (trace ++ rest) -> EdgeBagBalance rest.
Proof.
  intros d bag root trace rest Hbag Hcycle Hperm state.
  destruct (trace_count_permutation d bag (trace ++ rest) state Hperm)
    as [Hleaves Henters].
  destruct (trace_count_app d trace rest state) as [Hleaveapp Henterapp].
  pose proof (graph_cycle_trace_balance d root trace state Hcycle) as Htrace.
  specialize (Hbag state). lia.
Qed.

Lemma permutation_remove_present : forall d (edge : ProductionGraphEdge d) bag,
    List.In edge bag ->
    Permutation (edge :: remove_one_edge edge bag) bag.
Proof.
  intros d edge bag. induction bag as [|head tail IH]; intros Hin; [contradiction|].
  cbn. destruct (production_graph_edge_eq_dec edge head) as [->|Hne].
  - apply Permutation_refl.
  - destruct Hin as [->|Hin]; [contradiction|].
    eapply Permutation_trans.
    + apply perm_swap.
    + constructor. now apply IH.
Qed.

Lemma balanced_bag_cycle_nonempty : forall d bag source edge,
    @EdgeBagBalance d bag -> List.In edge bag -> RunEdgeSource edge = source ->
    exists trace rest,
      GraphCycle trace source /\ Permutation bag (trace ++ rest) /\ trace <> [].
Proof.
  intros d bag source edge Hbalance Hedge Hsource.
  destruct (maximal_trail_partition_exists d bag source)
    as [trace [target [rest [Hpartition Hmax]]]].
  assert (Htarget : target = source).
  { eapply maximal_balanced_trail_is_cycle; eauto. }
  subst target. exists trace, rest. split; [exact (proj1 Hpartition)|]. split.
  - exact (proj2 Hpartition).
  - intro Hnil. subst trace.
    assert (Hsingle : TrailPartition bag source [edge] (RunEdgeTarget edge)
      (remove_one_edge edge bag)).
    { split.
      - rewrite <- Hsource. apply graph_edge_trace_singleton.
      - symmetry. now apply permutation_remove_present. }
    specialize (Hmax [edge] (RunEdgeTarget edge)
      (remove_one_edge edge bag) Hsingle). cbn in Hmax. lia.
Qed.

Lemma graph_cycle_splice_at_vertex : forall d root outer vertex inner,
    @GraphCycle d outer root -> GraphCycle inner vertex ->
    VertexOccursInCycle root outer vertex ->
    exists combined,
      GraphCycle combined root /\
      Permutation combined (outer ++ inner) /\
      length combined = (length outer + length inner)%nat.
Proof.
  intros d root outer vertex inner Houter Hinner [->|Hoccurs].
  - exists (inner ++ outer). split.
    + eapply graph_edge_trace_append; eauto.
    + split; [apply Permutation_app_comm|rewrite app_length; lia].
  - apply in_map_iff in Hoccurs as [edge [Htarget Hedge]].
    apply in_split in Hedge as [prefix [suffix Houtereq]]. subst outer.
    destruct (graph_edge_trace_split d root root prefix (edge :: suffix) Houter)
      as [middle [Hprefix Hrest]].
    inversion Hrest; subst.
    exists (prefix ++ (edge :: (inner ++ suffix))). split.
    + eapply graph_edge_trace_append; [exact Hprefix|].
      econstructor. eapply graph_edge_trace_append; eauto.
    + split.
      * rewrite <- app_assoc.
        exact (Permutation_app_head prefix
          (perm_skip edge (Permutation_app_comm inner suffix))).
      * repeat rewrite length_app. cbn. rewrite length_app.
        rewrite <- Nat.add_assoc. f_equal. cbn. f_equal. apply Nat.add_comm.
Qed.

Definition CyclePartition {d} (bag : list (ProductionGraphEdge d))
    (root : NVec d) (trace rest : list (ProductionGraphEdge d)) : Prop :=
  GraphCycle trace root /\ Permutation bag (trace ++ rest).

Lemma maximal_cycle_partition_exists : forall d bag root,
    exists trace rest,
      @CyclePartition d bag root trace rest /\
      forall longer other_rest,
        CyclePartition bag root longer other_rest ->
        length longer <= length trace.
Proof.
  intros d bag root.
  set (predicate := fun size => exists trace rest,
    @CyclePartition d bag root trace rest /\ length trace = size).
  assert (Hex : exists size, predicate size).
  { exists 0%nat, [], bag. split; [split; [constructor|reflexivity]|reflexivity]. }
  assert (Hbound : forall size, predicate size -> size <= length bag).
  { intros size [trace [rest [[_ Hperm] <-]]].
    apply Permutation_length in Hperm. rewrite app_length in Hperm. lia. }
  destruct (bounded_nat_predicate_maximum predicate (length bag) Hex Hbound)
    as [maximum [[trace [rest [Hpartition Hlength]]] Hmaximum]].
  exists trace, rest. split; [exact Hpartition|].
  intros longer other_rest Hlonger. rewrite Hlength. apply Hmaximum.
  exists longer, other_rest. now split.
Qed.

Lemma positive_kirchhoff_euler_bag_cycle : forall d states graph bag root,
    NoDup graph ->
    List.In root states ->
    EdgeEndpointsIn states graph ->
    FiniteDirectedStronglyConnected states graph ->
    (forall edge, List.In edge graph <-> List.In edge bag) ->
    @EdgeBagBalance d bag ->
    exists trace,
      GraphCycle trace root /\ Permutation trace bag.
Proof.
  intros d states graph bag root Hnodup Hroot Hendpoints Hstrong Hsupport Hbalance.
  destruct (maximal_cycle_partition_exists d bag root)
    as [trace [rest [[Hcycle Hperm] Hmax]]].
  destruct rest as [|residual resttail].
  - exists trace. split; [exact Hcycle|]. rewrite app_nil_r in Hperm.
    symmetry; exact Hperm.
  - exfalso.
    assert (Hresidual : List.In residual (residual :: resttail)) by now left.
    assert (Hresidual_graph : List.In residual graph).
    { apply Hsupport. eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
      apply in_or_app; now right. }
    destruct (Hendpoints residual Hresidual_graph) as [Hsrc _].
    destruct (Hstrong root (RunEdgeSource residual) Hroot Hsrc)
      as [path Hpath].
    destruct (graph_path_reaches_residual_source d graph bag root trace
      (residual :: resttail) (RunEdgeSource residual) path Hcycle Hpath
      (fun edge Hedge => (proj1 (Hsupport edge)) Hedge) Hperm
      (ex_intro _ residual (conj Hresidual eq_refl)))
      as [vertex [edge [Hvertex [Hedge Hsource]]]].
    assert (Hrestbalance : EdgeBagBalance (residual :: resttail)).
    { eapply residual_of_cycle_balanced; eauto. }
    destruct (balanced_bag_cycle_nonempty d (residual :: resttail) vertex edge
      Hrestbalance Hedge Hsource)
      as [inner [newrest [Hinner [Hinnerperm Hinnernonempty]]]].
    destruct (graph_cycle_splice_at_vertex d root trace vertex inner
      Hcycle Hinner Hvertex)
      as [combined [Hcombined [Hcombinedperm Hlength]]].
    assert (Hnewpartition : CyclePartition bag root combined newrest).
    { split; [exact Hcombined|].
      eapply Permutation_trans; [exact Hperm|].
      eapply Permutation_trans.
      - apply Permutation_app_head. exact Hinnerperm.
      - rewrite app_assoc. apply Permutation_app_tail.
        symmetry. exact Hcombinedperm. }
    specialize (Hmax combined newrest Hnewpartition). rewrite Hlength in Hmax.
    destruct inner; [contradiction|cbn in Hmax; lia].
Qed.

Definition ExpandEdgeWeights {d} (graph : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> nat) : list (ProductionGraphEdge d) :=
  List.flat_map (fun edge => List.repeat edge (weight edge)) graph.

Lemma count_occ_repeat_same : forall d count (edge : ProductionGraphEdge d),
    count_occ production_graph_edge_eq_dec (List.repeat edge count) edge = count.
Proof.
  intros d count; induction count as [|count IH]; intros edge; cbn; [reflexivity|].
  destruct (production_graph_edge_eq_dec edge edge); [now rewrite IH|contradiction].
Qed.

Lemma count_occ_repeat_different : forall d count
    (left right : ProductionGraphEdge d),
    left <> right ->
    count_occ production_graph_edge_eq_dec (List.repeat left count) right = 0%nat.
Proof.
  intros d count; induction count as [|count IH]; intros left right Hne;
    cbn; [reflexivity|].
  destruct (production_graph_edge_eq_dec left right); [contradiction|now apply IH].
Qed.

Lemma expand_edge_weights_parikh : forall d graph weight edge,
    NoDup graph -> List.In edge graph ->
    GraphEdgeParikh (@ExpandEdgeWeights d graph weight) edge = weight edge.
Proof.
  intros d graph; induction graph as [|head tail IH]; intros weight edge Hnodup Hin;
    [contradiction|].
  inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
  unfold ExpandEdgeWeights. cbn. unfold GraphEdgeParikh. rewrite count_occ_app.
  destruct Hin as [->|Hin].
  - rewrite count_occ_repeat_same.
    assert (Hzero : count_occ production_graph_edge_eq_dec
      (List.flat_map (fun candidate => List.repeat candidate (weight candidate)) tail)
      edge = 0%nat).
    { apply count_occ_not_In. rewrite in_flat_map. intros [candidate [Hcandidate Hinrepeat]].
      apply repeat_spec in Hinrepeat. subst candidate. contradiction. }
    rewrite Hzero. lia.
  - rewrite count_occ_repeat_different.
    + change (GraphEdgeParikh (ExpandEdgeWeights tail weight) edge = weight edge).
      now apply IH.
    + intro Heq; subst edge; contradiction.
Qed.

Lemma expand_edge_weights_support : forall d graph weight edge,
    NoDup graph ->
    (List.In edge (@ExpandEdgeWeights d graph weight) <->
     List.In edge graph /\ (0 < weight edge)%nat).
Proof.
  intros d graph weight edge Hnodup. split.
  - unfold ExpandEdgeWeights. rewrite in_flat_map.
    intros [candidate [Hin Hrepeat]].
    assert (Hpositive : (0 < weight candidate)%nat).
    { destruct (weight candidate); [cbn in Hrepeat; contradiction|lia]. }
    pose proof (repeat_spec _ _ _ Hrepeat) as Heq. subst candidate.
    now split.
  - intros [Hin Hpositive]. unfold ExpandEdgeWeights. rewrite in_flat_map.
    exists edge. split; [exact Hin|]. destruct (weight edge); [lia|].
    cbn. now left.
Qed.

Lemma expand_edge_weights_balanced : forall d graph weight,
    NoDup graph ->
    @KirchhoffBalanceNat d graph weight ->
    EdgeBagBalance (ExpandEdgeWeights graph weight).
Proof.
  intros d graph weight Hnodup Hbalance state.
  assert (Hsub : forall edge,
      List.In edge (ExpandEdgeWeights graph weight) -> List.In edge graph).
  { intros edge Hin. apply (proj1 (expand_edge_weights_support d graph weight edge
      Hnodup)) in Hin. exact (proj1 Hin). }
  rewrite <- (graph_weight_sum_parikh d graph (ExpandEdgeWeights graph weight)
      state Hnodup Hsub),
    <- (graph_weight_sum_parikh_enters d graph (ExpandEdgeWeights graph weight)
      state Hnodup Hsub).
  eapply eq_trans.
  - apply graph_weight_sum_nat_ext. intros edge Hin.
    now apply expand_edge_weights_parikh.
  - rewrite Hbalance. symmetry. apply graph_weight_sum_nat_ext.
    intros edge Hin. now apply expand_edge_weights_parikh.
Qed.

Lemma action_displacement_app : forall d (left right : list (ZVec d)),
    ActionDisplacement (left ++ right) =
      zvec_add (ActionDisplacement left) (ActionDisplacement right).
Proof.
  intros d left; induction left as [|action tail IH]; intro right; cbn.
  - apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index index' Heq; subst index'.
    unfold zvec_add, zvec_zero. rewrite (Vector.nth_map2 Z.add _ _ index index index
      eq_refl eq_refl), const_nth. lia.
  - rewrite IH. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros index index' Heq; subst index'. unfold zvec_add.
    repeat rewrite (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl).
    lia.
Qed.

Lemma action_displacement_repeat : forall d count (action : ZVec d),
    ActionDisplacement (List.repeat action count) = zvec_scale_nat count action.
Proof.
  intros d count; induction count as [|count IH]; intro action; cbn.
  - apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index index' Heq; subst index'.
    unfold zvec_zero. rewrite zvec_scale_nat_nth, const_nth. cbn. lia.
  - rewrite IH. apply (proj1 (Vector.eq_nth_iff Z d _ _)).
    intros index index' Heq; subst index'. unfold zvec_add.
    rewrite (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl),
      !zvec_scale_nat_nth. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma action_displacement_permutation : forall d left right,
    @Permutation (ZVec d) left right ->
    ActionDisplacement left = ActionDisplacement right.
Proof.
  intros d left right Hperm. induction Hperm; cbn; try congruence.
  - apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index index' Heq; subst index'.
    unfold zvec_add.
    repeat rewrite (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl).
    lia.
Qed.

Lemma kirchhoff_displacement_nat_expand : forall d graph weight,
    @KirchhoffDisplacementNat d graph weight =
      ActionDisplacement
        (List.map RunEdgeAction (ExpandEdgeWeights graph weight)).
Proof.
  intros d graph weight. unfold KirchhoffDisplacementNat, WeightedGraphActionWord.
  apply f_equal. induction graph as [|edge tail IH]; cbn; [reflexivity|].
  rewrite map_app, map_repeat, IH. reflexivity.
Qed.

Theorem graph_edge_parikh_displacement : forall d graph trace weight,
    NoDup graph ->
    (forall edge, List.In edge trace -> List.In edge graph) ->
    (forall edge, List.In edge graph -> GraphEdgeParikh trace edge = weight edge) ->
    @KirchhoffDisplacementNat d graph weight =
      ActionDisplacement (GraphTraceActionWord trace).
Proof.
  intros d graph trace weight Hnodup Hsub Hexact.
  assert (Hperm : Permutation trace (ExpandEdgeWeights graph weight)).
  { apply (proj2 (Permutation_count_occ production_graph_edge_eq_dec
      trace (ExpandEdgeWeights graph weight))). intro edge.
    destruct (in_dec production_graph_edge_eq_dec edge graph) as [Hin|Hnotin].
    - change (GraphEdgeParikh trace edge =
        GraphEdgeParikh (ExpandEdgeWeights graph weight) edge).
      rewrite (Hexact edge Hin).
      rewrite (expand_edge_weights_parikh d graph weight edge Hnodup Hin).
      reflexivity.
    - assert (Hnottrace : ~ List.In edge trace).
      { intro Hbad; apply Hnotin; now apply Hsub. }
      assert (Hnotexpand : ~ List.In edge (ExpandEdgeWeights graph weight)).
      { intro Hbad. apply expand_edge_weights_support in Hbad; tauto. }
      unfold GraphEdgeParikh.
      assert (Htracezero : count_occ production_graph_edge_eq_dec trace edge = 0%nat).
      { now apply count_occ_not_In. }
      assert (Hexpandzero : count_occ production_graph_edge_eq_dec
        (ExpandEdgeWeights graph weight) edge = 0%nat).
      { now apply count_occ_not_In. }
      now rewrite Htracezero, Hexpandzero. }
  rewrite kirchhoff_displacement_nat_expand.
  unfold GraphTraceActionWord.
  apply action_displacement_permutation. now apply Permutation_map.
Qed.

Theorem positive_kirchhoff_euler_total_cycle : forall d states graph root weight,
    NoDup graph ->
    List.In root states ->
    EdgeEndpointsIn states graph ->
    FiniteDirectedStronglyConnected states graph ->
    @KirchhoffBalanceNat d graph weight ->
    (forall edge, List.In edge graph -> (0 < weight edge)%nat) ->
    exists trace,
      GraphCycle trace root /\
      (forall edge, List.In edge trace -> List.In edge graph) /\
      TotalGraphCycle graph trace /\
      forall edge, List.In edge graph -> GraphEdgeParikh trace edge = weight edge.
Proof.
  intros d states graph root weight Hnodup Hroot Hendpoints Hstrong
    Hbalance Hpositive.
  set (bag := ExpandEdgeWeights graph weight).
  assert (Hsupport : forall edge, List.In edge graph <-> List.In edge bag).
  { intro edge. unfold bag. rewrite expand_edge_weights_support by exact Hnodup.
    split; [intro Hin; split; [exact Hin|now apply Hpositive]|tauto]. }
  assert (Hbgbalance : EdgeBagBalance bag).
  { unfold bag. now apply expand_edge_weights_balanced. }
  destruct (positive_kirchhoff_euler_bag_cycle d states graph bag root Hnodup
    Hroot Hendpoints Hstrong Hsupport Hbgbalance) as [trace [Hcycle Hperm]].
  exists trace. split; [exact Hcycle|]. split.
  - intros edge Hin. apply Hsupport.
    eapply Permutation_in; [exact Hperm|exact Hin].
  - split.
    + intros edge Hin. rewrite (graph_edge_parikh_permutation d trace bag Hperm edge).
      unfold bag. rewrite expand_edge_weights_parikh by assumption. now apply Hpositive.
    + intros edge Hin. rewrite (graph_edge_parikh_permutation d trace bag Hperm edge).
      unfold bag. now apply expand_edge_weights_parikh.
Qed.

Theorem production_graph_exact_nodup_edges : forall d system gamma witness,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    exists graph : list (ProductionGraphEdge d),
      NoDup graph /\
      forall source action target,
        ProductionGraphTransition system gamma witness source action target <->
        List.In {| RunEdgeSource := source;
                   RunEdgeAction := action;
                   RunEdgeTarget := target |} graph.
Proof.
  intros d system gamma witness Hvalid Hw.
  destruct (production_graph_transitions_finite d system gamma witness Hvalid Hw)
    as [transitions Htransitions].
  exists (nodup production_graph_edge_eq_dec transitions). split.
  - apply NoDup_nodup.
  - intros source action target. rewrite nodup_In. apply Htransitions.
Qed.

Theorem production_graph_positive_kirchhoff_realized : forall d system gamma witness
    graph weight,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    NoDup graph ->
    (forall source action target,
      ProductionGraphTransition system gamma witness source action target <->
      List.In {| RunEdgeSource := source;
                 RunEdgeAction := action;
                 RunEdgeTarget := target |} graph) ->
    KirchhoffBalanceNat graph weight ->
    (forall edge, List.In edge graph -> (0 < weight edge)%nat) ->
    exists trace,
      ProductionGraphEdgeTrace system gamma witness
        (ProductionGraphSpecialState gamma witness)
        (ProductionGraphSpecialState gamma witness) trace /\
      TotalGraphCycle graph trace /\
      forall edge, List.In edge graph -> GraphEdgeParikh trace edge = weight edge.
Proof.
  intros d system gamma witness graph weight Hvalid Hw Hnodup Hgraph
    Hbalance Hpositive.
  destruct (production_graph_states_finite d system gamma witness Hvalid Hw)
    as [states Hstates].
  assert (Hroot : List.In (ProductionGraphSpecialState gamma witness) states).
  { apply Hstates. apply production_graph_special_state_member. }
  assert (Hendpoints : EdgeEndpointsIn states graph).
  { intros edge Hin. destruct edge as [source action target]. cbn in *.
    apply <- Hgraph in Hin.
    destruct (production_graph_transition_states d system gamma witness
      source action target Hin) as [Hs Ht]. split; now apply Hstates. }
  assert (Hstrong : FiniteDirectedStronglyConnected states graph).
  { intros source target Hsource Htarget.
    apply <- Hstates in Hsource. apply <- Hstates in Htarget.
    destruct (corollary_5_10_production_graph_strongly_connected d system gamma
      witness source target Hvalid Hw Hsource Htarget) as [word Hpath].
    destruct (production_graph_path_has_edge_trace d system gamma witness
      source target word Hpath) as [trace [[Htrace Hall] _]].
    exists trace. split; [exact Htrace|].
    eapply List.Forall_impl; [|exact Hall]. intros edge Hedge.
    destruct edge as [edge_source edge_action edge_target]. cbn in *.
    now apply Hgraph. }
  destruct (positive_kirchhoff_euler_total_cycle d states graph
    (ProductionGraphSpecialState gamma witness) weight Hnodup Hroot Hendpoints
    Hstrong Hbalance Hpositive)
    as [trace [Hcycle [Htracegraph [Htotal Hexact]]]].
  exists trace. split; [split|].
  - exact Hcycle.
  - apply List.Forall_forall. intros edge Hin.
    destruct edge as [source action target]. cbn in *.
    apply (proj2 (Hgraph source action target)). now apply Htracegraph.
  - now split.
Qed.
