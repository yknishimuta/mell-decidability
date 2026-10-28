From Coq Require Import Arith Fin Lia List Vector VectorSpec Classical_Prop.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.Order Require Import PeriodicOrder.
From Mell.VAS Require Import Runs Transformer Intraproductions
  IntraproductionsLemma57.

Import ListNotations.

Definition ProjectBounded {d} (witness configuration : NVec d) : NVec d :=
  Vector.map2 (fun mask value => if Nat.eqb mask 0 then value else 0)
    witness configuration.

Definition Lemma57Witness {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness : NVec d) : Prop :=
  IntraProduction system gamma witness /\
  forall index : Fin.t d,
    (BoundedGammaCoordinate system gamma index <->
     Vector.nth witness index = 0%nat).

Definition ProductionGraphState {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness state : NVec d) : Prop :=
  exists configuration,
    QGamma system gamma configuration /\
    state = ProjectBounded witness configuration.

Definition ProductionGraphSpecialState {d} (gamma : ProductionTriple d)
    (witness : NVec d) : NVec d :=
  ProjectBounded witness (GammaCapacity gamma).

Record RunEdge (d : nat) := {
  RunEdgeSource : NVec d;
  RunEdgeAction : ZVec d;
  RunEdgeTarget : NVec d
}.

Arguments RunEdgeSource {d} _.
Arguments RunEdgeAction {d} _.
Arguments RunEdgeTarget {d} _.

Fixpoint run_edge_trace {d} (source : NVec d) (targets : list (NVec d))
    : list (RunEdge d) :=
  match targets with
  | [] => []
  | target :: tail =>
      {| RunEdgeSource := source;
         RunEdgeAction := StepAction source target;
         RunEdgeTarget := target |} :: run_edge_trace target tail
  end.

Definition RunAdjacentStep {d} (run : VASRun d)
    (source : NVec d) (action : ZVec d) (target : NVec d) : Prop :=
  List.In {| RunEdgeSource := source;
             RunEdgeAction := action;
             RunEdgeTarget := target |}
    (run_edge_trace (RunSource run) (RunTargets run)).

Definition ProductionGraphTransition {d} (system : PlainVAS d)
    (gamma : ProductionTriple d) (witness : NVec d)
    (source : NVec d) (action : ZVec d) (target : NVec d) : Prop :=
  exists run configuration next,
    OmegaGamma system gamma run /\
    RunAdjacentStep run configuration action next /\
    PlainVASStep system configuration action next /\
    source = ProjectBounded witness configuration /\
    target = ProjectBounded witness next.

Lemma project_bounded_nth : forall d (witness configuration : NVec d)
    (index : Fin.t d),
    Vector.nth (ProjectBounded witness configuration) index =
      if Nat.eqb (Vector.nth witness index) 0
      then Vector.nth configuration index else 0%nat.
Proof.
  intros. unfold ProjectBounded.
  rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl).
  reflexivity.
Qed.

Lemma project_bounded_zero_coordinate : forall d witness configuration
    (index : Fin.t d),
    Vector.nth witness index = 0%nat ->
    Vector.nth (@ProjectBounded d witness configuration) index =
      Vector.nth configuration index.
Proof. intros; rewrite project_bounded_nth, H, Nat.eqb_refl; reflexivity. Qed.

Lemma project_bounded_nonzero_coordinate : forall d witness configuration
    (index : Fin.t d),
    Vector.nth witness index <> 0%nat ->
    Vector.nth (@ProjectBounded d witness configuration) index = 0%nat.
Proof.
  intros d witness configuration index Hnonzero. rewrite project_bounded_nth.
  destruct (Nat.eqb (Vector.nth witness index) 0) eqn:Heq; [|reflexivity].
  apply Nat.eqb_eq in Heq. contradiction.
Qed.

Lemma project_bounded_bounded_coordinate : forall d system gamma witness
    configuration (index : Fin.t d),
    @Lemma57Witness d system gamma witness ->
    BoundedGammaCoordinate system gamma index ->
    Vector.nth (ProjectBounded witness configuration) index =
      Vector.nth configuration index.
Proof. intros d system gamma witness configuration index [_ Hmask] Hbounded.
  apply project_bounded_zero_coordinate, (proj1 (Hmask index)), Hbounded.
Qed.

Lemma project_bounded_unbounded_coordinate : forall d system gamma witness
    configuration (index : Fin.t d),
    @Lemma57Witness d system gamma witness ->
    ~ BoundedGammaCoordinate system gamma index ->
    Vector.nth (ProjectBounded witness configuration) index = 0%nat.
Proof.
  intros d system gamma witness configuration index [_ Hmask] Hunbounded.
  apply project_bounded_nonzero_coordinate. intro Hzero.
  apply Hunbounded, (proj2 (Hmask index)), Hzero.
Qed.

Lemma project_bounded_witness_independent : forall d system gamma left right,
    @Lemma57Witness d system gamma left ->
    Lemma57Witness system gamma right ->
    forall configuration,
      ProjectBounded left configuration = ProjectBounded right configuration.
Proof.
  intros d system gamma left right [_ Hleft] [_ Hright] configuration.
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  repeat rewrite project_bounded_nth.
  destruct (classic (BoundedGammaCoordinate system gamma index)) as [Hb|Hu].
  - rewrite (proj1 (Hleft index) Hb), (proj1 (Hright index) Hb).
    reflexivity.
  - assert (Hl : Vector.nth left index <> 0%nat).
    { intro Hz. apply Hu, (proj2 (Hleft index)), Hz. }
    assert (Hr : Vector.nth right index <> 0%nat).
    { intro Hz. apply Hu, (proj2 (Hright index)), Hz. }
    destruct (Nat.eqb (Vector.nth left index) 0) eqn:Hel;
      [apply Nat.eqb_eq in Hel; contradiction|].
    destruct (Nat.eqb (Vector.nth right index) 0) eqn:Her;
      [apply Nat.eqb_eq in Her; contradiction|reflexivity].
Qed.

Lemma production_graph_special_state_member : forall d system gamma witness,
    @ProductionGraphState d system gamma witness
      (ProductionGraphSpecialState gamma witness).
Proof. intros. exists (GammaCapacity gamma). split.
  - apply qgamma_capacity.
  - reflexivity.
Qed.

Lemma run_adjacent_step_properties : forall d system run source action target,
    ValidVASRun system run ->
    @RunAdjacentStep d run source action target ->
    PlainVASStep system source action target /\
    RunOccurs source run /\ RunOccurs target run.
Proof.
  intros d system [run_source targets] source action target.
  cbn. revert run_source source action target.
  induction targets as [|head tail IH]; intros current source action target
    Hvalid Hadj; cbn in *.
  - contradiction.
  - destruct Hvalid as [Hstep Htail]. destruct Hadj as [Hedge|Hadj].
    + inversion Hedge; subst. split.
      * split; [exact Hstep|reflexivity].
      * split; [now left|now right; left].
    + destruct (IH head source action target Htail Hadj)
        as [Hplain [Hsource Htarget]]. split; [exact Hplain|].
      split; now right.
Qed.

Lemma production_graph_transition_action : forall d system gamma witness
    source action target,
    @ProductionGraphTransition d system gamma witness source action target ->
    List.In action system.
Proof. intros d system gamma witness source action target
  [run [q [q' [_ [_ [[Hin _] _]]]]]]. exact Hin. Qed.

Lemma production_graph_transition_states : forall d system gamma witness
    source action target,
    @ProductionGraphTransition d system gamma witness source action target ->
    ProductionGraphState system gamma witness source /\
    ProductionGraphState system gamma witness target.
Proof.
  intros d system gamma witness source action target
    [run [q [q' [Homega [Hadj [Hstep [Hsource Htarget]]]]]]].
  destruct (run_adjacent_step_properties d system run q action q'
    (proj1 Homega) Hadj) as [_ [Hq Hq']]. split.
  - exists q. split; [eapply omega_occurrence_qgamma; eauto|exact Hsource].
  - exists q'. split; [eapply omega_occurrence_qgamma; eauto|exact Htarget].
Qed.

Lemma production_graph_state_witness_independent : forall d system gamma
    left right,
    @Lemma57Witness d system gamma left -> Lemma57Witness system gamma right ->
    forall state,
      ProductionGraphState system gamma left state <->
      ProductionGraphState system gamma right state.
Proof.
  intros d system gamma left right Hl Hr state. split.
  - intros [q [Hq ->]]. exists q. split; [exact Hq|].
    now rewrite (project_bounded_witness_independent d system gamma left right).
  - intros [q [Hq ->]]. exists q. split; [exact Hq|].
    now rewrite (project_bounded_witness_independent d system gamma left right).
Qed.

Lemma production_graph_transition_witness_independent : forall d system gamma
    left right,
    @Lemma57Witness d system gamma left -> Lemma57Witness system gamma right ->
    forall source action target,
      ProductionGraphTransition system gamma left source action target <->
      ProductionGraphTransition system gamma right source action target.
Proof.
  intros d system gamma left right Hl Hr source action target. split.
  - intros [run [q [q' [Ho [Ha [Hs [-> ->]]]]]]].
    exists run, q, q'. split; [exact Ho|]. split; [exact Ha|].
    split; [exact Hs|]. split.
    + exact (project_bounded_witness_independent d system gamma left right
        Hl Hr q).
    + exact (project_bounded_witness_independent d system gamma left right
        Hl Hr q').
  - intros [run [q [q' [Ho [Ha [Hs [-> ->]]]]]]].
    exists run, q, q'. split; [exact Ho|]. split; [exact Ha|].
    split; [exact Hs|]. split.
    + symmetry. exact (project_bounded_witness_independent d system gamma
        left right Hl Hr q).
    + symmetry. exact (project_bounded_witness_independent d system gamma
        left right Hl Hr q').
Qed.

Lemma nvec_nth_le_weight : forall d (value : NVec d) (index : Fin.t d),
    (Vector.nth value index <= nvec_weight value)%nat.
Proof.
  intros d value. induction value as [|head tail_d tail IH].
  - intro index. exact (Fin.case0 (fun index =>
      (Vector.nth (@Vector.nil nat) index <=
       nvec_weight (@Vector.nil nat))%nat) index).
  - intro index. refine (Fin.caseS' index
      (fun index =>
        (Vector.nth (@Vector.cons nat head tail_d tail) index <=
         nvec_weight (@Vector.cons nat head tail_d tail))%nat) _ _).
    + cbn. lia.
    + intro inner. cbn. specialize (IH inner). lia.
Qed.

Theorem corollary_5_11_projected_states_antichain : forall d system gamma
    witness source target,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    ProductionGraphState system gamma witness source ->
    ProductionGraphState system gamma witness target ->
    nvec_le source target ->
    source = target.
Proof.
  intros d system gamma witness source target Hvalid Hw
    [configuration [Hconfiguration ->]]
    [other [Hother ->]] Hprojected.
  destruct Hw as [Hintra Hmask].
  set (multiplier := S (nvec_weight configuration)).
  assert (Hconfiguration_le :
      nvec_le configuration
        (nvec_add other (nvec_scale multiplier witness))).
  { intro index.
    unfold nvec_add, nvec_scale.
    rewrite (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
      (Vector.nth_map _ _ index index eq_refl).
    destruct (classic (BoundedGammaCoordinate system gamma index))
      as [Hbounded|Hunbounded].
    - pose proof (Hprojected index) as Hle.
      rewrite (project_bounded_bounded_coordinate d system gamma witness
        configuration index (conj Hintra Hmask) Hbounded),
        (project_bounded_bounded_coordinate d system gamma witness
          other index (conj Hintra Hmask) Hbounded) in Hle.
      rewrite (proj1 (Hmask index) Hbounded). lia.
    - assert (Hpositive : (0 < Vector.nth witness index)%nat).
      { destruct (Vector.nth witness index) eqn:Heq; [|lia].
        exfalso. apply Hunbounded, (proj2 (Hmask index)), Heq. }
      pose proof (nvec_nth_le_weight d configuration index) as Hweight.
      unfold multiplier. nia. }
  assert (Hraised : QGamma system gamma
      (nvec_add other (nvec_scale multiplier witness))).
  { eapply lemma_5_5_qgamma_add_intraproduction_nsmul; eauto. }
  destruct (lemma_5_6_intraproduction_dominates d system gamma
      configuration (nvec_add other (nvec_scale multiplier witness))
      Hvalid Hconfiguration Hraised Hconfiguration_le)
    as [increment [Hincrement Hdominates]].
  apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'.
  destruct (classic (BoundedGammaCoordinate system gamma index))
    as [Hbounded|Hunbounded].
  - repeat rewrite (project_bounded_bounded_coordinate d system gamma witness
      _ index (conj Hintra Hmask) Hbounded).
    pose proof (Hprojected index) as Hforward.
    repeat rewrite (project_bounded_bounded_coordinate d system gamma witness
      _ index (conj Hintra Hmask) Hbounded) in Hforward.
    pose proof (Hdominates index) as Hbackward.
    unfold nvec_add, nvec_scale in Hbackward.
    repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index
      eq_refl eq_refl) in Hbackward.
    repeat rewrite (Vector.nth_map _ _ index index eq_refl) in Hbackward.
    rewrite (proj1 (Hmask index) Hbounded),
      (bounded_coordinate_intraproduction_zero d system gamma index increment
        Hbounded Hincrement) in Hbackward.
    lia.
  - repeat rewrite (project_bounded_unbounded_coordinate d system gamma witness
      _ index (conj Hintra Hmask) Hunbounded). reflexivity.
Qed.

Theorem production_graph_states_finite : forall d system gamma witness,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    exists states : list (NVec d),
      forall state,
        ProductionGraphState system gamma witness state <->
        List.In state states.
Proof.
  intros d system gamma witness Hvalid Hw.
  destruct (@restricted_af_finite_cover_classic
      (NVec d) (ProductionGraphState system gamma witness) nvec_le
      (nvec_le_restricted_afs d
        (ProductionGraphState system gamma witness)))
    as [basis Hbasis].
  exists (List.map (@proj1_sig _ _) basis). intro state. split.
  - intro Hstate.
    destruct (Hbasis (exist _ state Hstate)) as [base [Hin Hle]].
    assert (Heq : proj1_sig base = state).
    { eapply corollary_5_11_projected_states_antichain; eauto.
      exact (proj2_sig base). }
    apply in_map_iff. exists base. split; [exact Heq|exact Hin].
  - intro Hin. apply in_map_iff in Hin as [base [Heq Hin]].
    rewrite <- Heq. exact (proj2_sig base).
Qed.

Definition ProductionGraphEdge (d : nat) := RunEdge d.

Definition production_graph_edge_candidates {d}
    (states : list (NVec d)) (actions : list (ZVec d)) :
    list (ProductionGraphEdge d) :=
  List.flat_map (fun source =>
    List.flat_map (fun action =>
      List.map (fun target =>
        {| RunEdgeSource := source;
           RunEdgeAction := action;
           RunEdgeTarget := target |}) states) actions) states.

Lemma production_graph_edge_candidates_spec : forall d states actions
    source action target,
    List.In {| RunEdgeSource := source;
               RunEdgeAction := action;
               RunEdgeTarget := target |}
      (@production_graph_edge_candidates d states actions) <->
    List.In source states /\ List.In action actions /\ List.In target states.
Proof.
  intros d states actions source action target. unfold production_graph_edge_candidates.
  rewrite in_flat_map. split.
  - intros [candidate [Hcandidate Hin]]. rewrite in_flat_map in Hin.
    destruct Hin as [label [Hlabel Hin]]. apply in_map_iff in Hin.
    destruct Hin as [destination [Heq Hdestination]].
    inversion Heq; subst. repeat split; assumption.
  - intros [Hsource [Haction Htarget]]. exists source. split; [exact Hsource|].
    apply in_flat_map. exists action. split; [exact Haction|].
    apply in_map_iff. exists target. split; reflexivity || assumption.
Qed.

Lemma finite_predicate_sublist : forall (A : Type) (predicate : A -> Prop)
    candidates,
    exists selected : list A,
      forall value,
        List.In value selected <->
        List.In value candidates /\ predicate value.
Proof.
  intros A predicate candidates. induction candidates as [|head tail IH].
  - exists []. intro value. cbn. tauto.
  - destruct IH as [selected Hselected].
    destruct (classic (predicate head)) as [Hhead|Hhead].
    + exists (head :: selected). intro value. cbn. rewrite Hselected.
      split.
      * intros [->|[Hin Hpredicate]]; [tauto|tauto].
      * intros [[->|Hin] Hpredicate]; [tauto|tauto].
    + exists selected. intro value. rewrite Hselected. cbn. split.
      * intros [Hin Hpredicate]. tauto.
      * intros [[Heq|Hin] Hpredicate]; [subst; contradiction|tauto].
Qed.

Theorem production_graph_transitions_finite : forall d system gamma witness,
    @ValidProductionTriple d system gamma ->
    Lemma57Witness system gamma witness ->
    exists transitions : list (ProductionGraphEdge d),
      forall source action target,
        ProductionGraphTransition system gamma witness source action target <->
        List.In {| RunEdgeSource := source;
                   RunEdgeAction := action;
                   RunEdgeTarget := target |} transitions.
Proof.
  intros d system gamma witness Hvalid Hw.
  destruct (production_graph_states_finite d system gamma witness Hvalid Hw)
    as [states Hstates].
  set (candidates := production_graph_edge_candidates states system).
  set (predicate := fun edge : ProductionGraphEdge d =>
    ProductionGraphTransition system gamma witness
      (RunEdgeSource edge) (RunEdgeAction edge) (RunEdgeTarget edge)).
  destruct (finite_predicate_sublist (ProductionGraphEdge d) predicate candidates)
    as [transitions Htransitions].
  exists transitions. intros source action target. split.
  - intro Htransition. apply Htransitions. split.
    + apply production_graph_edge_candidates_spec.
      destruct (production_graph_transition_states d system gamma witness
        source action target Htransition) as [Hsource Htarget].
      repeat split; [now apply Hstates| |now apply Hstates].
      now apply production_graph_transition_action with
        (gamma := gamma) (witness := witness) (source := source)
        (target := target).
    + exact Htransition.
  - intro Hin. apply Htransitions in Hin as [_ Htransition]. exact Htransition.
Qed.

Theorem finite_production_graph_exists : forall d system gamma,
    @ValidProductionTriple d system gamma ->
    exists witness : NVec d,
    exists states : list (NVec d),
    exists transitions : list (ProductionGraphEdge d),
      Lemma57Witness system gamma witness /\
      (forall state,
        ProductionGraphState system gamma witness state <->
        List.In state states) /\
      (forall source action target,
        ProductionGraphTransition system gamma witness source action target <->
        List.In {| RunEdgeSource := source;
                   RunEdgeAction := action;
                   RunEdgeTarget := target |} transitions).
Proof.
  intros d system gamma Hvalid.
  destruct (lemma_5_7_bounded_coordinates_intraproduction d system gamma Hvalid)
    as [witness Hw].
  destruct (production_graph_states_finite d system gamma witness Hvalid Hw)
    as [states Hstates].
  destruct (production_graph_transitions_finite d system gamma witness
    Hvalid Hw) as [transitions Htransitions].
  exists witness, states, transitions. split; [exact Hw|].
  split; assumption.
Qed.

Theorem production_graph_special_state_witness_independent : forall d gamma
    left right system,
    @Lemma57Witness d system gamma left -> Lemma57Witness system gamma right ->
    ProductionGraphSpecialState gamma left =
    ProductionGraphSpecialState gamma right.
Proof.
  intros d gamma left right system Hleft Hright.
  unfold ProductionGraphSpecialState.
  exact (project_bounded_witness_independent d system gamma left right
    Hleft Hright (GammaCapacity gamma)).
Qed.
