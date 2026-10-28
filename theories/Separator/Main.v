From Coq Require Import Classical_Prop Fin Lia List Lra QArith Qring Vector.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs Contexts RunOrder.
From Mell.Decision Require Import Invariant.
From Mell.Geometry Require Import MathCompBridge QConeCore.
From Mell.Order Require Import FiniteBasis PeriodicOrder.
From Mell.Semilinear Require Import Closure Presentation.
From Mell.Separator Require Import Attractor DirectedRuns FiniteGraph
  RankDecrease SafetyWitness WitnessUpdate.

Import ListNotations.
Open Scope Q_scope.
Module StdVector := Coq.Vectors.Vector.

Definition qvec_head_unit (d : nat) : QVec (S d) :=
  fun index => Fin.caseS' index (fun _ => Q) 1 (fun _ => 0).

Definition qvec_lift {d} (value : QVec d) : QVec (S d) :=
  fun index => Fin.caseS' index (fun _ => Q) 0 value.

Fixpoint full_orthant_generators (d : nat) : list (QVec d) :=
  match d return list (QVec d) with
  | O => []
  | S tail => qvec_head_unit tail ::
      List.map (@qvec_lift tail) (full_orthant_generators tail)
  end.

Lemma qvec_lift_zero : forall d,
  QVecEq (qvec_lift (qvec_zero d)) (qvec_zero (S d)).
Proof.
  intros d index. refine (Fin.caseS' index (fun chosen => _) _ _); reflexivity.
Qed.

Lemma qvec_lift_add : forall d (left right : QVec d),
  QVecEq (qvec_lift (qvec_add left right))
    (qvec_add (qvec_lift left) (qvec_lift right)).
Proof.
  intros d left right index.
  refine (Fin.caseS' index (fun chosen => _) _ _); reflexivity.
Qed.

Lemma qvec_lift_scale : forall d coefficient (value : QVec d),
  QVecEq (qvec_lift (qvec_scale coefficient value))
    (qvec_scale coefficient (qvec_lift value)).
Proof.
  intros d coefficient value index.
  refine (Fin.caseS' index (fun chosen => _) _ _).
  - cbn. symmetry. apply Qmult_0_r.
  - intro tail_index. reflexivity.
Qed.

Lemma qcone_combination_lift : forall d generators (value : QVec d),
  QConeCombination generators value ->
  exists lifted,
    QConeCombination (List.map (@qvec_lift d) generators) lifted /\
    QVecEq (qvec_lift value) lifted.
Proof.
  intros d generators value Hcombination. induction Hcombination.
  - exists (qvec_zero (S d)). split; [constructor|apply qvec_lift_zero].
  - destruct IHHcombination as [lifted [Hlifted Heq]].
    exists (qvec_add (qvec_scale coefficient (qvec_lift generator)) lifted).
    split.
    + constructor; [exact H|now apply in_map|exact Hlifted].
    + eapply qvec_eq_trans; [apply qvec_lift_add|].
      apply qvec_eq_add; [apply qvec_lift_scale|exact Heq].
Qed.

Lemma qcone_combination_mono : forall d
    (smaller larger : list (QVec d)) value,
  (forall generator, List.In generator smaller -> List.In generator larger) ->
  QConeCombination smaller value -> QConeCombination larger value.
Proof.
  intros d smaller larger value Hin Hcombination.
  induction Hcombination; constructor; auto.
Qed.

Lemma full_orthant_contains_nvec : forall d (value : NVec d),
  qcone_generated (full_orthant_generators d) (nvec_to_qvec value).
Proof.
  intros d value. induction value as [|head d tail IH].
  - exists (qvec_zero 0). split; [constructor|].
    intro index. exact (Fin.case0 (fun index => _ = _) index).
  - destruct IH as [generated [Hgenerated Heq]].
    destruct (qcone_combination_lift d _ _ Hgenerated)
      as [lifted [Hlifted Hlifted_eq]].
    exists (qvec_add
      (qvec_scale (q_of_nat head) (qvec_head_unit d)) lifted).
    split.
    + constructor.
      * unfold q_of_nat, Qle. cbn. lia.
      * now left.
      * apply (qcone_combination_mono (S d)
          (List.map (@qvec_lift d) (full_orthant_generators d))
          (full_orthant_generators (S d)) lifted); [|exact Hlifted].
        intros generator Hin. now right.
    + intro index. refine (Fin.caseS' index (fun chosen => _) _ _).
      * change (q_of_nat head == q_of_nat head * 1 + lifted Fin.F1).
        specialize (Hlifted_eq Fin.F1).
        transitivity (q_of_nat head * 1 + 0).
        -- symmetry. eapply Qeq_trans; [apply Qplus_0_r|apply Qmult_1_r].
        -- apply Qplus_comp; [reflexivity|exact Hlifted_eq].
      * intro tail_index.
        change (q_of_nat (StdVector.nth tail tail_index) ==
          q_of_nat head * 0 + lifted (Fin.FS tail_index)).
        specialize (Hlifted_eq (Fin.FS tail_index)).
        specialize (Heq tail_index).
        eapply Qeq_trans; [exact Heq|].
        eapply Qeq_trans; [exact Hlifted_eq|].
        symmetry. eapply Qeq_trans.
        -- apply Qplus_comp; [apply Qmult_0_r|reflexivity].
        -- apply Qplus_0_l.
Qed.

Lemma full_orthant_contains_qvec : forall d (point : QVec d),
  (forall index, 0 <= point index) ->
  qcone_generated (full_orthant_generators d) point.
Proof.
  intros d. induction d as [|d IH]; intros point Hnonnegative.
  - exists (qvec_zero 0). split; [constructor|].
    intro index. exact (Fin.case0 (fun index => _ = _) index).
  - set (tail := fun index : Fin.t d => point (Fin.FS index)).
    destruct (IH tail) as [generated [Hgenerated Heq]].
    { intro index. exact (Hnonnegative (Fin.FS index)). }
    destruct (qcone_combination_lift d _ _ Hgenerated)
      as [lifted [Hlifted Hlifted_eq]].
    exists (qvec_add
      (qvec_scale (point Fin.F1) (qvec_head_unit d)) lifted).
    split.
    + constructor.
      * exact (Hnonnegative Fin.F1).
      * now left.
      * apply (qcone_combination_mono (S d)
          (List.map (@qvec_lift d) (full_orthant_generators d))
          (full_orthant_generators (S d)) lifted); [|exact Hlifted].
        intros generator Hin. now right.
    + intro index. refine (Fin.caseS' index (fun chosen => _) _ _).
      * change (point Fin.F1 == point Fin.F1 * 1 + lifted Fin.F1).
        specialize (Hlifted_eq Fin.F1).
        transitivity (point Fin.F1 * 1 + 0).
        -- symmetry. eapply Qeq_trans; [apply Qplus_0_r|apply Qmult_1_r].
        -- apply Qplus_comp; [reflexivity|exact Hlifted_eq].
      * intro tail_index.
        change (point (Fin.FS tail_index) ==
          point Fin.F1 * 0 + lifted (Fin.FS tail_index)).
        specialize (Hlifted_eq (Fin.FS tail_index)).
        specialize (Heq tail_index).
        eapply Qeq_trans; [exact Heq|].
        eapply Qeq_trans; [exact Hlifted_eq|].
        symmetry. eapply Qeq_trans.
        -- apply Qplus_comp; [apply Qmult_0_r|reflexivity].
        -- apply Qplus_0_l.
Qed.

Lemma full_orthant_generators_nonnegative : forall d generator,
  List.In generator (full_orthant_generators d) ->
  forall index, 0 <= generator index.
Proof.
  intros d. induction d as [|d IH]; intros generator Hin index; cbn in Hin.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + refine (Fin.caseS' index (fun chosen => _) _ _).
      * change (0 <= 1)%Z. lia.
      * intro tail_index. change (0 <= 0)%Z. lia.
    + apply in_map_iff in Hin as [tail [<- Htail]].
      refine (Fin.caseS' index (fun chosen => _) _ _).
      * change (0 <= 0)%Z. lia.
      * intro tail_index. now apply (IH tail Htail tail_index).
Qed.

Lemma full_orthant_nonnegative : forall d point,
  qcone_generated (full_orthant_generators d) point ->
  forall index, 0 <= point index.
Proof.
  intros d point [generated [Hgenerated Heq]] index.
  specialize (Heq index). setoid_rewrite Heq. clear point Heq.
  induction Hgenerated; cbn [qvec_zero qvec_add qvec_scale].
  - change (0 <= 0)%Z. lia.
  - setoid_replace 0 with (0 + 0) by reflexivity.
    apply Qplus_le_compat; [|exact IHHgenerated].
    apply Qmult_le_0_compat; [exact H|].
    now apply (full_orthant_generators_nonnegative d generator H0 index).
Qed.

Theorem full_orthant_generated_iff_nonnegative : forall d point,
  qcone_generated (full_orthant_generators d) point <->
  forall index, 0 <= point index.
Proof.
  intros d point. split.
  - apply full_orthant_nonnegative.
  - apply full_orthant_contains_qvec.
Qed.

Definition full_orthant_node {d} {system : IBVAS d}
    (run : {run : IRun d | ValidIRun system run}) : DirectedIRun system :=
  {| directed_root := proj1_sig run;
     directed_root_valid := proj2_sig run;
     directed_generators := full_orthant_generators d;
     directed_cone_nonnegative := full_orthant_nonnegative d |}.

Lemma full_orthant_node_member : forall d (system : IBVAS d)
    (base run : {run : IRun d | ValidIRun system run}),
  IRunLe (proj1_sig base) (proj1_sig run) ->
  DirectedRunMember (full_orthant_node base) (proj1_sig run).
Proof.
  intros d system base run Hle. split; [exact (proj2_sig run)|].
  exists (nvec_sub_local (irun_target (proj1_sig run))
    (irun_target (proj1_sig base))).
  split.
  - exact Hle.
  - split.
    + change (irun_target (proj1_sig run) =
        nvec_add (irun_target (proj1_sig base))
          (nvec_sub_local (irun_target (proj1_sig run))
            (irun_target (proj1_sig base)))).
      apply nvec_sub_exact_local. exact (proj1 Hle).
    + apply full_orthant_contains_nvec.
Qed.

Lemma full_orthant_nodes_homogeneous : forall d (system : IBVAS d)
    (basis : list {run : IRun d | ValidIRun system run}),
  HomogeneousWitnessNodes (List.map full_orthant_node basis).
Proof.
  intros d system basis left right left_node right_node _ Hleft Hright.
  unfold witness_vertex_node in Hleft, Hright.
  apply nth_error_In in Hleft. apply nth_error_In in Hright.
  apply in_map_iff in Hleft as [left_base [<- _]].
  apply in_map_iff in Hright as [right_base [<- _]].
  intro point. reflexivity.
Qed.

Lemma empty_nset_semilinear : forall d,
  Semilinear (fun _ : NVec d => False).
Proof.
  intros d. exists []. intro value. split; [contradiction|].
  intro Hdenote. now apply (denote_empty d value) in Hdenote.
Qed.

Theorem initial_safety_witness_exists : forall d (system : IBVAS d)
    (safe : NSet d),
  Semilinear safe ->
  (forall value, Reach system value -> safe value) ->
  exists witness : SafetyWitness system safe,
    SameSet (witness_attractor witness) (fun _ => False).
Proof.
  intros d system safe Hsafe Hreach.
  destruct (irun_le_finite_cover d system) as [basis Hbasis].
  unshelve refine (ex_intro _ {| witness_safe_semilinear := Hsafe;
    witness_reach_safe := Hreach;
    witness_attractor := fun _ => False;
    witness_attractor_semilinear := empty_nset_semilinear d;
    witness_attractor_closed := empty_attractor d system;
    witness_attractor_safe := _;
    witness_nodes := List.map full_orthant_node basis;
    witness_nodes_homogeneous := full_orthant_nodes_homogeneous d system basis;
    witness_run_coverage := _ |} _).
  - intros value Hfalse. contradiction.
  - intros run Hvalid. right.
    destruct (Hbasis (exist _ run Hvalid)) as [base [Hin Hle]].
    exists (full_orthant_node base). split.
    + now apply in_map.
    + exact (full_orthant_node_member d system base
        (exist _ run Hvalid) Hle).
  - intro value. reflexivity.
Qed.

Theorem terminal_safety_witness_invariant : forall d
    (system : IBVAS d) (safe : NSet d)
    (witness : SafetyWitness system safe),
  witness_nodes witness = [] ->
  Semilinear (witness_attractor witness) /\
  InitialIncluded system (witness_attractor witness) /\
  Closed system (witness_attractor witness) /\
  (forall value, witness_attractor witness value -> safe value).
Proof.
  intros d system safe witness Hempty.
  assert (Hinitial : InitialIncluded system (witness_attractor witness)).
  { intros value Hin.
    assert (Hleaf : ValidIRun system (irun_leaf value)) by
      (constructor; exact Hin).
    destruct (@witness_run_coverage d system safe witness
      (irun_leaf value) Hleaf) as
      [Hattractor|[node [Hnode _]]].
    - exact Hattractor.
    - rewrite Hempty in Hnode. contradiction. }
  pose proof (attractor_with_initials_inductive d system
    (witness_attractor witness)
    (@witness_attractor_closed d system safe witness) Hinitial) as Hinvariant.
  repeat split.
  - exact (@witness_attractor_semilinear d system safe witness).
  - exact Hinitial.
  - exact (proj2 Hinvariant).
  - exact (@witness_attractor_safe d system safe witness).
Qed.

Theorem every_safety_witness_reaches_terminal : forall d
    (system : IBVAS d) (safe : NSet d)
    (witness : SafetyWitness system safe),
  exists terminal : SafetyWitness system safe,
    witness_nodes terminal = [].
Proof.
  intros d system safe witness.
  set (P := fun nodes => forall current : SafetyWitness system safe,
      witness_nodes current = nodes ->
      exists terminal : SafetyWitness system safe,
        witness_nodes terminal = []).
  assert (Hterminal : forall nodes, P nodes).
  { apply (well_founded_induction
      (witness_rank_less_well_founded d system)).
    intros nodes IH current Hnodes.
    destruct nodes as [|head tail].
    - exists current. exact Hnodes.
    - assert (Hnonempty : witness_nodes current <> []).
      { rewrite Hnodes. discriminate. }
      destruct (lemma_7_1_safety_witness_rank_descent
        d system safe current Hnonempty) as [next Hnext].
      rewrite Hnodes in Hnext.
      exact (IH (witness_nodes next) Hnext next eq_refl). }
  exact (Hterminal (witness_nodes witness) witness eq_refl).
Qed.

Theorem separator_S : forall d (system : IBVAS d) (Phi : NSet d),
  Semilinear Phi ->
  (forall value, Reach system value -> Phi value) ->
  exists J : NSet d,
    Semilinear J /\
    InitialIncluded system J /\
    Closed system J /\
    (forall value, J value -> Phi value).
Proof.
  intros d system Phi Hsemilinear Hsafe.
  destruct (initial_safety_witness_exists d system Phi
    Hsemilinear Hsafe) as [initial _].
  destruct (every_safety_witness_reaches_terminal d system Phi initial)
    as [terminal Hterminal].
  destruct (terminal_safety_witness_invariant d system Phi terminal
    Hterminal) as [Hsemi [Hinitial [Hclosed Hsubset]]].
  exists (witness_attractor terminal).
  repeat split; assumption.
Qed.
