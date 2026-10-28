From Coq Require Import Arith Bool Fin Lia List Vector ZArith QArith Qring.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge RationalDefinability
  LatticeGordanPullback QConeCore.
From Mell.VAS Require Import Runs Intraproductions IntraproductionsLemma57
  ProductionGraph GraphParikh Kirchhoff RelationCone
  KirchhoffRelation.

Import ListNotations.
Open Scope Q_scope.

Fixpoint qformula_all_fin (count : nat) :
    (Fin.t count -> QFormula) -> QFormula :=
  match count as n return (Fin.t n -> QFormula) -> QFormula with
  | O => fun _ => QFTop
  | S n => fun body =>
      QFAnd (body Fin.F1)
        (qformula_all_fin n (fun index => body (Fin.FS index)))
  end.

Lemma qformula_all_fin_closed : forall count body bound,
    (forall index, qformula_closed bound (body index) = true) ->
    qformula_closed bound (qformula_all_fin count body) = true.
Proof.
  intros count; induction count as [|count IH]; intros body bound H; cbn; auto.
  apply andb_true_iff. split; [apply H|apply IH]. intro index. apply H.
Qed.

Lemma qformula_all_fin_correct : forall count body environment,
    qformula_semantics environment (qformula_all_fin count body) <->
    forall index, qformula_semantics environment (body index).
Proof.
  intros count; induction count as [|count IH]; intros body environment; cbn.
  - split; [intros _ index; exact (Fin.case0 (fun _ => _) index)|auto].
  - rewrite IH. split.
    + intros [Hhead Htail] index.
      refine (Fin.caseS' index (fun i => qformula_semantics environment (body i))
        Hhead _). intro tail. apply Htail.
    + intro H. split; [apply (H Fin.F1)|intro index; apply (H (Fin.FS index))].
Qed.

Fixpoint qformula_and_list (formulas : list QFormula) : QFormula :=
  match formulas with
  | [] => QFTop
  | formula :: tail => QFAnd formula (qformula_and_list tail)
  end.

Lemma qformula_and_list_closed : forall formulas bound,
    List.Forall (fun formula => qformula_closed bound formula = true) formulas ->
    qformula_closed bound (qformula_and_list formulas) = true.
Proof.
  intros formulas bound H; induction H; cbn; [reflexivity|].
  rewrite H, IHForall. reflexivity.
Qed.

Lemma qformula_and_list_correct : forall formulas environment,
    qformula_semantics environment (qformula_and_list formulas) <->
    forall formula, List.In formula formulas -> qformula_semantics environment formula.
Proof.
  intros formulas; induction formulas as [|head tail IH]; intro environment; cbn.
  - tauto.
  - rewrite IH. split.
    + intros [Hhead Htail] formula [->|Hin]; auto.
    + intro H. split; [apply H; now left|]. intros; apply H; now right.
Qed.

Definition qindex (index : Fin.t 1) : nat := proj1_sig (Fin.to_nat index).

Lemma fin_to_nat_FS_value : forall n (index : Fin.t n),
    proj1_sig (Fin.to_nat (Fin.FS index)) = S (proj1_sig (Fin.to_nat index)).
Proof.
  intros n index. induction index; cbn; [reflexivity|].
  destruct (Fin.to_nat index). reflexivity.
Qed.

Definition qpair_input_variable (edge_count d : nat) (index : Fin.t d) : nat :=
  (edge_count + proj1_sig (Fin.to_nat index))%nat.

Definition qpair_output_variable (edge_count d : nat) (index : Fin.t d) : nat :=
  (edge_count + d + proj1_sig (Fin.to_nat index))%nat.

Definition qnonnegative_formula (edge_count d : nat) : QFormula :=
  qformula_all_fin d (fun index =>
    QFLe (QTConst 0) (QTVar (qpair_input_variable edge_count d index))).

Definition qoutput_nonnegative_formula (edge_count d : nat) : QFormula :=
  qformula_all_fin d (fun index =>
    QFLe (QTConst 0) (QTVar (qpair_output_variable edge_count d index))).

Definition qsupport_coordinate_formula (variable : nat) (support : nat) : QFormula :=
  if Nat.eqb support 0
  then QFEq (QTVar variable) (QTConst 0)
  else QFLt (QTConst 0) (QTVar variable).

Definition qinput_support_formula {d} (edge_count : nat) (support : NVec d) :
    QFormula :=
  qformula_all_fin d (fun index =>
    qsupport_coordinate_formula (qpair_input_variable edge_count d index)
      (Vector.nth support index)).

Definition qoutput_support_formula {d} (edge_count : nat) (support : NVec d) :
    QFormula :=
  qformula_all_fin d (fun index =>
    qsupport_coordinate_formula (qpair_output_variable edge_count d index)
      (Vector.nth support index)).

Definition qweights_positive_formula (edge_count : nat) : QFormula :=
  qformula_all_fin edge_count (fun index =>
    QFLt (QTConst 0) (QTVar (proj1_sig (Fin.to_nat index)))).

Fixpoint qedge_linear_term {d} (position : nat)
    (edges : list (ProductionGraphEdge d))
    (coefficient : ProductionGraphEdge d -> Q) : QTerm :=
  match edges with
  | [] => QTConst 0
  | edge :: tail =>
      QTAdd (QTScale (coefficient edge) (QTVar position))
        (qedge_linear_term (S position) tail coefficient)
  end.

Definition qedge_out_coefficient {d} (state : NVec d)
    (edge : ProductionGraphEdge d) : Q :=
  if EdgeLeaves state edge then 1 else 0.

Definition qedge_in_coefficient {d} (state : NVec d)
    (edge : ProductionGraphEdge d) : Q :=
  if EdgeEnters state edge then 1 else 0.

Definition qedge_balance_formula {d} (edges : list (ProductionGraphEdge d))
    (state : NVec d) : QFormula :=
  QFEq (qedge_linear_term 0 edges (qedge_out_coefficient state))
    (qedge_linear_term 0 edges (qedge_in_coefficient state)).

Definition qedge_states {d} (edges : list (ProductionGraphEdge d)) : list (NVec d) :=
  List.flat_map (fun edge => [RunEdgeSource edge; RunEdgeTarget edge]) edges.

Definition qkirchhoff_balance_formula {d}
    (edges : list (ProductionGraphEdge d)) : QFormula :=
  qformula_and_list (List.map (qedge_balance_formula edges) (qedge_states edges)).

Definition qedge_action_coefficient {d} (coordinate : Fin.t d)
    (edge : ProductionGraphEdge d) : Q :=
  inject_Z (Vector.nth (RunEdgeAction edge) coordinate).

Definition qdisplacement_formula {d} (edges : list (ProductionGraphEdge d)) :
    QFormula :=
  qformula_all_fin d (fun coordinate =>
    QFEq
      (QTAdd (QTVar (qpair_output_variable (length edges) d coordinate))
        (QTOpp (QTVar (qpair_input_variable (length edges) d coordinate))))
      (qedge_linear_term 0 edges (qedge_action_coefficient coordinate))).

Definition qkirchhoff_relation_body {d} (gamma : ProductionTriple d)
    (edges : list (ProductionGraphEdge d)) : QFormula :=
  QFAnd (qnonnegative_formula (length edges) d)
  (QFAnd (qoutput_nonnegative_formula (length edges) d)
  (QFAnd (qinput_support_formula (length edges) (GammaInput gamma))
  (QFAnd (qoutput_support_formula (length edges) (GammaOutput gamma))
  (QFAnd (qweights_positive_formula (length edges))
  (QFAnd (qkirchhoff_balance_formula edges)
          (qdisplacement_formula edges)))))).

Definition qkirchhoff_relation_formula {d} (gamma : ProductionTriple d)
    (edges : list (ProductionGraphEdge d)) : QFormula :=
  qexists_many (length edges) (qkirchhoff_relation_body gamma edges).

Lemma qterm_closed_var : forall bound variable,
    (variable < bound)%nat -> qterm_closed bound (QTVar variable) = true.
Proof.
  intros bound variable Hlt. change (Nat.ltb variable bound = true).
  now apply Nat.ltb_lt.
Qed.

Lemma qpair_input_variable_lt : forall edge_count d (index : Fin.t d),
    (qpair_input_variable edge_count d index < edge_count + (d + d))%nat.
Proof.
  intros. unfold qpair_input_variable.
  apply (proj1 (Nat.add_lt_mono_l _ _ edge_count)).
  eapply Nat.lt_le_trans; [apply (proj2_sig (Fin.to_nat index))|lia].
Qed.

Lemma qpair_output_variable_lt : forall edge_count d (index : Fin.t d),
    (qpair_output_variable edge_count d index < edge_count + (d + d))%nat.
Proof.
  intros. unfold qpair_output_variable.
  replace (edge_count + d + proj1_sig (Fin.to_nat index))%nat with
    (edge_count + (d + proj1_sig (Fin.to_nat index)))%nat by lia.
  apply (proj1 (Nat.add_lt_mono_l _ _ edge_count)).
  apply (proj1 (Nat.add_lt_mono_l _ _ d)).
  apply (proj2_sig (Fin.to_nat index)).
Qed.

Lemma qweight_variable_lt : forall edge_count d (index : Fin.t edge_count),
    (proj1_sig (Fin.to_nat index) < edge_count + (d + d))%nat.
Proof.
  intros. eapply Nat.lt_le_trans; [apply (proj2_sig (Fin.to_nat index))|lia].
Qed.

Lemma qterm_closed_edge_linear : forall d position edges coefficient bound,
    (position + length edges <= bound)%nat ->
    qterm_closed bound (@qedge_linear_term d position edges coefficient) = true.
Proof.
  intros d position edges; revert position.
  induction edges as [|edge tail IH]; intros position coefficient bound Hbound; cbn.
  - reflexivity.
  - rewrite andb_true_iff. split.
    + destruct bound as [|bound']; [cbn in Hbound; lia|].
      cbn. rewrite Nat.leb_le. simpl in Hbound. lia.
    + apply IH. simpl in Hbound. lia.
Qed.

Lemma qkirchhoff_relation_body_closed : forall d gamma edges,
    qformula_closed (length edges + (d + d))
      (@qkirchhoff_relation_body d gamma edges) = true.
Proof.
  intros d gamma edges. unfold qkirchhoff_relation_body. cbn.
  repeat rewrite andb_true_iff. repeat split.
  - apply qformula_all_fin_closed. intro index. cbn. apply qterm_closed_var.
    apply qpair_input_variable_lt.
  - apply qformula_all_fin_closed. intro index. cbn. apply qterm_closed_var.
    apply qpair_output_variable_lt.
  - apply qformula_all_fin_closed. intro index.
    unfold qsupport_coordinate_formula. destruct Nat.eqb; cbn;
      repeat rewrite andb_true_iff; repeat split; try reflexivity;
      apply qterm_closed_var; apply qpair_input_variable_lt.
  - apply qformula_all_fin_closed. intro index.
    unfold qsupport_coordinate_formula. destruct Nat.eqb; cbn;
      repeat rewrite andb_true_iff; repeat split; try reflexivity;
      apply qterm_closed_var; apply qpair_output_variable_lt.
  - apply qformula_all_fin_closed. intro index. cbn. apply qterm_closed_var.
    apply qweight_variable_lt.
  - apply qformula_and_list_closed. apply List.Forall_forall.
    intros formula Hin. apply in_map_iff in Hin as [state [<- _]].
    cbn. repeat rewrite andb_true_iff. split;
      apply qterm_closed_edge_linear; lia.
  - apply qformula_all_fin_closed. intro index. cbn.
    repeat rewrite andb_true_iff. repeat split.
    + apply qterm_closed_var. apply qpair_output_variable_lt.
    + apply qterm_closed_var. apply qpair_input_variable_lt.
    + apply qterm_closed_edge_linear. lia.
Qed.

Lemma qkirchhoff_relation_formula_closed : forall d gamma edges,
    qformula_closed (d + d) (@qkirchhoff_relation_formula d gamma edges) = true.
Proof.
  intros. unfold qkirchhoff_relation_formula. rewrite qexists_many_closed.
  replace (length edges + (d + d))%nat with (length edges + (d + d))%nat
    by reflexivity. apply qkirchhoff_relation_body_closed.
Qed.

Lemma qweight_environment_inside : forall d (weights : QVec d) environment index,
    qvec_bind_environment d weights environment
      (proj1_sig (Fin.to_nat index)) = weights index.
Proof. apply qvec_bind_environment_inside. Qed.

Lemma qpair_environment_input : forall d k (weights : QVec k)
    (pair : QVec (d + d)) index,
    qvec_bind_environment k weights (qvec_environment pair)
      (qpair_input_variable k d index) == qpair_left pair index.
Proof.
  intros d k weights pair index. unfold qpair_input_variable.
  rewrite qvec_bind_environment_outside.
  rewrite <- (Fin.L_sanity d index), qvec_environment_inside.
  symmetry. apply qvec_left_nth.
Qed.

Lemma qpair_environment_output : forall d k (weights : QVec k)
    (pair : QVec (d + d)) index,
    qvec_bind_environment k weights (qvec_environment pair)
      (qpair_output_variable k d index) == qpair_right pair index.
Proof.
  intros d k weights pair index. unfold qpair_output_variable.
  replace (k + d + proj1_sig (Fin.to_nat index))%nat with
    (k + (d + proj1_sig (Fin.to_nat index)))%nat by lia.
  rewrite qvec_bind_environment_outside.
  replace (d + proj1_sig (Fin.to_nat index))%nat with
    (proj1_sig (Fin.to_nat (Fin.R d index))) by
      now rewrite Fin.R_sanity.
  rewrite qvec_environment_inside. symmetry. apply qvec_right_nth.
Qed.

Lemma qformula_nonnegative_correct : forall d k (weights : QVec k)
    (pair : QVec (d + d)),
    qformula_semantics (qvec_bind_environment k weights (qvec_environment pair))
      (qnonnegative_formula k d) <-> NonnegativeQVec (qpair_left pair).
Proof.
  intros d k weights pair. unfold qnonnegative_formula.
  rewrite qformula_all_fin_correct. unfold NonnegativeQVec. split; intros H index;
    specialize (H index); cbn in H.
  - eapply (proj1 (Qle_comp 0 0 (Qeq_refl 0) _ _
      (qpair_environment_input d k weights pair index))). exact H.
  - eapply (proj2 (Qle_comp 0 0 (Qeq_refl 0) _ _
      (qpair_environment_input d k weights pair index))). exact H.
Qed.

Lemma qformula_output_nonnegative_correct : forall d k (weights : QVec k)
    (pair : QVec (d + d)),
    qformula_semantics (qvec_bind_environment k weights (qvec_environment pair))
      (qoutput_nonnegative_formula k d) <-> NonnegativeQVec (qpair_right pair).
Proof.
  intros d k weights pair. unfold qoutput_nonnegative_formula.
  rewrite qformula_all_fin_correct. unfold NonnegativeQVec. split; intros H index;
    specialize (H index); cbn in H.
  - eapply (proj1 (Qle_comp 0 0 (Qeq_refl 0) _ _
      (qpair_environment_output d k weights pair index))). exact H.
  - eapply (proj2 (Qle_comp 0 0 (Qeq_refl 0) _ _
      (qpair_environment_output d k weights pair index))). exact H.
Qed.

Lemma qsupport_coordinate_correct : forall environment variable support value,
    environment variable == value -> 0 <= value ->
    (qformula_semantics environment (qsupport_coordinate_formula variable support) <->
     (0 < value <-> 0 < q_of_nat support)).
Proof.
  intros environment variable support value Heq Hnonnegative.
  unfold qsupport_coordinate_formula, nvec_to_qvec.
  destruct (Nat.eqb support 0) eqn:Hzero.
  - apply Nat.eqb_eq in Hzero; subst support. cbn. unfold q_of_nat; cbn.
    setoid_rewrite Heq. split.
    + intro Hvalue. split; intro Hpositive.
      * setoid_rewrite Hvalue in Hpositive. exfalso. exact (Qlt_irrefl 0 Hpositive).
      * exfalso. exact (Qlt_irrefl 0 Hpositive).
    + intro Hsupport. apply Qle_antisym.
      * destruct (Qlt_le_dec 0 value) as [Hpositive|Hle]; [|exact Hle].
        apply Hsupport in Hpositive. exfalso. exact (Qlt_irrefl 0 Hpositive).
      * exact Hnonnegative.
  - apply Nat.eqb_neq in Hzero.
    assert (Hsupportpositive : 0 < q_of_nat support).
    { unfold q_of_nat, Qlt. cbn. lia. }
    cbn. setoid_rewrite Heq. split.
    + intro Hpositive. split; [intro; exact Hsupportpositive|intro; exact Hpositive].
    + intro Hsupport. apply Hsupport. exact Hsupportpositive.
Qed.

Lemma qformula_input_support_correct : forall d k (weights : QVec k)
    (pair : QVec (d + d)) support,
    NonnegativeQVec (qpair_left pair) ->
    qformula_semantics (qvec_bind_environment k weights (qvec_environment pair))
      (qinput_support_formula k support) <->
    SamePositiveSupport (qpair_left pair) support.
Proof.
  intros d k weights pair support Hnonnegative. unfold qinput_support_formula.
  rewrite qformula_all_fin_correct. unfold SamePositiveSupport. split; intros H index.
  - apply (proj1 (qsupport_coordinate_correct _ _ _ _
      (qpair_environment_input d k weights pair index) (Hnonnegative index))).
    apply H.
  - apply (proj2 (qsupport_coordinate_correct _ _ _ _
      (qpair_environment_input d k weights pair index) (Hnonnegative index))).
    apply H.
Qed.

Lemma qformula_output_support_correct : forall d k (weights : QVec k)
    (pair : QVec (d + d)) support,
    NonnegativeQVec (qpair_right pair) ->
    qformula_semantics (qvec_bind_environment k weights (qvec_environment pair))
      (qoutput_support_formula k support) <->
    SamePositiveSupport (qpair_right pair) support.
Proof.
  intros d k weights pair support Hnonnegative. unfold qoutput_support_formula.
  rewrite qformula_all_fin_correct. unfold SamePositiveSupport. split; intros H index.
  - apply (proj1 (qsupport_coordinate_correct _ _ _ _
      (qpair_environment_output d k weights pair index) (Hnonnegative index))).
    apply H.
  - apply (proj2 (qsupport_coordinate_correct _ _ _ _
      (qpair_environment_output d k weights pair index) (Hnonnegative index))).
    apply H.
Qed.

Lemma qformula_weights_positive_correct : forall d
    (edges : list (ProductionGraphEdge d))
    (weights : QVec (length edges)) (pair : QVec (d + d)),
    qformula_semantics
      (qvec_bind_environment (length edges) weights (qvec_environment pair))
      (qweights_positive_formula (length edges)) <->
    forall index, 0 < weights index.
Proof.
  intros d edges weights pair. unfold qweights_positive_formula.
  rewrite qformula_all_fin_correct. split; intros H index; specialize (H index);
    cbn in H.
  - pose proof (qvec_bind_environment_inside (length edges) weights
      (qvec_environment pair) index) as Heq. setoid_rewrite Heq in H. exact H.
  - pose proof (qvec_bind_environment_inside (length edges) weights
      (qvec_environment pair) index) as Heq. setoid_rewrite <- Heq in H. exact H.
Qed.

Lemma weights_positive_lookup_equiv : forall d
    (edges : list (ProductionGraphEdge d)) (weights : QVec (length edges)),
    NoDup edges ->
    ((forall index, 0 < weights index) <->
     forall edge, List.In edge edges -> 0 < EdgeWeightLookup edges weights edge).
Proof.
  intros d edges; induction edges as [|head tail IH]; intros weights Hnodup.
  - split.
    + intros _ edge Hin. contradiction.
    + intros _ index. exact (Fin.case0 (fun index => 0 < weights index) index).
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst. split.
    + intros H edge [Heq|Hin].
      * subst. cbn [EdgeWeightLookup].
        destruct (production_graph_edge_eq_dec edge edge); [apply H|contradiction].
      * cbn [EdgeWeightLookup].
        destruct (production_graph_edge_eq_dec edge head) as [Heq|Hneq].
        -- subst. contradiction.
        -- apply (proj1 (IH (fun index => weights (Fin.FS index)) Hnodup')).
           ++ intro index. apply H.
           ++ exact Hin.
    + intros H index.
      refine (Fin.caseS' index (fun i => 0 < weights i) _ _).
      * specialize (H head (or_introl eq_refl)). cbn [EdgeWeightLookup] in H.
        destruct (production_graph_edge_eq_dec head head); [exact H|contradiction].
      * intro tail_index.
        apply (proj2 (IH (fun index => weights (Fin.FS index)) Hnodup')).
        intros edge Hin. specialize (H edge (or_intror Hin)).
        cbn [EdgeWeightLookup] in H.
        destruct (production_graph_edge_eq_dec edge head) as [Heq|Hneq].
        -- subst. contradiction.
        -- exact H.
Qed.

Lemma qformula_weights_positive_edges : forall d
    (edges : list (ProductionGraphEdge d))
    (weights : QVec (length edges)) (pair : QVec (d + d)),
    NoDup edges ->
    (qformula_semantics
      (qvec_bind_environment (length edges) weights (qvec_environment pair))
      (qweights_positive_formula (length edges)) <->
     forall edge, List.In edge edges -> 0 < EdgeWeightLookup edges weights edge).
Proof.
  intros d edges weights pair Hnodup. rewrite qformula_weights_positive_correct.
  apply weights_positive_lookup_equiv. exact Hnodup.
Qed.

Fixpoint EdgeLinearVectorSum {d} (edges : list (ProductionGraphEdge d)) :
    QVec (length edges) ->
    (ProductionGraphEdge d -> Q) -> Q :=
  match edges as listed return QVec (length listed) ->
      (ProductionGraphEdge d -> Q) -> Q with
  | [] => fun _ _ => 0
  | edge :: tail => fun weights coefficient =>
      coefficient edge * weights Fin.F1 +
      EdgeLinearVectorSum tail (fun index => weights (Fin.FS index)) coefficient
  end.

Lemma qedge_linear_term_correct : forall d edges position coefficient
    (weights : QVec (length edges)) environment,
    (forall index, environment (position + proj1_sig (Fin.to_nat index))%nat ==
      weights index) ->
    qterm_semantics environment (@qedge_linear_term d position edges coefficient) ==
      EdgeLinearVectorSum edges weights coefficient.
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros position coefficient
    weights environment Henv; cbn [qedge_linear_term EdgeLinearVectorSum].
  - reflexivity.
  - apply Qplus_comp.
    + apply Qmult_comp; [reflexivity|].
      specialize (Henv Fin.F1). cbn in Henv. now rewrite Nat.add_0_r in Henv.
    + apply IH. intro index.
      replace (S position + proj1_sig (Fin.to_nat index))%nat with
        (position + proj1_sig (Fin.to_nat (Fin.FS index)))%nat.
      * apply Henv.
      * rewrite fin_to_nat_FS_value. lia.
Qed.

Lemma qedge_linear_term_bound_correct : forall d edges coefficient
    (weights : QVec (length edges)) (pair : QVec (d + d)),
    qterm_semantics
      (qvec_bind_environment (length edges) weights (qvec_environment pair))
      (@qedge_linear_term d 0 edges coefficient) ==
    EdgeLinearVectorSum edges weights coefficient.
Proof.
  intros. apply qedge_linear_term_correct. intro index.
  rewrite Nat.add_0_l, qvec_bind_environment_inside. reflexivity.
Qed.

Lemma fold_right_extensional_q : forall A (values : list A) left right,
    (forall value, List.In value values -> left value == right value) ->
    List.fold_right Qplus 0 (List.map left values) ==
    List.fold_right Qplus 0 (List.map right values).
Proof.
  intros A values; induction values as [|head tail IH]; intros left right H;
    cbn; [reflexivity|].
  apply Qplus_comp; [apply H; now left|]. apply IH. intros; apply H; now right.
Qed.

Lemma edge_linear_vector_sum_lookup : forall d
    (edges : list (ProductionGraphEdge d))
    (weights : QVec (length edges))
    (coefficient : ProductionGraphEdge d -> Q),
    NoDup edges ->
    EdgeLinearVectorSum edges weights coefficient ==
    List.fold_right Qplus 0
      (List.map (fun edge => coefficient edge * EdgeWeightLookup edges weights edge)
        edges).
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros weights coefficient Hnodup;
    cbn [EdgeLinearVectorSum]; [reflexivity|].
  inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
  apply Qplus_comp.
  - apply Qmult_comp; [reflexivity|]. cbn [EdgeWeightLookup].
    destruct (production_graph_edge_eq_dec edge edge); [reflexivity|contradiction].
  - eapply Qeq_trans; [apply IH; exact Hnodup'|].
    apply fold_right_extensional_q. intros other Hin. apply Qmult_comp; [reflexivity|].
    cbn [EdgeWeightLookup].
    destruct (production_graph_edge_eq_dec other edge) as [Heq|Hneq].
    + subst. contradiction.
    + reflexivity.
Qed.

Lemma fold_coeff_selector_q : forall d (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> Q)
    (select : ProductionGraphEdge d -> bool),
    List.fold_right Qplus 0
      (List.map (fun edge => (if select edge then 1 else 0) * weight edge) edges) ==
    GraphWeightSumQ edges weight select.
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros weight select;
    cbn [GraphWeightSumQ]; [reflexivity|].
  apply Qplus_comp.
  - destruct (select edge); ring.
  - apply IH.
Qed.

Lemma edge_linear_vector_sum_selector : forall d
    (edges : list (ProductionGraphEdge d))
    (weights : QVec (length edges))
    (select : ProductionGraphEdge d -> bool),
    NoDup edges ->
    EdgeLinearVectorSum edges weights
      (fun edge => if select edge then 1 else 0) ==
    GraphWeightSumQ edges (EdgeWeightLookup edges weights) select.
Proof.
  intros d edges weights select Hnodup.
  eapply Qeq_trans; [apply edge_linear_vector_sum_lookup; exact Hnodup|].
  apply fold_coeff_selector_q.
Qed.

Lemma fold_action_displacement_q : forall d
    (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> Q) (coordinate : Fin.t d),
    List.fold_right Qplus 0
      (List.map (fun edge => qedge_action_coefficient coordinate edge * weight edge)
        edges) ==
    KirchhoffDisplacementQ edges weight coordinate.
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros weight coordinate;
    cbn [KirchhoffDisplacementQ qvec_rsum]; [reflexivity|].
  unfold qvec_add, qvec_scale, qedge_action_coefficient, zvec_to_qvec.
  apply Qplus_comp; [apply Qmult_comm|apply IH].
Qed.

Lemma edge_linear_vector_sum_action : forall d
    (edges : list (ProductionGraphEdge d))
    (weights : QVec (length edges)) (coordinate : Fin.t d),
    NoDup edges ->
    EdgeLinearVectorSum edges weights (qedge_action_coefficient coordinate) ==
    KirchhoffDisplacementQ edges (EdgeWeightLookup edges weights) coordinate.
Proof.
  intros d edges weights coordinate Hnodup.
  eapply Qeq_trans; [apply edge_linear_vector_sum_lookup; exact Hnodup|].
  apply fold_action_displacement_q.
Qed.

Lemma qedge_balance_formula_correct : forall d
    (edges : list (ProductionGraphEdge d)) state
    (weights : QVec (length edges)) (pair : QVec (d + d)),
    NoDup edges ->
    (qformula_semantics
      (qvec_bind_environment (length edges) weights (qvec_environment pair))
      (qedge_balance_formula edges state) <->
     GraphWeightSumQ edges (EdgeWeightLookup edges weights) (EdgeLeaves state) ==
     GraphWeightSumQ edges (EdgeWeightLookup edges weights) (EdgeEnters state)).
Proof.
  intros d edges state weights pair Hnodup. unfold qedge_balance_formula.
  cbn. setoid_rewrite qedge_linear_term_bound_correct.
  unfold qedge_out_coefficient, qedge_in_coefficient.
  setoid_rewrite (edge_linear_vector_sum_selector d edges weights
    (EdgeLeaves state)
    Hnodup).
  setoid_rewrite (edge_linear_vector_sum_selector d edges weights
    (EdgeEnters state)
    Hnodup).
  tauto.
Qed.

Lemma graph_weight_sum_q_outside_states : forall d edges weight state select_endpoint,
    (forall edge, select_endpoint edge = true ->
      List.In state [RunEdgeSource edge; RunEdgeTarget edge]) ->
    ~ List.In state (qedge_states edges) ->
    @GraphWeightSumQ d edges weight select_endpoint == 0.
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros weight state select Hsel Houtside;
    cbn [GraphWeightSumQ qedge_states] in *; [reflexivity|].
  assert (Htail : ~ List.In state (qedge_states tail)).
  { intro Hin. apply Houtside. apply in_or_app. right. exact Hin. }
  destruct (select edge) eqn:Hedge.
  - exfalso. apply Houtside. apply in_or_app. left. apply Hsel; exact Hedge.
  - cbn. setoid_rewrite (IH weight state select Hsel Htail). ring.
Qed.

Lemma qkirchhoff_balance_formula_correct : forall d
    (edges : list (ProductionGraphEdge d))
    (weights : QVec (length edges)) (pair : QVec (d + d)),
    NoDup edges ->
    (qformula_semantics
      (qvec_bind_environment (length edges) weights (qvec_environment pair))
      (qkirchhoff_balance_formula edges) <->
     KirchhoffBalanceQ edges (EdgeWeightLookup edges weights)).
Proof.
  intros d edges weights pair Hnodup. unfold qkirchhoff_balance_formula.
  rewrite qformula_and_list_correct. split.
  - intros H state. destruct (in_dec nvec_eq_dec state (qedge_states edges)) as [Hin|Hout].
    + apply (proj1 (qedge_balance_formula_correct d edges state weights pair Hnodup)).
      apply H. apply in_map. exact Hin.
    + eapply Qeq_trans.
      * apply (graph_weight_sum_q_outside_states d edges
          (EdgeWeightLookup edges weights) state (EdgeLeaves state)).
        -- intros edge. unfold EdgeLeaves. destruct nvec_eq_dec; intro Htrue;
             [subst; now left|discriminate].
        -- exact Hout.
      * symmetry. apply (graph_weight_sum_q_outside_states d edges
          (EdgeWeightLookup edges weights) state (EdgeEnters state)).
        -- intros edge. unfold EdgeEnters. destruct nvec_eq_dec; intro Htrue;
             [subst; now right; left|discriminate].
        -- exact Hout.
  - intros H formula Hin. apply in_map_iff in Hin as [state [<- _]].
    apply (proj2 (qedge_balance_formula_correct d edges state weights pair Hnodup)).
    apply H.
Qed.

Lemma qdisplacement_formula_correct : forall d
    (edges : list (ProductionGraphEdge d))
    (weights : QVec (length edges)) (pair : QVec (d + d)),
    NoDup edges ->
    (qformula_semantics
      (qvec_bind_environment (length edges) weights (qvec_environment pair))
      (qdisplacement_formula edges) <->
     QVecEq (QVecDifference (qpair_right pair) (qpair_left pair))
       (KirchhoffDisplacementQ edges (EdgeWeightLookup edges weights))).
Proof.
  intros d edges weights pair Hnodup. unfold qdisplacement_formula.
  rewrite qformula_all_fin_correct. split; intros H coordinate; specialize (H coordinate);
    cbn in H; unfold QVecDifference.
  - eapply Qeq_trans.
    + apply Qplus_comp.
      * symmetry. apply qpair_environment_output.
      * apply Qopp_comp. symmetry. apply qpair_environment_input.
    + eapply Qeq_trans; [exact H|].
      eapply Qeq_trans; [apply qedge_linear_term_bound_correct|].
      apply edge_linear_vector_sum_action. exact Hnodup.
  - eapply Qeq_trans.
    + apply Qplus_comp.
      * apply qpair_environment_output.
      * apply Qopp_comp. apply qpair_environment_input.
    + eapply Qeq_trans; [exact H|].
      symmetry. eapply Qeq_trans; [apply qedge_linear_term_bound_correct|].
      apply edge_linear_vector_sum_action. exact Hnodup.
Qed.

Lemma qkirchhoff_relation_body_correct : forall d
    (gamma : ProductionTriple d) (edges : list (ProductionGraphEdge d))
    (weights : QVec (length edges)) (pair : QVec (d + d)),
    NoDup edges ->
    (qformula_semantics
      (qvec_bind_environment (length edges) weights (qvec_environment pair))
      (qkirchhoff_relation_body gamma edges) <->
     NonnegativeQVec (qpair_left pair) /\
     NonnegativeQVec (qpair_right pair) /\
     SamePositiveSupport (qpair_left pair) (GammaInput gamma) /\
     SamePositiveSupport (qpair_right pair) (GammaOutput gamma) /\
     FiniteKirchhoffWitness gamma edges (qpair_left pair) (qpair_right pair) weights).
Proof.
  intros d gamma edges weights pair Hnodup. unfold qkirchhoff_relation_body.
  cbn. rewrite qformula_nonnegative_correct, qformula_output_nonnegative_correct.
  split.
  - intros [Hinput [Houtput [Hinput_support [Houtput_support
      [Hpositive [Hbalance Hdisplacement]]]]]].
    refine (conj Hinput (conj Houtput (conj _ (conj _ _)))).
    + apply (proj1 (qformula_input_support_correct d (length edges) weights pair
        (GammaInput gamma) Hinput)); exact Hinput_support.
    + apply (proj1 (qformula_output_support_correct d (length edges) weights pair
        (GammaOutput gamma) Houtput)); exact Houtput_support.
    + unfold FiniteKirchhoffWitness. refine (conj _ (conj _ _)).
      * apply (proj1 (qkirchhoff_balance_formula_correct d edges weights pair Hnodup)).
        exact Hbalance.
      * apply (proj1 (qformula_weights_positive_edges d edges weights pair Hnodup)).
        exact Hpositive.
      * apply (proj1 (qdisplacement_formula_correct d edges weights pair Hnodup)).
        exact Hdisplacement.
  - intros [Hinput [Houtput [Hinput_support [Houtput_support
      [Hbalance [Hpositive Hdisplacement]]]]]].
    refine (conj Hinput (conj Houtput (conj _ (conj _ (conj _ (conj _ _)))))).
    + apply (proj2 (qformula_input_support_correct d (length edges) weights pair
        (GammaInput gamma) Hinput)); exact Hinput_support.
    + apply (proj2 (qformula_output_support_correct d (length edges) weights pair
        (GammaOutput gamma) Houtput)); exact Houtput_support.
    + apply (proj2 (qformula_weights_positive_edges d edges weights pair Hnodup)).
      exact Hpositive.
    + apply (proj2 (qkirchhoff_balance_formula_correct d edges weights pair Hnodup)).
      exact Hbalance.
    + apply (proj2 (qdisplacement_formula_correct d edges weights pair Hnodup)).
      exact Hdisplacement.
Qed.

Theorem kirchhoff_relation_for_edges_qdefinable : forall d
    (gamma : ProductionTriple d) (edges : list (ProductionGraphEdge d)),
    NoDup edges ->
    QDefinable (fun pair : QVec (d + d) =>
      KirchhoffRelationForEdges gamma edges (qpair_left pair) (qpair_right pair)).
Proof.
  intros d gamma edges Hnodup. exists (qkirchhoff_relation_formula gamma edges).
  split; [apply qkirchhoff_relation_formula_closed|]. intro pair.
  unfold qkirchhoff_relation_formula. split.
  - intro Hrelation. apply finite_edge_weights_equiv in Hrelation; [|exact Hnodup].
    destruct Hrelation as [Hinput [Houtput [Hinput_support [Houtput_support
      [weights Hwitness]]]]].
    apply qexists_many_intro with (value := weights).
    apply (proj2 (qkirchhoff_relation_body_correct d gamma edges weights pair Hnodup)).
    exact (conj Hinput (conj Houtput
      (conj Hinput_support (conj Houtput_support Hwitness)))).
  - intro Hformula. apply qexists_many_elim in Hformula as [weights Hbody].
    apply finite_edge_weights_equiv; [exact Hnodup|].
    pose proof (proj1 (qkirchhoff_relation_body_correct d gamma edges weights pair
      Hnodup) Hbody) as [Hinput [Houtput [Hinput_support [Houtput_support Hwitness]]]].
    exact (conj Hinput (conj Houtput (conj Hinput_support
      (conj Houtput_support (ex_intro _ weights Hwitness))))).
Qed.

Lemma qdefinable_pointwise_congr : forall d (left right : QSet d),
    (forall value, left value <-> right value) ->
    QDefinable left -> QDefinable right.
Proof.
  intros d left right Hsame [formula [Hclosed Hformula]].
  exists formula. split; [exact Hclosed|]. intro value.
  rewrite <- Hformula. symmetry. apply Hsame.
Qed.

Theorem production_kirchhoff_relation_qdefinable : forall d
    (system : PlainVAS d) (gamma : ProductionTriple d),
    ValidProductionTriple system gamma ->
    QDefinable (fun pair : QVec (d + d) =>
      ProductionKirchhoffRelation system gamma
        (qpair_left pair) (qpair_right pair)).
Proof.
  intros d system gamma Hvalid.
  destruct (lemma_5_7_bounded_coordinates_intraproduction d system gamma Hvalid)
    as [witness [Hintra Hmask]].
  assert (Hwitness : Lemma57Witness system gamma witness) by
    (split; assumption).
  destruct (exact_production_graph_edges_exists d system gamma witness Hvalid Hwitness)
    as [edges Hedges].
  refine (qdefinable_pointwise_congr (d + d)
    (fun pair : QVec (d + d) => KirchhoffRelationForEdges gamma edges
      (qpair_left pair) (qpair_right pair))
    (fun pair : QVec (d + d) => ProductionKirchhoffRelation system gamma
      (qpair_left pair) (qpair_right pair)) _ _).
  - intro pair. symmetry. apply (production_kirchhoff_relation_fixed_edges
      d system gamma witness edges (qpair_left pair) (qpair_right pair));
      [exact Hwitness|exact Hedges].
  - apply kirchhoff_relation_for_edges_qdefinable. exact (proj1 Hedges).
Qed.
