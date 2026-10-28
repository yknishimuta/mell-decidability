From Coq Require Import Arith Fin Lia List Vector VectorSpec ZArith QArith Qring.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Geometry Require Import MathCompBridge QConeCore RationalHToV.
From Mell.Order Require Import PeriodicOrder.
From Mell.Semilinear Require Import Presentation LinearEquations.
From Mell.VAS Require Import Intraproductions ProductionGraph GraphParikh Kirchhoff
  KirchhoffRelation KirchhoffLemma514 GraphCyclePumping.

Import ListNotations.
Open Scope Q_scope.

Lemma clear_nonnegative_qvec : forall d (value : QVec d),
    NonnegativeQVec value ->
    exists (denominator : nat) (cleared : NVec d),
      (0 < denominator)%nat /\
      QVecEq (qvec_scale (q_of_nat denominator) value)
        (nvec_to_qvec cleared).
Proof.
  intros d value Hnonnegative.
  destruct (qvector_clear_denominators d (qvec_to_vector d value)) as
    [denominator [numerator [Hdenominator Hclear]]].
  exists denominator, (Vector.map Z.to_nat numerator). split; [assumption|].
  intro index. unfold qvec_scale, nvec_to_qvec.
  rewrite (Vector.nth_map Z.to_nat _ index index eq_refl).
  specialize (Hclear index). rewrite qvec_to_vector_nth in Hclear.
  assert (Hnumerator : (0 <= Vector.nth numerator index)%Z).
  { assert (Hq : 0 <= inject_Z (Vector.nth numerator index)).
    { setoid_rewrite Hclear. apply Qmult_le_0_compat.
      - unfold q_of_nat, Qle. cbn. lia.
      - apply Hnonnegative. }
    unfold Qle, inject_Z in Hq. cbn in Hq. lia. }
  unfold q_of_nat. rewrite Z2Nat.id by exact Hnumerator.
  symmetry. exact Hclear.
Qed.
Lemma clear_positive_qvec_coordinate : forall d (value : QVec d)
    denominator cleared (index : Fin.t d),
    (0 < denominator)%nat ->
    QVecEq (qvec_scale (q_of_nat denominator) value)
      (nvec_to_qvec cleared) ->
    0 < value index ->
    (0 < Vector.nth cleared index)%nat.
Proof.
  intros d value denominator cleared index Hdenominator Hclear Hpositive.
  specialize (Hclear index). unfold qvec_scale, nvec_to_qvec in Hclear.
  destruct (Vector.nth cleared index) eqn:Hcoordinate; [|lia].
  unfold q_of_nat in Hclear. cbn in Hclear.
  assert (0 < inject_Z (Z.of_nat denominator) * value index).
  { apply Qmult_lt_0_compat; [unfold Qlt, inject_Z; cbn; lia|exact Hpositive]. }
  setoid_rewrite Hclear in H. unfold Qlt, inject_Z in H. cbn in H. lia.
Qed.

Lemma qvec_clear_common_scale : forall d (left right : QVec d),
    NonnegativeQVec left -> NonnegativeQVec right ->
    exists multiplier left_nat right_nat,
      (0 < multiplier)%nat /\
      QVecEq (qvec_scale (q_of_nat multiplier) left)
        (nvec_to_qvec left_nat) /\
      QVecEq (qvec_scale (q_of_nat multiplier) right)
        (nvec_to_qvec right_nat).
Proof.
  intros d left right Hleft Hright.
  destruct (clear_nonnegative_qvec d left Hleft) as [dl [nl [Hdl Eleft]]].
  destruct (clear_nonnegative_qvec d right Hright) as [dr [nr [Hdr Eright]]].
  exists (dl * dr)%nat, (nvec_scale dr nl), (nvec_scale dl nr).
  split; [nia|]. split; intro index.
  - specialize (Eleft index).
    unfold qvec_scale, nvec_to_qvec, nvec_scale.
    rewrite (Vector.nth_map _ _ index index eq_refl).
    unfold qvec_scale, nvec_to_qvec in Eleft.
    unfold q_of_nat in *. rewrite Nat2Z.inj_mul, Nat2Z.inj_mul, inject_Z_mult.
    transitivity (inject_Z (Z.of_nat dr) *
      (inject_Z (Z.of_nat dl) * left index)); [ring|].
    setoid_rewrite Eleft. reflexivity.
  - specialize (Eright index).
    unfold qvec_scale, nvec_to_qvec, nvec_scale.
    rewrite (Vector.nth_map _ _ index index eq_refl).
    unfold qvec_scale, nvec_to_qvec in Eright.
    unfold q_of_nat in *. rewrite Nat2Z.inj_mul, Nat2Z.inj_mul, inject_Z_mult.
    transitivity (inject_Z (Z.of_nat dl) *
      (inject_Z (Z.of_nat dr) * right index)); [ring|].
    setoid_rewrite Eright. reflexivity.
Qed.

Lemma vector_nth_of_list_in : forall A (values : list A)
    (index : Fin.t (length values)),
    List.In (Vector.nth (Vector.of_list values) index) values.
Proof.
  intros A values index. rewrite <- to_list_of_list_opp.
  apply (proj1 (VectorSpec.to_list_In _ _ _ _)), Vector.In_nth.
Qed.

Lemma edge_weight_lookup_qvec_ext : forall d edges
    (left right : QVec (length edges)) edge,
    QVecEq left right ->
    @EdgeWeightLookup d edges left edge == EdgeWeightLookup edges right edge.
Proof.
  intros d edges. induction edges as [|head tail IH]; intros left right edge Heq;
    cbn [EdgeWeightLookup]; [reflexivity|].
  destruct (production_graph_edge_eq_dec edge head).
  - apply Heq.
  - apply IH. intro index. apply (Heq (Fin.FS index)).
Qed.

Lemma edge_weight_lookup_scale : forall d edges coefficient
    (weights : QVec (length edges)) edge,
    @EdgeWeightLookup d edges (qvec_scale coefficient weights) edge ==
      coefficient * EdgeWeightLookup edges weights edge.
Proof.
  intros d edges. induction edges as [|head tail IH];
    intros coefficient weights edge; cbn [EdgeWeightLookup].
  - ring.
  - destruct (production_graph_edge_eq_dec edge head).
    + reflexivity.
    + apply IH.
Qed.

Fixpoint EdgeWeightLookupNat {d} (edges : list (ProductionGraphEdge d)) :
    NVec (length edges) -> ProductionGraphEdge d -> nat :=
  match edges as listed return NVec (length listed) -> ProductionGraphEdge d -> nat with
  | [] => fun _ _ => 0%nat
  | head :: tail => fun weights edge =>
      if production_graph_edge_eq_dec edge head
      then Vector.nth weights Fin.F1
      else EdgeWeightLookupNat tail (Vector.tl weights) edge
  end.

Lemma edge_weight_lookup_nat_embedding : forall d edges
    (weights : NVec (length edges)) edge,
    @EdgeWeightLookup d edges (fun index => q_of_nat (Vector.nth weights index))
      edge == q_of_nat (EdgeWeightLookupNat edges weights edge).
Proof.
  intros d edges. induction edges as [|head tail IH]; intros weights edge.
  - cbn [EdgeWeightLookup EdgeWeightLookupNat]. reflexivity.
  - refine (Vector.caseS' weights (fun weights =>
      EdgeWeightLookup (head :: tail)
        (fun index => q_of_nat (Vector.nth weights index)) edge ==
      q_of_nat (EdgeWeightLookupNat (head :: tail) weights edge)) _).
    intros first rest. cbn [EdgeWeightLookup EdgeWeightLookupNat].
    destruct (production_graph_edge_eq_dec edge head); [reflexivity|apply IH].
Qed.

Lemma edge_weights_nonnegative : forall d edges
    (weight : ProductionGraphEdge d -> Q),
    (forall edge, List.In edge edges -> 0 < weight edge) ->
    NonnegativeQVec (EdgeWeightVectorOfFunction edges weight).
Proof.
  intros d edges weight Hpositive index. unfold EdgeWeightVectorOfFunction.
  apply Qlt_le_weak, Hpositive, vector_nth_of_list_in.
Qed.

Lemma clear_positive_edge_weights : forall d edges
    (weight : ProductionGraphEdge d -> Q),
    NoDup edges ->
    (forall edge, List.In edge edges -> 0 < weight edge) ->
    exists denominator (cleared : NVec (length edges)),
      (0 < denominator)%nat /\
      QVecEq
        (qvec_scale (q_of_nat denominator)
          (EdgeWeightVectorOfFunction edges weight))
        (nvec_to_qvec cleared) /\
      (forall edge, List.In edge edges ->
        (0 < EdgeWeightLookupNat edges cleared edge)%nat).
Proof.
  intros d edges weight Hnodup Hpositive.
  destruct (clear_nonnegative_qvec (length edges)
    (EdgeWeightVectorOfFunction edges weight)
    (edge_weights_nonnegative d edges weight Hpositive))
    as [denominator [cleared [Hdenominator Hclear]]].
  exists denominator, cleared. repeat split; try assumption.
  intros edge Hin.
  assert (Hlookup :
    q_of_nat (EdgeWeightLookupNat edges cleared edge) ==
    q_of_nat denominator * weight edge).
  { symmetry. eapply Qeq_trans.
    - apply Qmult_comp; [reflexivity|]. symmetry.
      exact (edge_weight_lookup_of_function d edges weight edge Hnodup Hin).
    - eapply Qeq_trans.
      + symmetry. apply edge_weight_lookup_scale.
      + eapply Qeq_trans.
        * apply edge_weight_lookup_qvec_ext. exact Hclear.
        * eapply Qeq_trans; [apply edge_weight_lookup_nat_embedding|].
          reflexivity. }
  destruct (EdgeWeightLookupNat edges cleared edge) eqn:Hzero; [|lia].
  unfold q_of_nat in Hlookup. cbn in Hlookup.
  assert (Hproduct : 0 < q_of_nat denominator * weight edge).
  { apply Qmult_lt_0_compat.
    - unfold q_of_nat, Qlt. cbn. lia.
    - now apply Hpositive. }
  setoid_rewrite <- Hlookup in Hproduct.
  unfold q_of_nat, Qlt, inject_Z in Hproduct. cbn in Hproduct. lia.
Qed.

Lemma qvec_clear_multiply : forall d denominator multiplier
    (value : QVec d) (cleared : NVec d),
    QVecEq (qvec_scale (q_of_nat denominator) value)
      (nvec_to_qvec cleared) ->
    QVecEq (qvec_scale (q_of_nat (denominator * multiplier)) value)
      (nvec_to_qvec (nvec_scale multiplier cleared)).
Proof.
  intros d denominator multiplier value cleared H index.
  specialize (H index). unfold qvec_scale, nvec_to_qvec, nvec_scale in *.
  rewrite (Vector.nth_map _ _ index index eq_refl).
  unfold q_of_nat in *. rewrite !Nat2Z.inj_mul, !inject_Z_mult.
  transitivity (inject_Z (Z.of_nat multiplier) *
    (inject_Z (Z.of_nat denominator) * value index)); [ring|].
  setoid_rewrite H. reflexivity.
Qed.

Lemma edge_weight_lookup_nat_scale : forall d edges coefficient
    (weights : NVec (length edges)) edge,
    @EdgeWeightLookupNat d edges (nvec_scale coefficient weights) edge =
      (coefficient * EdgeWeightLookupNat edges weights edge)%nat.
Proof.
  intros d edges. induction edges as [|head tail IH]; intros coefficient weights edge.
  - cbn [EdgeWeightLookupNat nvec_scale]. lia.
  - refine (Vector.caseS' weights (fun weights =>
      EdgeWeightLookupNat (head :: tail) (nvec_scale coefficient weights) edge =
      (coefficient * EdgeWeightLookupNat (head :: tail) weights edge)%nat) _).
    intros first rest. cbn [EdgeWeightLookupNat nvec_scale].
    destruct (production_graph_edge_eq_dec edge head); [reflexivity|apply IH].
Qed.

Fixpoint EdgeWeightMass {d} (edges : list (ProductionGraphEdge d))
    (weight : ProductionGraphEdge d -> nat) : nat :=
  match edges with
  | [] => 0%nat
  | edge :: tail => (weight edge + EdgeWeightMass tail weight)%nat
  end.

Lemma edge_weight_le_mass : forall d edges weight edge,
    List.In edge edges ->
    (weight edge <= @EdgeWeightMass d edges weight)%nat.
Proof.
  intros d edges; induction edges as [|head tail IH]; intros weight edge Hin;
    cbn in *; [contradiction|].
  destruct Hin as [<-|Hin]; [lia|]. specialize (IH weight edge Hin). lia.
Qed.

Lemma kirchhoff_balance_nat_of_q_embedding : forall d edges weight,
    @KirchhoffBalanceQ d edges (fun edge => q_of_nat (weight edge)) ->
    KirchhoffBalanceNat edges weight.
Proof.
  intros d edges weight Hbalance state.
  specialize (Hbalance state).
  pose proof (graph_weight_sum_nat_to_q d edges weight (EdgeLeaves state)) as Hl.
  pose proof (graph_weight_sum_nat_to_q d edges weight (EdgeEnters state)) as Hr.
  apply Nat2Z.inj, (proj1 (inject_Z_injective _ _)).
  eapply Qeq_trans; [symmetry; exact Hl|].
  eapply Qeq_trans; [exact Hbalance|exact Hr].
Qed.

Lemma kirchhoff_displacement_nat_endpoint : forall d edges weight
    (input output : NVec d),
    QVecEq (KirchhoffDisplacementQ edges (fun edge => q_of_nat (weight edge)))
      (QVecDifference (nvec_to_qvec output) (nvec_to_qvec input)) ->
    nvec_to_zvec output = zvec_add (nvec_to_zvec input)
      (KirchhoffDisplacementNat edges weight).
Proof.
  intros d edges weight input output H.
  pose proof (kirchhoff_displacement_nat_to_q d edges weight) as Hnat.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index other <-.
  specialize (H index). specialize (Hnat index).
  unfold QVecDifference, nvec_to_qvec, nvec_to_zvec, zvec_add in *.
  rewrite (Vector.nth_map Z.of_nat _ index index eq_refl),
    (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (Vector.nth_map Z.of_nat _ index index eq_refl) in *.
  unfold zvec_to_qvec in Hnat.
  transitivity
    (Z.of_nat (Vector.nth input index) +
     Vector.nth (KirchhoffDisplacementNat edges weight) index)%Z; [|reflexivity].
  apply (proj1 (inject_Z_injective _ _)).
  rewrite inject_Z_plus. unfold q_of_nat in *.
  setoid_rewrite <- Hnat. setoid_rewrite H. unfold Qminus. ring.
Qed.

Theorem positive_rational_kirchhoff_uniform_scaling : forall d
    (gamma : ProductionTriple d) edges (input output : QVec d)
    (weight : ProductionGraphEdge d -> Q) multiplier
    (prefix suffix : ProductionGraphEdge d -> nat),
    NoDup edges ->
    NonnegativeQVec input -> NonnegativeQVec output ->
    SamePositiveSupport input (GammaInput gamma) ->
    SamePositiveSupport output (GammaOutput gamma) ->
    KirchhoffBalanceQ edges weight ->
    (forall edge, List.In edge edges -> 0 < weight edge) ->
    QVecEq (QVecDifference output input)
      (KirchhoffDisplacementQ edges weight) ->
    exists scale (scaled_input scaled_output : NVec d)
      (scaled_weight : ProductionGraphEdge d -> nat),
      (0 < scale)%nat /\
      QVecEq (qvec_scale (q_of_nat scale) input)
        (nvec_to_qvec scaled_input) /\
      QVecEq (qvec_scale (q_of_nat scale) output)
        (nvec_to_qvec scaled_output) /\
      nvec_le (nvec_scale multiplier (GammaInput gamma)) scaled_input /\
      nvec_le (nvec_scale multiplier (GammaOutput gamma)) scaled_output /\
      KirchhoffBalanceNat edges scaled_weight /\
      (forall edge, List.In edge edges ->
        (prefix edge + suffix edge < scaled_weight edge)%nat) /\
      nvec_to_zvec scaled_output = zvec_add (nvec_to_zvec scaled_input)
        (KirchhoffDisplacementNat edges scaled_weight).
Proof.
  intros d gamma edges input output weight multiplier prefix suffix Hnodup
    Hinput_nonnegative Houtput_nonnegative Hinput_support Houtput_support
    Hbalance Hpositive Hdisplacement.
  destruct (qvec_clear_common_scale d input output Hinput_nonnegative
    Houtput_nonnegative) as [duv [input0 [output0 [Hduv [Hinput0 Houtput0]]]]].
  destruct (clear_positive_edge_weights d edges weight Hnodup Hpositive)
    as [dw [weights0 [Hdw [Hweights0 Hweights0_positive]]]].
  set (common := (duv * dw)%nat).
  set (base_input := nvec_scale dw input0).
  set (base_output := nvec_scale dw output0).
  set (base_weights_vec := nvec_scale duv weights0).
  set (base_weight := fun edge => EdgeWeightLookupNat edges base_weights_vec edge).
  assert (Hcommon_positive : (0 < common)%nat) by (unfold common; nia).
  assert (Hbase_input : QVecEq (qvec_scale (q_of_nat common) input)
      (nvec_to_qvec base_input)).
  { unfold common, base_input. now apply qvec_clear_multiply. }
  assert (Hbase_output : QVecEq (qvec_scale (q_of_nat common) output)
      (nvec_to_qvec base_output)).
  { unfold common, base_output. now apply qvec_clear_multiply. }
  assert (Hweights_combined : QVecEq
      (qvec_scale (q_of_nat common) (EdgeWeightVectorOfFunction edges weight))
      (nvec_to_qvec base_weights_vec)).
  { unfold common, base_weights_vec.
    rewrite Nat.mul_comm. now apply qvec_clear_multiply. }
  assert (Hbase_weight_q : forall edge, List.In edge edges ->
      q_of_nat (base_weight edge) == q_of_nat common * weight edge).
  { intros edge Hin. unfold base_weight.
    eapply Qeq_trans; [symmetry; apply edge_weight_lookup_nat_embedding|].
    eapply Qeq_trans.
    - apply edge_weight_lookup_qvec_ext, qvec_eq_sym. exact Hweights_combined.
    - eapply Qeq_trans; [apply edge_weight_lookup_scale|].
      apply Qmult_comp; [reflexivity|].
      now apply edge_weight_lookup_of_function. }
  assert (Hbase_balance : KirchhoffBalanceNat edges base_weight).
  { apply kirchhoff_balance_nat_of_q_embedding.
    intro state. eapply Qeq_trans.
    - apply graph_weight_sum_q_ext. exact Hbase_weight_q.
    - eapply Qeq_trans; [apply graph_weight_sum_q_scale|].
      eapply Qeq_trans.
      + apply Qmult_comp; [reflexivity|apply Hbalance].
      + eapply Qeq_trans; [symmetry; apply graph_weight_sum_q_scale|].
        symmetry. apply graph_weight_sum_q_ext. exact Hbase_weight_q. }
  assert (Hbase_displacement_q : QVecEq
      (KirchhoffDisplacementQ edges (fun edge => q_of_nat (base_weight edge)))
      (QVecDifference (nvec_to_qvec base_output) (nvec_to_qvec base_input))).
  { intro index.
    eapply Qeq_trans.
    - apply kirchhoff_displacement_q_ext. exact Hbase_weight_q.
    - eapply Qeq_trans.
      + apply kirchhoff_displacement_q_scale_local.
      + specialize (Hdisplacement index).
        specialize (Hbase_input index). specialize (Hbase_output index).
        unfold qvec_scale, QVecDifference, nvec_to_qvec in *.
        setoid_rewrite <- Hdisplacement. setoid_rewrite <- Hbase_output.
        setoid_rewrite <- Hbase_input. ring. }
  assert (Hbase_endpoint : nvec_to_zvec base_output =
      zvec_add (nvec_to_zvec base_input)
        (KirchhoffDisplacementNat edges base_weight)).
  { now apply kirchhoff_displacement_nat_endpoint. }
  set (mass := EdgeWeightMass edges
    (fun edge => (prefix edge + suffix edge)%nat)).
  set (boost := S (multiplier *
    (nvec_norm (GammaInput gamma) + nvec_norm (GammaOutput gamma)) + mass)).
  set (scaled_input := nvec_scale boost base_input).
  set (scaled_output := nvec_scale boost base_output).
  set (scaled_weight := fun edge => (boost * base_weight edge)%nat).
  exists (boost * common)%nat, scaled_input, scaled_output, scaled_weight.
  repeat split.
  - unfold boost. nia.
  - unfold scaled_input. rewrite Nat.mul_comm.
    apply qvec_clear_multiply. exact Hbase_input.
  - unfold scaled_output. rewrite Nat.mul_comm.
    apply qvec_clear_multiply. exact Hbase_output.
  - intro index. unfold scaled_input, nvec_scale.
    repeat rewrite (Vector.nth_map _ _ index index eq_refl).
    destruct (Nat.eq_dec (Vector.nth (GammaInput gamma) index) 0%nat)
      as [Hzero|Hnonzero].
    + rewrite Hzero. cbn. lia.
    + assert (Hqpositive : 0 < input index).
      { apply (proj2 (Hinput_support index)).
        unfold nvec_to_qvec, q_of_nat, Qlt, inject_Z. cbn. lia. }
      assert (Hbase_positive : (0 < Vector.nth base_input index)%nat).
      { apply (clear_positive_qvec_coordinate d input common base_input index
          Hcommon_positive Hbase_input Hqpositive). }
      pose proof (nvec_coordinate_le_norm d (GammaInput gamma) index).
      unfold boost. nia.
  - intro index. unfold scaled_output, nvec_scale.
    repeat rewrite (Vector.nth_map _ _ index index eq_refl).
    destruct (Nat.eq_dec (Vector.nth (GammaOutput gamma) index) 0%nat)
      as [Hzero|Hnonzero].
    + rewrite Hzero. cbn. lia.
    + assert (Hqpositive : 0 < output index).
      { apply (proj2 (Houtput_support index)).
        unfold nvec_to_qvec, q_of_nat, Qlt, inject_Z. cbn. lia. }
      assert (Hbase_positive : (0 < Vector.nth base_output index)%nat).
      { apply (clear_positive_qvec_coordinate d output common base_output index
          Hcommon_positive Hbase_output Hqpositive). }
      pose proof (nvec_coordinate_le_norm d (GammaOutput gamma) index).
      unfold boost. nia.
  - unfold scaled_weight. now apply kirchhoff_balance_nat_nsmul.
  - intros edge Hin.
    assert (Hmass : (prefix edge + suffix edge <= mass)%nat).
    { unfold mass. exact (edge_weight_le_mass d edges
        (fun item => (prefix item + suffix item)%nat) edge Hin). }
    assert (Hbase_positive : (0 < base_weight edge)%nat).
    { unfold base_weight, base_weights_vec.
      rewrite edge_weight_lookup_nat_scale.
      specialize (Hweights0_positive edge Hin). nia. }
    unfold scaled_weight, boost. nia.
  - apply kirchhoff_displacement_nat_endpoint.
    intro index. unfold scaled_weight, scaled_input, scaled_output.
    eapply Qeq_trans.
    + apply kirchhoff_displacement_q_ext. intros edge Hin.
      unfold q_of_nat. rewrite Nat2Z.inj_mul, inject_Z_mult. reflexivity.
    + eapply Qeq_trans; [apply kirchhoff_displacement_q_scale_local|].
      pose proof (kirchhoff_displacement_nat_to_q d edges base_weight index)
        as Hnat.
      specialize (Hbase_displacement_q index).
      unfold QVecDifference, nvec_to_qvec, nvec_scale, qvec_scale in *.
      repeat rewrite (Vector.nth_map _ _ index index eq_refl).
      unfold q_of_nat in *. rewrite !Nat2Z.inj_mul, !inject_Z_mult.
      setoid_rewrite Hbase_displacement_q. ring.
Qed.

Lemma kirchhoff_balance_nat_residual : forall d edges total removed,
    @KirchhoffBalanceNat d edges total ->
    KirchhoffBalanceNat edges removed ->
    (forall edge, List.In edge edges -> (removed edge <= total edge)%nat) ->
    KirchhoffBalanceNat edges
      (fun edge => (total edge - removed edge)%nat).
Proof.
  intros d edges total removed Htotal Hremoved Hle state.
  assert (Hpoint : forall edge, List.In edge edges ->
      total edge = (removed edge + (total edge - removed edge))%nat).
  { intros edge Hin. specialize (Hle edge Hin). lia. }
  pose proof (graph_weight_sum_nat_ext d edges total
    (fun edge => (removed edge + (total edge - removed edge))%nat)
    (EdgeLeaves state) Hpoint) as Hleave.
  pose proof (graph_weight_sum_nat_ext d edges total
    (fun edge => (removed edge + (total edge - removed edge))%nat)
    (EdgeEnters state) Hpoint) as Henter.
  rewrite graph_weight_sum_nat_add in Hleave, Henter.
  specialize (Htotal state). specialize (Hremoved state). lia.
Qed.

Lemma kirchhoff_displacement_q_add_local : forall d edges left right,
    QVecEq (@KirchhoffDisplacementQ d edges
      (fun edge => left edge + right edge))
      (qvec_add (KirchhoffDisplacementQ edges left)
        (KirchhoffDisplacementQ edges right)).
Proof.
  intros d edges; induction edges as [|edge tail IH]; intros left right index.
  - cbn [KirchhoffDisplacementQ qvec_rsum]. unfold qvec_add, qvec_zero.
    symmetry. apply Qplus_0_l.
  - change (qvec_add
      (qvec_scale (left edge + right edge)
        (zvec_to_qvec (RunEdgeAction edge)))
      (KirchhoffDisplacementQ tail (fun e => left e + right e)) index ==
      qvec_add
        (qvec_add (qvec_scale (left edge) (zvec_to_qvec (RunEdgeAction edge)))
          (KirchhoffDisplacementQ tail left))
        (qvec_add (qvec_scale (right edge) (zvec_to_qvec (RunEdgeAction edge)))
          (KirchhoffDisplacementQ tail right)) index).
    unfold qvec_add, qvec_scale. setoid_rewrite (IH left right index).
    unfold qvec_add. ring.
Qed.

Lemma kirchhoff_displacement_nat_add : forall d edges left right,
    @KirchhoffDisplacementNat d edges (fun edge => left edge + right edge)%nat =
      zvec_add (KirchhoffDisplacementNat edges left)
        (KirchhoffDisplacementNat edges right).
Proof.
  intros d edges left right.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index other <-.
  apply (proj1 (inject_Z_injective _ _)).
  unfold zvec_add. rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl),
    inject_Z_plus.
  pose proof (kirchhoff_displacement_nat_to_q d edges
    (fun edge => left edge + right edge)%nat index) as Hsum.
  pose proof (kirchhoff_displacement_nat_to_q d edges left index) as Hl.
  pose proof (kirchhoff_displacement_nat_to_q d edges right index) as Hr.
  eapply Qeq_trans; [symmetry; exact Hsum|].
  eapply Qeq_trans.
  - apply kirchhoff_displacement_q_ext. intros edge Hin.
    unfold q_of_nat. rewrite Nat2Z.inj_add, inject_Z_plus. reflexivity.
  eapply Qeq_trans; [apply kirchhoff_displacement_q_add_local|].
  unfold qvec_add. apply Qplus_comp; assumption.
Qed.

Lemma kirchhoff_displacement_nat_ext : forall d edges left right,
    (forall edge, List.In edge edges -> left edge = right edge) ->
    @KirchhoffDisplacementNat d edges left = KirchhoffDisplacementNat edges right.
Proof.
  intros d edges left right Heq.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index other <-.
  apply (proj1 (inject_Z_injective _ _)).
  pose proof (kirchhoff_displacement_nat_to_q d edges left index) as Hl.
  pose proof (kirchhoff_displacement_nat_to_q d edges right index) as Hr.
  eapply Qeq_trans; [symmetry; exact Hl|].
  eapply Qeq_trans.
  - apply kirchhoff_displacement_q_ext. intros edge Hin.
    now rewrite Heq.
  - exact Hr.
Qed.

Theorem positive_residual_kirchhoff : forall d edges
    (total removed : ProductionGraphEdge d -> nat)
    (input output removed_input removed_output : NVec d),
    KirchhoffBalanceNat edges total ->
    KirchhoffBalanceNat edges removed ->
    (forall edge, List.In edge edges ->
      (removed edge < total edge)%nat) ->
    nvec_le removed_input input -> nvec_le removed_output output ->
    nvec_to_zvec output = zvec_add (nvec_to_zvec input)
      (KirchhoffDisplacementNat edges total) ->
    nvec_to_zvec removed_output = zvec_add (nvec_to_zvec removed_input)
      (KirchhoffDisplacementNat edges removed) ->
    let residual_input := nvec_sub input removed_input in
    let residual_output := nvec_sub output removed_output in
    let residual_weight := fun edge => (total edge - removed edge)%nat in
    KirchhoffBalanceNat edges residual_weight /\
    (forall edge, List.In edge edges -> (0 < residual_weight edge)%nat) /\
    nvec_to_zvec residual_output = zvec_add (nvec_to_zvec residual_input)
      (KirchhoffDisplacementNat edges residual_weight).
Proof.
  intros d edges total removed input output removed_input removed_output
    Htotal Hremoved Hstrict Hinput_le Houtput_le Htotal_endpoint
    Hremoved_endpoint. cbn.
  assert (Hresidual_balance : KirchhoffBalanceNat edges
      (fun edge => total edge - removed edge)%nat).
  { apply kirchhoff_balance_nat_residual; try assumption.
    intros edge Hin. specialize (Hstrict edge Hin). lia. }
  split; [exact Hresidual_balance|]. split.
  - intros edge Hin. specialize (Hstrict edge Hin). lia.
  - pose proof (nvec_sub_exact d removed_input input Hinput_le) as Hinput_exact.
    pose proof (nvec_sub_exact d removed_output output Houtput_le) as Houtput_exact.
    assert (Hweight_exact : forall edge, List.In edge edges ->
        total edge = (removed edge + (total edge - removed edge))%nat).
    { intros edge Hin. specialize (Hstrict edge Hin). lia. }
    assert (Hdisp : KirchhoffDisplacementNat edges total =
        zvec_add (KirchhoffDisplacementNat edges removed)
          (KirchhoffDisplacementNat edges
            (fun edge => total edge - removed edge)%nat)).
    { transitivity (KirchhoffDisplacementNat edges
        (fun edge => removed edge + (total edge - removed edge))%nat).
      - apply kirchhoff_displacement_nat_ext. intros edge Hin.
        exact (Hweight_exact edge Hin).
      - apply kirchhoff_displacement_nat_add. }
    apply (proj1 (Vector.eq_nth_iff Z d _ _)). intros index other <-.
    pose proof (f_equal (fun v : ZVec d => Vector.nth v index)
      Htotal_endpoint) as Htotali.
    pose proof (f_equal (fun v : ZVec d => Vector.nth v index)
      Hremoved_endpoint) as Hremovedi.
    pose proof (f_equal (fun v : NVec d => Vector.nth v index)
      Hinput_exact) as Hinputi.
    pose proof (f_equal (fun v : NVec d => Vector.nth v index)
      Houtput_exact) as Houtputi.
    pose proof (f_equal (fun v : ZVec d => Vector.nth v index) Hdisp) as Hdispi.
    unfold nvec_sub, nvec_add, nvec_to_zvec, zvec_add in *.
    repeat rewrite (Vector.nth_map2 Nat.sub _ _ index index index eq_refl eq_refl)
      in *.
    repeat rewrite (Vector.nth_map Z.of_nat _ index index eq_refl) in *.
    repeat rewrite (Vector.nth_map2 Nat.sub _ _ index index index eq_refl eq_refl)
      in *.
    repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl)
      in *.
    repeat rewrite (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl)
      in *.
    rewrite (Nat2Z.inj_sub _ _ (Houtput_le index)).
    rewrite (Vector.nth_map Z.of_nat _ index index eq_refl),
      (Vector.nth_map2 Nat.sub _ _ index index index eq_refl eq_refl).
    rewrite (Nat2Z.inj_sub _ _ (Hinput_le index)).
    rewrite (Vector.nth_map Z.of_nat _ index index eq_refl) in Htotali.
    rewrite (Vector.nth_map Z.of_nat _ index index eq_refl) in Hremovedi.
    lia.
Qed.
