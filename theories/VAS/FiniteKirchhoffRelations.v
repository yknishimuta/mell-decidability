From Coq Require Import Arith Bool Fin Lia List Vector ZArith QArith Qring
  Classical_Prop Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import MathCompBridge QConeCore.
From Mell.VAS Require Import Runs Transformer Intraproductions ProductionGraph
  ProductionGraphFiniteness Kirchhoff KirchhoffRelation
  KirchhoffDefinability KirchhoffLemma514.

Import ListNotations.
Open Scope Q_scope.

Lemma nonnegative_qvec_positive_scale : forall d coefficient (value : QVec d),
    0 < coefficient -> NonnegativeQVec value ->
    NonnegativeQVec (qvec_scale coefficient value).
Proof.
  intros d coefficient value Hcoefficient Hvalue index.
  unfold qvec_scale. apply Qmult_le_0_compat.
  - now apply Qlt_le_weak.
  - apply Hvalue.
Qed.

Lemma qvec_difference_scale : forall d coefficient
    (left right : QVec d),
    QVecEq
      (QVecDifference (qvec_scale coefficient left)
        (qvec_scale coefficient right))
      (qvec_scale coefficient (QVecDifference left right)).
Proof.
  intros d coefficient left right index.
  unfold QVecDifference, qvec_scale. ring.
Qed.

Lemma kirchhoff_relation_for_edges_positive_scale : forall d gamma edges
    coefficient (input output : QVec d),
    0 < coefficient ->
    @KirchhoffRelationForEdges d gamma edges input output ->
    KirchhoffRelationForEdges gamma edges
      (qvec_scale coefficient input) (qvec_scale coefficient output).
Proof.
  intros d gamma edges coefficient input output Hcoefficient
    [Hinput [Houtput [Hinput_support [Houtput_support
      [weight [Hbalance [Hpositive Hdisplacement]]]]]]].
  split; [now apply nonnegative_qvec_positive_scale|].
  split; [now apply nonnegative_qvec_positive_scale|].
  split.
  - apply (proj2 (same_positive_support_positive_scale
      d coefficient input (GammaInput gamma) Hcoefficient)). exact Hinput_support.
  - split.
    + apply (proj2 (same_positive_support_positive_scale
      d coefficient output (GammaOutput gamma) Hcoefficient)). exact Houtput_support.
    + exists (fun edge => coefficient * weight edge). repeat split.
    + now apply kirchhoff_balance_q_scale.
    + intros edge Hedge. apply Qmult_lt_0_compat; [exact Hcoefficient|].
      now apply Hpositive.
    + eapply qvec_eq_trans; [apply qvec_difference_scale|].
      eapply qvec_eq_trans.
      * apply qvec_eq_scale; [reflexivity|exact Hdisplacement].
      * apply qvec_eq_sym, kirchhoff_displacement_q_scale_local.
Qed.

Theorem production_kirchhoff_positive_scale : forall d system gamma
    coefficient (input output : QVec d),
    0 < coefficient ->
    @ProductionKirchhoffRelation d system gamma input output ->
    ProductionKirchhoffRelation system gamma
      (qvec_scale coefficient input) (qvec_scale coefficient output).
Proof.
  intros d system gamma coefficient input output Hcoefficient
    [witness [edges [Hwitness [Hedges Hrelation]]]].
  exists witness, edges. split; [exact Hwitness|]. split; [exact Hedges|].
  now apply kirchhoff_relation_for_edges_positive_scale.
Qed.

Lemma kirchhoff_relation_for_edges_qvec_ext : forall d gamma edges
    input input' output output',
    QVecEq input input' -> QVecEq output output' ->
    (@KirchhoffRelationForEdges d gamma edges input output <->
     KirchhoffRelationForEdges gamma edges input' output').
Proof.
  intros d gamma edges input input' output output' Hinput Houtput.
  unfold KirchhoffRelationForEdges. split.
  - intros [Hin [Hout [Hsin [Hsout [weight [Hb [Hp Hd]]]]]]].
    split; [now apply (proj1 (nonnegative_qvec_ext d input input' Hinput))|].
    split; [now apply (proj1 (nonnegative_qvec_ext d output output' Houtput))|].
    split; [now apply (proj1 (same_positive_support_ext d input input'
        (GammaInput gamma) Hinput))|].
    split; [now apply (proj1 (same_positive_support_ext d output output'
        (GammaOutput gamma) Houtput))|].
    exists weight. split; [exact Hb|]. split; [exact Hp|].
      eapply qvec_eq_trans; [|exact Hd]. intro index.
      unfold QVecDifference. apply Qplus_comp.
      * apply qvec_eq_sym, Houtput.
      * apply Qopp_comp, qvec_eq_sym, Hinput.
  - intros [Hin [Hout [Hsin [Hsout [weight [Hb [Hp Hd]]]]]]].
    split; [now apply (proj2 (nonnegative_qvec_ext d input input' Hinput))|].
    split; [now apply (proj2 (nonnegative_qvec_ext d output output' Houtput))|].
    split; [now apply (proj2 (same_positive_support_ext d input input'
        (GammaInput gamma) Hinput))|].
    split; [now apply (proj2 (same_positive_support_ext d output output'
        (GammaOutput gamma) Houtput))|].
    exists weight. split; [exact Hb|]. split; [exact Hp|].
      eapply qvec_eq_trans; [|exact Hd]. intro index.
      unfold QVecDifference. apply Qplus_comp.
      * apply Houtput.
      * apply Qopp_comp, Hinput.
Qed.

Lemma production_kirchhoff_qvec_ext : forall d system gamma
    input input' output output',
    QVecEq input input' -> QVecEq output output' ->
    (@ProductionKirchhoffRelation d system gamma input output <->
     ProductionKirchhoffRelation system gamma input' output').
Proof.
  intros d system gamma input input' output output' Hinput Houtput. split.
  - intros [witness [edges [Hw [He Hr]]]]. exists witness, edges.
    split; [exact Hw|]. split; [exact He|].
    apply (proj1 (kirchhoff_relation_for_edges_qvec_ext d gamma edges
      input input' output output' Hinput Houtput)). exact Hr.
  - intros [witness [edges [Hw [He Hr]]]]. exists witness, edges.
    split; [exact Hw|]. split; [exact He|].
    apply (proj2 (kirchhoff_relation_for_edges_qvec_ext d gamma edges
      input input' output output' Hinput Houtput)). exact Hr.
Qed.

Lemma production_kirchhoff_positive_scale_iff : forall d system gamma
    coefficient (input output : QVec d),
    0 < coefficient ->
    (@ProductionKirchhoffRelation d system gamma
      (qvec_scale coefficient input) (qvec_scale coefficient output) <->
     ProductionKirchhoffRelation system gamma input output).
Proof.
  intros d system gamma coefficient input output Hcoefficient. split.
  - intro Hscaled.
    pose proof (production_kirchhoff_positive_scale d system gamma
      (/ coefficient) _ _ (Qinv_lt_0_compat coefficient Hcoefficient) Hscaled)
      as Hunscaled.
    destruct Hunscaled as [witness [edges [Hw [He Hr]]]].
    exists witness, edges. split; [exact Hw|]. split; [exact He|].
    destruct Hr as [Hin [Hout [Hsin [Hsout [weight Hweight]]]]].
    assert (Hinput_cancel : QVecEq input
        (qvec_scale (/ coefficient) (qvec_scale coefficient input))).
    { intro index. unfold qvec_scale. symmetry. field.
      intro Hzero. apply (Qlt_not_eq 0 coefficient Hcoefficient).
      now symmetry. }
    assert (Houtput_cancel : QVecEq output
        (qvec_scale (/ coefficient) (qvec_scale coefficient output))).
    { intro index. unfold qvec_scale. symmetry. field.
      intro Hzero. apply (Qlt_not_eq 0 coefficient Hcoefficient).
      now symmetry. }
    split.
    + apply (proj2 (nonnegative_qvec_ext d _ _ Hinput_cancel)). exact Hin.
    + split.
      * apply (proj2 (nonnegative_qvec_ext d _ _ Houtput_cancel)). exact Hout.
      * split.
        -- apply (proj2 (same_positive_support_ext d _ _ _ Hinput_cancel)).
           exact Hsin.
        -- split.
           ++ apply (proj2 (same_positive_support_ext d _ _ _ Houtput_cancel)).
              exact Hsout.
           ++ destruct Hweight as [Hbalance [Hpositive Hdisplacement]].
              exists weight. split; [exact Hbalance|]. split; [exact Hpositive|].
              eapply qvec_eq_trans; [|exact Hdisplacement].
              intro index. unfold QVecDifference.
              apply Qplus_comp; [apply Houtput_cancel|].
              apply Qopp_comp. apply Hinput_cancel.
  - now apply production_kirchhoff_positive_scale.
Qed.

Definition GammaInputSupportMask {d} (gamma : ProductionTriple d) :
    BoundedMask d := Vector.map (fun value => Nat.ltb 0 value) (GammaInput gamma).

Definition GammaOutputSupportMask {d} (gamma : ProductionTriple d) :
    BoundedMask d := Vector.map (fun value => Nat.ltb 0 value) (GammaOutput gamma).

Lemma gamma_input_support_mask_nth : forall d (gamma : ProductionTriple d) index,
    Vector.nth (GammaInputSupportMask gamma) index = true <->
    (0 < Vector.nth (GammaInput gamma) index)%nat.
Proof.
  intros. unfold GammaInputSupportMask.
  rewrite (Vector.nth_map _ _ index index eq_refl), Nat.ltb_lt. reflexivity.
Qed.

Lemma gamma_output_support_mask_nth : forall d (gamma : ProductionTriple d) index,
    Vector.nth (GammaOutputSupportMask gamma) index = true <->
    (0 < Vector.nth (GammaOutput gamma) index)%nat.
Proof.
  intros. unfold GammaOutputSupportMask.
  rewrite (Vector.nth_map _ _ index index eq_refl), Nat.ltb_lt. reflexivity.
Qed.

Lemma support_mask_same_positive_support : forall d
    (gamma1 gamma2 : ProductionTriple d),
    GammaInputSupportMask gamma1 = GammaInputSupportMask gamma2 ->
    forall value,
      SamePositiveSupport value (GammaInput gamma1) <->
      SamePositiveSupport value (GammaInput gamma2).
Proof.
  intros d gamma1 gamma2 Hmask value. split; intros H index.
  - specialize (H index).
    pose proof (f_equal (fun mask => Vector.nth mask index) Hmask) as Hnth.
    unfold GammaInputSupportMask in Hnth.
    repeat rewrite (Vector.nth_map _ _ index index eq_refl) in Hnth.
    assert (Hpositive :
      (0 < Vector.nth (GammaInput gamma1) index)%nat <->
      (0 < Vector.nth (GammaInput gamma2) index)%nat).
    { repeat rewrite <- Nat.ltb_lt. now rewrite Hnth. }
    unfold nvec_to_qvec, q_of_nat, Qlt, inject_Z in *. cbn in *. lia.
  - specialize (H index).
    pose proof (f_equal (fun mask => Vector.nth mask index) Hmask) as Hnth.
    unfold GammaInputSupportMask in Hnth.
    repeat rewrite (Vector.nth_map _ _ index index eq_refl) in Hnth.
    assert (Hpositive :
      (0 < Vector.nth (GammaInput gamma1) index)%nat <->
      (0 < Vector.nth (GammaInput gamma2) index)%nat).
    { repeat rewrite <- Nat.ltb_lt. now rewrite Hnth. }
    unfold nvec_to_qvec, q_of_nat, Qlt, inject_Z in *. cbn in *. lia.
Qed.

Lemma output_support_mask_same_positive_support : forall d
    (gamma1 gamma2 : ProductionTriple d),
    GammaOutputSupportMask gamma1 = GammaOutputSupportMask gamma2 ->
    forall value,
      SamePositiveSupport value (GammaOutput gamma1) <->
      SamePositiveSupport value (GammaOutput gamma2).
Proof.
  intros d gamma1 gamma2 Hmask value. split; intros H index.
  - specialize (H index).
    pose proof (f_equal (fun mask => Vector.nth mask index) Hmask) as Hnth.
    unfold GammaOutputSupportMask in Hnth.
    repeat rewrite (Vector.nth_map _ _ index index eq_refl) in Hnth.
    assert (Hpositive :
      (0 < Vector.nth (GammaOutput gamma1) index)%nat <->
      (0 < Vector.nth (GammaOutput gamma2) index)%nat).
    { repeat rewrite <- Nat.ltb_lt. now rewrite Hnth. }
    unfold nvec_to_qvec, q_of_nat, Qlt, inject_Z in *. cbn in *. lia.
  - specialize (H index).
    pose proof (f_equal (fun mask => Vector.nth mask index) Hmask) as Hnth.
    unfold GammaOutputSupportMask in Hnth.
    repeat rewrite (Vector.nth_map _ _ index index eq_refl) in Hnth.
    assert (Hpositive :
      (0 < Vector.nth (GammaOutput gamma1) index)%nat <->
      (0 < Vector.nth (GammaOutput gamma2) index)%nat).
    { repeat rewrite <- Nat.ltb_lt. now rewrite Hnth. }
    unfold nvec_to_qvec, q_of_nat, Qlt, inject_Z in *. cbn in *. lia.
Qed.

Lemma exact_edges_same_signature_permutation : forall d system gamma1 gamma2
    witness1 witness2 signature edges1 edges2,
    @GraphSignatureRepresents d signature system gamma1 witness1 ->
    GraphSignatureRepresents signature system gamma2 witness2 ->
    ExactProductionGraphEdges system gamma1 witness1 edges1 ->
    ExactProductionGraphEdges system gamma2 witness2 edges2 ->
    Permutation edges1 edges2.
Proof.
  intros d system gamma1 gamma2 witness1 witness2 signature edges1 edges2
    [_ [_ [_ Hsig1]]] [_ [_ [_ Hsig2]]] [Hnodup1 Hexact1] [Hnodup2 Hexact2].
  apply NoDup_Permutation; try assumption.
  intros [source action target]. rewrite <- Hexact1, <- Hexact2, Hsig1, Hsig2.
  reflexivity.
Qed.

Lemma kirchhoff_relation_for_edges_same_support : forall d
    (gamma1 gamma2 : ProductionTriple d) edges input output,
    GammaInputSupportMask gamma1 = GammaInputSupportMask gamma2 ->
    GammaOutputSupportMask gamma1 = GammaOutputSupportMask gamma2 ->
    (@KirchhoffRelationForEdges d gamma1 edges input output <->
     KirchhoffRelationForEdges gamma2 edges input output).
Proof.
  intros d gamma1 gamma2 edges input output Hinput_mask Houtput_mask.
  unfold KirchhoffRelationForEdges. repeat apply and_iff_compat_l.
  rewrite (support_mask_same_positive_support d gamma1 gamma2 Hinput_mask input).
  rewrite (output_support_mask_same_positive_support d gamma1 gamma2 Houtput_mask output).
  reflexivity.
Qed.

Theorem production_kirchhoff_same_signature_support : forall d system
    (gamma1 gamma2 : ProductionTriple d) witness1 witness2 signature,
    ValidProductionTriple system gamma1 ->
    ValidProductionTriple system gamma2 ->
    Lemma57Witness system gamma1 witness1 ->
    Lemma57Witness system gamma2 witness2 ->
    GraphSignatureRepresents signature system gamma1 witness1 ->
    GraphSignatureRepresents signature system gamma2 witness2 ->
    GammaCapacity gamma1 = GammaCapacity gamma2 ->
    GammaInputSupportMask gamma1 = GammaInputSupportMask gamma2 ->
    GammaOutputSupportMask gamma1 = GammaOutputSupportMask gamma2 ->
    forall input output,
      (ProductionKirchhoffRelation system gamma1 input output <->
       ProductionKirchhoffRelation system gamma2 input output).
Proof.
  intros d system gamma1 gamma2 witness1 witness2 signature Hvalid1 Hvalid2
    Hw1 Hw2 Hsig1 Hsig2 _ Hinput_mask Houtput_mask input output.
  destruct (exact_production_graph_edges_exists d system gamma1 witness1
    Hvalid1 Hw1) as [edges1 Hedges1].
  destruct (exact_production_graph_edges_exists d system gamma2 witness2
    Hvalid2 Hw2) as [edges2 Hedges2].
  rewrite (production_kirchhoff_relation_fixed_edges d system gamma1
    witness1 edges1 input output Hw1 Hedges1).
  rewrite (production_kirchhoff_relation_fixed_edges d system gamma2
    witness2 edges2 input output Hw2 Hedges2).
  rewrite (kirchhoff_relation_edges_permutation d gamma1 edges1 edges2
    input output (exact_edges_same_signature_permutation d system gamma1
      gamma2 witness1 witness2 signature edges1 edges2 Hsig1 Hsig2
      Hedges1 Hedges2)).
  now apply kirchhoff_relation_for_edges_same_support.
Qed.

Definition ProductionKirchhoffKey (d : nat) :=
  (ProductionGraphSignature d * BoundedMask d * BoundedMask d)%type.

Definition production_kirchhoff_keys {d}
    (catalog : list (ProductionGraphSignature d)) :
    list (ProductionKirchhoffKey d) :=
  List.flat_map (fun signature =>
    List.flat_map (fun input_mask =>
      List.map (fun output_mask => (signature, input_mask, output_mask))
        (all_bounded_masks d))
      (all_bounded_masks d)) catalog.

Lemma production_kirchhoff_key_complete : forall d catalog signature
    input_mask output_mask,
    List.In signature catalog ->
    List.In (signature, input_mask, output_mask)
      (@production_kirchhoff_keys d catalog).
Proof.
  intros d catalog signature input_mask output_mask Hsignature.
  unfold production_kirchhoff_keys. apply in_flat_map. exists signature.
  split; [exact Hsignature|]. apply in_flat_map. exists input_mask.
  split; [apply all_bounded_masks_complete|]. apply in_map.
  apply all_bounded_masks_complete.
Qed.

Definition ProductionKirchhoffKeyRealized {d} (system : PlainVAS d)
    (capacity : NVec d) (key : ProductionKirchhoffKey d)
    (gamma : ProductionTriple d) : Prop :=
  ValidProductionTriple system gamma /\
  GammaCapacity gamma = capacity /\
  exists witness,
    Lemma57Witness system gamma witness /\
    GraphSignatureRepresents (fst (fst key)) system gamma witness /\
    GammaInputSupportMask gamma = snd (fst key) /\
    GammaOutputSupportMask gamma = snd key.

Lemma finite_key_realizer_selection : forall d system capacity
    (keys : list (ProductionKirchhoffKey d)),
    exists representatives : list (ProductionTriple d),
      (forall gamma0, List.In gamma0 representatives ->
        exists key, List.In key keys /\
          ProductionKirchhoffKeyRealized system capacity key gamma0) /\
      (forall key, List.In key keys ->
        (exists gamma, ProductionKirchhoffKeyRealized system capacity key gamma) ->
        exists gamma0, List.In gamma0 representatives /\
          ProductionKirchhoffKeyRealized system capacity key gamma0).
Proof.
  intros d system capacity keys. induction keys as [|key tail IH].
  - exists []. split; intros; cbn in *; contradiction.
  - destruct IH as [representatives [Hsound Hcomplete]].
    destruct (classic (exists gamma,
      ProductionKirchhoffKeyRealized system capacity key gamma))
      as [[gamma Hgamma]|Hnone].
    + exists (gamma :: representatives). split.
      * intros gamma0 [->|Hin].
        -- exists key. split; [now left|exact Hgamma].
        -- destruct (Hsound gamma0 Hin) as [other [Hother Hr]].
           exists other. split; [now right|exact Hr].
      * intros other [->|Hin] Hexists.
        -- exists gamma. split; [now left|exact Hgamma].
        -- destruct (Hcomplete other Hin Hexists) as [gamma0 [Hg Hr]].
           exists gamma0. split; [now right|exact Hr].
    + exists representatives. split.
      * intros gamma0 Hin. destruct (Hsound gamma0 Hin) as [other [Hother Hr]].
        exists other. split; [now right|exact Hr].
      * intros other [->|Hin] Hexists.
        -- contradiction.
        -- now apply Hcomplete.
Qed.

Theorem finite_production_kirchhoff_relation_representatives : forall d
    (system : PlainVAS d) (capacity : NVec d),
    exists representatives : list (ProductionTriple d),
      (forall gamma0,
        List.In gamma0 representatives ->
        ValidProductionTriple system gamma0 /\
        GammaCapacity gamma0 = capacity) /\
      (forall gamma,
        ValidProductionTriple system gamma ->
        GammaCapacity gamma = capacity ->
        exists gamma0,
          List.In gamma0 representatives /\
          forall input output,
            (ProductionKirchhoffRelation system gamma input output <->
             ProductionKirchhoffRelation system gamma0 input output)).
Proof.
  intros d system capacity.
  destruct (corollary_5_12_production_graph_class_finite d system capacity)
    as [catalog Hcatalog].
  destruct (finite_key_realizer_selection d system capacity
    (production_kirchhoff_keys catalog))
    as [representatives [Hsound Hcomplete]].
  exists representatives. split.
  - intros gamma0 Hin. destruct (Hsound gamma0 Hin) as [key [_ [Hv [Hc _]]]].
    now split.
  - intros gamma Hvalid Hcapacity.
    destruct (Hcatalog gamma Hvalid Hcapacity)
      as [witness [signature [Hw [Hsignature Hrep]]]].
    set (key := (signature, GammaInputSupportMask gamma,
      GammaOutputSupportMask gamma)).
    assert (Hkey : List.In key (production_kirchhoff_keys catalog)).
    { unfold key. now apply production_kirchhoff_key_complete. }
    assert (Hrealized : ProductionKirchhoffKeyRealized system capacity key gamma).
    { unfold ProductionKirchhoffKeyRealized, key. cbn.
      split; [exact Hvalid|]. split; [exact Hcapacity|]. exists witness.
      split; [exact Hw|]. split; [exact Hrep|]. split; reflexivity. }
    destruct (Hcomplete key Hkey (ex_intro _ gamma Hrealized))
      as [gamma0 [Hin Hgamma0]].
    exists gamma0. split; [exact Hin|].
    destruct Hgamma0 as [Hvalid0 [Hcapacity0 [witness0
      [Hw0 [Hrep0 [Hinput0 Houtput0]]]]]].
    intro input. intro output.
    eapply production_kirchhoff_same_signature_support
      with (witness1 := witness) (witness2 := witness0)
        (signature := signature); try eassumption.
    + now rewrite Hcapacity, Hcapacity0.
    + unfold key in Hinput0. cbn in Hinput0. symmetry. exact Hinput0.
    + unfold key in Houtput0. cbn in Houtput0. symmetry. exact Houtput0.
Qed.
