From Coq Require Import Classical_Pred_Type Classical_Prop Lia List QArith Qcanon.
From mathcomp Require Import all_ssreflect all_algebra.
From Mell.Geometry Require Import FaceOrder Faces FiniteFaces
  LatticeGordanInterface LatticeGordanV MathCompBridge QConeCore
  QcLinearAlgebra RationalDefinability RationalHToV.

Import ListNotations QcMathComp.
Import GRing.Theory.

Lemma list_in_mathcomp_mem : forall (A : eqType) (value : A) source,
    List.In value source -> value \in source.
Proof.
  intros A value source Hin. induction source as [|head tail IH];
    cbn in Hin; [contradiction|].
  destruct Hin as [->|Hin].
  - exact (mem_head value tail).
  - rewrite in_cons. apply/orP. right. now apply IH.
Qed.

Lemma mathcomp_mem_list_in : forall (A : eqType) (value : A) source,
    value \in source -> List.In value source.
Proof.
  intros A value source. induction source as [|head tail IH].
  - now rewrite in_nil.
  - rewrite in_cons. move/orP=> [/eqP ->|Hin];
      [now left|right; now apply IH].
Qed.

Definition qrow_generators {d} (generators : list (QVec d)) :
    list ('rV[Qc]_d) :=
  List.map qvec_to_qcrow generators.

Definition QSpanOf {d} (set : QSet d) (value : QVec d) : Prop :=
  exists generators : list (QVec d),
    List.Forall set generators /\
    qvec_to_qcrow value \in <<qrow_generators generators>>%VS.

Definition SpanPresentation {d} (set : QSet d)
    (generators : list (QVec d)) : Prop :=
  List.Forall set generators /\
  forall value,
    QSpanOf set value <->
    qvec_to_qcrow value \in <<qrow_generators generators>>%VS.

Definition SpanDimension {d} (set : QSet d) (dimension : nat) : Prop :=
  exists generators : list (QVec d),
    SpanPresentation set generators /\
    dimension = \dim <<qrow_generators generators>>%VS.

Definition QConeDifference {d} (cone : QSet d) (value : QVec d) : Prop :=
  exists positive negative,
    cone positive /\ cone negative /\
    QVecEq value (qvec_add positive (qvec_scale (-1) negative)).

Lemma row_span_aligned_coefficients : forall d
    (generators : list (QVec d)) (row : 'rV[Qc]_d),
    row \in <<qrow_generators generators>>%VS ->
    exists coefficients : list Q,
      length coefficients = length generators /\
      row = qvec_to_qcrow (qlinear_combination generators coefficients).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros row Hrow.
  - rewrite /qrow_generators /= span_nil memv0 in Hrow.
    move/eqP: Hrow=> ->. exists []. split; [reflexivity|].
    apply/matrixP. intros i j. rewrite !mxE. reflexivity.
  - rewrite /qrow_generators /= span_cons in Hrow.
    move/memv_addP: Hrow=> [head_part Hhead [tail_part Htail ->]].
    move/vlineP: Hhead=> [coefficient ->].
    destruct (IH tail_part Htail) as [coefficients [Hlength Htail_eq]].
    exists ((coefficient : Q) :: coefficients). split.
    + cbn. now rewrite Hlength.
    + cbn [qlinear_combination]; rewrite qvec_to_qcrow_add
        qvec_to_qcrow_scale Htail_eq q2qc_this. reflexivity.
Qed.

Lemma aligned_coefficients_in_row_span : forall d
    (generators : list (QVec d)) coefficients,
    length coefficients = length generators ->
    qvec_to_qcrow (qlinear_combination generators coefficients)
      \in <<qrow_generators generators>>%VS.
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength.
  - destruct coefficients; [|discriminate]. cbn [qlinear_combination].
    rewrite qvec_to_qcrow_zero. apply mem0v.
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    cbn [qlinear_combination qrow_generators]; rewrite span_cons
      qvec_to_qcrow_add qvec_to_qcrow_scale.
    apply memv_add.
    + apply/vlineP. eexists. reflexivity.
    + apply IH. exact Hlength.
Qed.

Lemma qspan_of_aligned_coefficients : forall d (set : QSet d) value,
    QSpanOf set value <->
    exists generators : list (QVec d),
      List.Forall set generators /\
      exists coefficients : list Q,
        length coefficients = length generators /\
        QVecEq value (qlinear_combination generators coefficients).
Proof.
  intros d set value. split.
  - intros [generators [Hall Hspan]].
    destruct (row_span_aligned_coefficients d generators _ Hspan)
      as [coefficients [Hlength Hrow]].
    exists generators. split; [exact Hall|]. exists coefficients.
    split; [exact Hlength|].
    apply qvec_to_qcrow_eq_reflect. exact Hrow.
  - intros [generators [Hall [coefficients [Hlength Heq]]]].
    exists generators. split; [exact Hall|].
    rewrite (qvec_to_qcrow_eq d value
      (qlinear_combination generators coefficients) Heq).
    now apply aligned_coefficients_in_row_span.
Qed.

Lemma qspan_of_add : forall d (set : QSet d) left right,
    QSpanOf set left -> QSpanOf set right ->
    QSpanOf set (qvec_add left right).
Proof.
  intros d set left right
    [left_generators [Hleft_points Hleft]]
    [right_generators [Hright_points Hright]].
  exists (left_generators ++ right_generators). split.
  - now apply List.Forall_app.
  - unfold qrow_generators. rewrite List.map_app span_cat
      qvec_to_qcrow_add. now apply memv_add.
Qed.

Lemma qspan_of_scale : forall d (set : QSet d) coefficient value,
    QSpanOf set value -> QSpanOf set (qvec_scale coefficient value).
Proof.
  intros d set coefficient value [generators [Hpoints Hvalue]].
  exists generators. split; [exact Hpoints|].
  rewrite qvec_to_qcrow_scale. now apply memvZ.
Qed.

Definition qcoefficient_positive (coefficient : Q) : Q :=
  if Qlt_le_dec coefficient 0 then 0 else coefficient.

Definition qcoefficient_negative (coefficient : Q) : Q :=
  if Qlt_le_dec coefficient 0 then - coefficient else 0.

Lemma qcoefficient_positive_nonnegative : forall coefficient,
    0 <= qcoefficient_positive coefficient.
Proof.
  intro coefficient. unfold qcoefficient_positive.
  destruct (Qlt_le_dec coefficient 0).
  - unfold Qle; cbn; lia.
  - exact q.
Qed.

Lemma qcoefficient_negative_nonnegative : forall coefficient,
    0 <= qcoefficient_negative coefficient.
Proof.
  intro coefficient. unfold qcoefficient_negative.
  destruct (Qlt_le_dec coefficient 0).
  - change (- (0 : Q) <= - coefficient).
    apply Qopp_le_compat. now apply Qlt_le_weak.
  - unfold Qle; cbn; lia.
Qed.

Lemma qcoefficient_positive_list_nonnegative : forall coefficients,
    List.Forall (fun coefficient => 0 <= coefficient)
      (List.map qcoefficient_positive coefficients).
Proof.
  intro coefficients. induction coefficients as [|coefficient tail IH].
  - constructor.
  - cbn. constructor; [apply qcoefficient_positive_nonnegative|exact IH].
Qed.

Lemma qcoefficient_negative_list_nonnegative : forall coefficients,
    List.Forall (fun coefficient => 0 <= coefficient)
      (List.map qcoefficient_negative coefficients).
Proof.
  intro coefficients. induction coefficients as [|coefficient tail IH].
  - constructor.
  - cbn. constructor; [apply qcoefficient_negative_nonnegative|exact IH].
Qed.

Lemma qcoefficient_positive_negative : forall coefficient,
    coefficient == qcoefficient_positive coefficient -
      qcoefficient_negative coefficient.
Proof.
  intro coefficient.
  destruct (Qlt_le_dec coefficient 0) as [Hlt|Hge] eqn:Hdecision.
  - unfold qcoefficient_positive, qcoefficient_negative. rewrite Hdecision.
    unfold Qminus. rewrite Qopp_opp Qplus_0_l. reflexivity.
  - unfold qcoefficient_positive, qcoefficient_negative. rewrite Hdecision.
    unfold Qminus. change (Qeq coefficient (Qplus coefficient 0)).
    symmetry. apply Qplus_0_r.
Qed.

Lemma qlinear_combination_positive_negative : forall d
    (generators : list (QVec d)) coefficients,
    length coefficients = length generators ->
    QVecEq (qlinear_combination generators coefficients)
      (qvec_add
        (qlinear_combination generators
          (List.map qcoefficient_positive coefficients))
        (qvec_scale (-1)
          (qlinear_combination generators
            (List.map qcoefficient_negative coefficients)))).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength.
  - destruct coefficients; [|discriminate]. cbn [qlinear_combination].
    intro index. unfold qvec_add, qvec_scale, qvec_zero. ring.
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    cbn [qlinear_combination List.map]. intro index.
    unfold qvec_add, qvec_scale.
    specialize (IH coefficients Hlength index).
    unfold qvec_add, qvec_scale in IH.
    remember (qcoefficient_positive coefficient) as positive eqn:Hpositive.
    remember (qcoefficient_negative coefficient) as negative eqn:Hnegative.
    assert (Hcoefficient : coefficient == positive - negative).
    { subst positive negative. apply qcoefficient_positive_negative. }
    setoid_rewrite IH.
    setoid_rewrite Hcoefficient.
    ring.
Qed.

Lemma qspan_of_member : forall d (set : QSet d) value,
    set value -> QSpanOf set value.
Proof.
  intros d set value Hvalue. exists [value]. split.
  - now constructor.
  - apply memv_span. cbn. apply/orP. left. apply/eqP. reflexivity.
Qed.

Lemma qspan_of_qvec_ext : forall d (set : QSet d) left right,
    QVecEq left right ->
    (QSpanOf set left <-> QSpanOf set right).
Proof.
  intros d set left right Heq. split.
  - intros [generators [Hall Hspan]]. exists generators. split;
      [exact Hall|].
    rewrite <- (qvec_to_qcrow_eq d left right Heq). exact Hspan.
  - intros [generators [Hall Hspan]]. exists generators. split;
      [exact Hall|].
    rewrite (qvec_to_qcrow_eq d left right Heq). exact Hspan.
Qed.

Lemma qspan_of_monotone : forall d (left right : QSet d),
    FaceSubset left right ->
    forall value, QSpanOf left value -> QSpanOf right value.
Proof.
  intros d left right Hsubset value [generators [Hall Hspan]].
  exists generators. split; [|exact Hspan].
  apply (proj2 (List.Forall_forall _ _)). intros generator Hin.
  apply Hsubset, (proj1 (List.Forall_forall _ _) Hall generator Hin).
Qed.

Lemma qspan_of_set_ext : forall d (left right : QSet d),
    SameSet left right ->
    forall value, QSpanOf left value <-> QSpanOf right value.
Proof.
  intros d left right Heq value. split.
  - intros [generators [Hall Hspan]]. exists generators. split.
    + apply (proj2 (List.Forall_forall _ _)). intros generator Hin.
      apply (proj1 (Heq generator)).
      exact (proj1 (List.Forall_forall _ _) Hall generator Hin).
    + exact Hspan.
  - intros [generators [Hall Hspan]]. exists generators. split.
    + apply (proj2 (List.Forall_forall _ _)). intros generator Hin.
      apply (proj2 (Heq generator)).
      exact (proj1 (List.Forall_forall _ _) Hall generator Hin).
    + exact Hspan.
Qed.

Lemma qlinear_combination_in_cone : forall d (cone : QSet d),
    IsCone cone -> forall generators coefficients,
    List.Forall cone generators ->
    length coefficients = length generators ->
    List.Forall (fun coefficient => 0 <= coefficient) coefficients ->
    cone (qlinear_combination generators coefficients).
Proof.
  intros d cone Hcone generators. induction generators as
    [|generator generators IH]; intros coefficients Hpoints Hlength Hcoefficients.
  - destruct coefficients; [|discriminate]. cbn [qlinear_combination].
    apply (cone_contains_zero cone Hcone).
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    inversion Hpoints as [|? ? Hgenerator Htail]; subst.
    inversion Hcoefficients as [|? ? Hcoefficient Hcoefficients']; subst.
    cbn in Hlength. injection Hlength as Hlength.
    cbn [qlinear_combination]. apply (cone_closed_add cone Hcone).
    + apply (cone_closed_scale cone Hcone); assumption.
    + apply IH; assumption.
Qed.

Theorem qspan_of_cone_difference : forall d (cone : QSet d),
    IsCone cone ->
    forall value, QSpanOf cone value <-> QConeDifference cone value.
Proof.
  intros d cone Hcone value. split.
  - intro Hspan.
    apply qspan_of_aligned_coefficients in Hspan as
      [generators [Hpoints [coefficients [Hlength Hvalue]]]].
    set (positive_coefficients :=
      List.map qcoefficient_positive coefficients).
    set (negative_coefficients :=
      List.map qcoefficient_negative coefficients).
    set (positive := qlinear_combination generators positive_coefficients).
    set (negative := qlinear_combination generators negative_coefficients).
    exists positive, negative. repeat split.
    + apply (qlinear_combination_in_cone d cone Hcone generators
        positive_coefficients Hpoints).
      * unfold positive_coefficients. now rewrite List.map_length.
      * unfold positive_coefficients.
        apply qcoefficient_positive_list_nonnegative.
    + apply (qlinear_combination_in_cone d cone Hcone generators
        negative_coefficients Hpoints).
      * unfold negative_coefficients. now rewrite List.map_length.
      * unfold negative_coefficients.
        apply qcoefficient_negative_list_nonnegative.
    + eapply qvec_eq_trans; [exact Hvalue|].
      apply qlinear_combination_positive_negative. exact Hlength.
  - intros [positive [negative [Hpositive [Hnegative Heq]]]].
    apply (proj2 (qspan_of_qvec_ext d cone value
      (qvec_add positive (qvec_scale (-1) negative)) Heq)).
    apply qspan_of_add.
    + now apply qspan_of_member.
    + apply qspan_of_scale. now apply qspan_of_member.
Qed.

Lemma qcone_combination_in_row_span : forall d
    (generators : list (QVec d)) value,
    QConeCombination generators value ->
    qvec_to_qcrow value \in <<qrow_generators generators>>%VS.
Proof.
  intros d generators value Hvalue. induction Hvalue.
  - rewrite qvec_to_qcrow_zero. apply mem0v.
  - rewrite qvec_to_qcrow_add qvec_to_qcrow_scale.
    apply memvD.
    + apply memvZ, memv_span, list_in_mathcomp_mem.
      apply List.in_map. exact H0.
    + exact IHHvalue.
Qed.

Lemma qcone_generated_in_row_span : forall d
    (generators : list (QVec d)) value,
    qcone_generated generators value ->
    qvec_to_qcrow value \in <<qrow_generators generators>>%VS.
Proof.
  intros d generators value [generated [Hgenerated Heq]].
  rewrite (qvec_to_qcrow_eq d value generated Heq).
  now apply qcone_combination_in_row_span.
Qed.

Lemma row_generators_in_qcone : forall d (generators : list (QVec d))
    row,
    row \in qrow_generators generators ->
    exists generator,
      qcone_generated generators generator /\
      row = qvec_to_qcrow generator.
Proof.
  intros d generators row Hrow.
  apply mathcomp_mem_list_in in Hrow.
  unfold qrow_generators in Hrow.
  apply List.in_map_iff in Hrow as [generator [Heq Hin]]. subst row.
  exists generator. split; [now apply qcone_generated_generator|reflexivity].
Qed.

Theorem qcone_span_presentation : forall d
    (generators : list (QVec d)),
    SpanPresentation (qcone_generated generators) generators.
Proof.
  intros d generators. split.
  - apply (proj2 (List.Forall_forall _ _)). intros generator Hin.
    now apply qcone_generated_generator.
  - intro value. split.
    + intros [points [Hpoints Hspan]].
      assert (Hsubspace : (<<qrow_generators points>> <=
          <<qrow_generators generators>>)%VS).
      { apply/span_subvP.
        intros row Hrow. apply mathcomp_mem_list_in in Hrow.
        unfold qrow_generators in Hrow.
        apply List.in_map_iff in Hrow as [point [Heq Hin]]. subst row.
        apply qcone_generated_in_row_span.
        exact (proj1 (List.Forall_forall _ _) Hpoints point Hin). }
      move/subvP: Hsubspace=> Hsubspace. exact (Hsubspace _ Hspan).
    + intro Hspan. exists generators. split.
      * apply (proj2 (List.Forall_forall _ _)). intros generator Hin.
        now apply qcone_generated_generator.
      * exact Hspan.
Qed.

Theorem polyhedral_span_dimension_exists : forall d (cone : QSet d),
    RationalPolyhedralCone cone ->
    exists dimension, SpanDimension cone dimension.
Proof.
  intros d cone [generators Hcone].
  exists (\dim <<qrow_generators generators>>%VS), generators. split.
  - split.
    + apply (proj2 (List.Forall_forall _ _)). intros generator Hin.
      apply (proj2 (Hcone generator)), qcone_generated_generator. exact Hin.
    + intro value.
      rewrite (qspan_of_set_ext d cone (qcone_generated generators)
        Hcone value).
      apply qcone_span_presentation.
  - reflexivity.
Qed.

Lemma span_presentation_subspace_inclusion : forall d
    (left right : QSet d) left_generators right_generators,
    SpanPresentation left left_generators ->
    SpanPresentation right right_generators ->
    FaceSubset left right ->
    (<<qrow_generators left_generators>> <=
      <<qrow_generators right_generators>>)%VS.
Proof.
  intros d left right left_generators right_generators
    [Hleft_points Hleft] [Hright_points Hright] Hsubset.
  apply/span_subvP. intros row Hrow.
  apply mathcomp_mem_list_in in Hrow.
  unfold qrow_generators in Hrow.
  apply List.in_map_iff in Hrow as [point [Heq Hin]]. subst row.
  apply (proj1 (Hright point)), qspan_of_member, Hsubset.
  exact (proj1 (List.Forall_forall _ _) Hleft_points point Hin).
Qed.

Definition qcrow_support_map {d} (normal : 'rV[Qc]_d) :=
  linfun (@mulmxr QcMathComp.qc_field_type 1 d 1 (normal^T)).

Lemma qcrow_support_map_entry : forall d
    (normal value : 'rV[Qc]_d),
    qcrow_support_map normal value ord0 ord0 = qcrow_inner normal value.
Proof.
  intros d normal value. rewrite /qcrow_support_map lfunE /mulmxr mxE.
  apply eq_bigr. intros index _. rewrite mxE mulrC. reflexivity.
Qed.

Lemma qcrow_inner_zero_mem_kernel : forall d
    (normal value : 'rV[Qc]_d),
    qcrow_inner normal value = (0%R : Qc) ->
    value \in lker (qcrow_support_map normal).
Proof.
  intros d normal value Hzero. rewrite memv_ker. apply/eqP.
  apply/matrixP. intros i j.
  rewrite (ord1 i) (ord1 j) qcrow_support_map_entry Hzero !mxE.
  reflexivity.
Qed.

Lemma qcrow_inner_nonzero_not_mem_kernel : forall d
    (normal value : 'rV[Qc]_d),
    qcrow_inner normal value != (0%R : Qc) ->
    value \notin lker (qcrow_support_map normal).
Proof.
  intros d normal value Hnonzero. rewrite memv_ker. apply/negP.
  intro Hzero. move/eqP: Hzero=> Hzero.
  have Hentry := congr1 (fun matrix : 'M[Qc]_(1,1) =>
    matrix ord0 ord0) Hzero.
  rewrite qcrow_support_map_entry !mxE in Hentry.
  apply (negP Hnonzero). apply/eqP. exact Hentry.
Qed.

Lemma span_of_orthogonal_generators : forall d (normal : QVec d)
    (generators : list (QVec d)),
    (forall point, List.In point generators ->
      qinner normal point == 0) ->
    (<<qrow_generators generators>> <=
      lker (qcrow_support_map (qvec_to_qcrow normal)))%VS.
Proof.
  intros d normal generators Hall. apply/span_subvP.
  intros row Hrow. apply mathcomp_mem_list_in in Hrow.
  unfold qrow_generators in Hrow.
  apply List.in_map_iff in Hrow as [point [Heq Hin]]. subst row.
  apply qcrow_inner_zero_mem_kernel, qcrow_inner_qvec_zero, Hall, Hin.
Qed.

Theorem proper_face_span_strict : forall d (cone face larger : QSet d)
    face_generators larger_generators,
    FaceOf cone face -> FaceOf cone larger ->
    ProperFaceSubset face larger ->
    SpanPresentation face face_generators ->
    SpanPresentation larger larger_generators ->
    (<<qrow_generators face_generators>> <=
      <<qrow_generators larger_generators>>)%VS /\
    ~ (<<qrow_generators larger_generators>> <=
      <<qrow_generators face_generators>>)%VS.
Proof.
  intros d cone face larger face_generators larger_generators
    Hface Hlarger [Hsubset Hproper] Hface_span Hlarger_span.
  assert (Hinclusion : (<<qrow_generators face_generators>> <=
      <<qrow_generators larger_generators>>)%VS).
  { now apply span_presentation_subspace_inclusion with
      (left := face) (right := larger). }
  split; [exact Hinclusion|].
  destruct (classic (forall point, larger point -> face point)) as
    [Hreverse|Hnot_reverse].
  - exfalso. apply Hproper, face_subset_antisym_same_set; assumption.
  - apply not_all_ex_not in Hnot_reverse as [point Hpoint].
    apply imply_to_and in Hpoint as [Hlarger_point Hnot_face].
    destruct Hface as [normals [Hsupport Hface_spec]].
    assert (Hcone_point : cone point).
    { apply (face_subset d cone larger Hlarger), Hlarger_point. }
    assert (Hnot_orthogonal : ~ NormalOrthogonal normals point).
    { intro Horthogonal. apply Hnot_face, (proj2 (Hface_spec point)).
      now split. }
    unfold NormalOrthogonal in Hnot_orthogonal.
    apply not_all_ex_not in Hnot_orthogonal as [normal Hnormal].
    apply imply_to_and in Hnormal as [Hnormal_in Hnormal_nonzero].
    assert (Hface_in_kernel :
        (<<qrow_generators face_generators>> <=
          lker (qcrow_support_map (qvec_to_qcrow normal)))%VS).
    { apply span_of_orthogonal_generators.
      intros face_point Hface_point.
      destruct Hface_span as [Hface_generators _].
      pose proof (proj1 (Hface_spec face_point)
        (proj1 (List.Forall_forall _ _) Hface_generators
          face_point Hface_point)) as Hface_data.
      exact (proj2 Hface_data normal Hnormal_in). }
    assert (Hpoint_in_larger : qvec_to_qcrow point \in
        <<qrow_generators larger_generators>>%VS).
    { apply (proj1 (proj2 Hlarger_span point)), qspan_of_member.
      exact Hlarger_point. }
    assert (Hpoint_not_kernel : qvec_to_qcrow point \notin
        lker (qcrow_support_map (qvec_to_qcrow normal))).
    { apply qcrow_inner_nonzero_not_mem_kernel,
        qcrow_inner_qvec_nonzero. exact Hnormal_nonzero. }
    intro Hreverse_span. apply (negP Hpoint_not_kernel).
    move/subvP: Hface_in_kernel=> Hface_in_kernel.
    apply Hface_in_kernel.
    move/subvP: Hreverse_span=> Hreverse_span.
    exact (Hreverse_span _ Hpoint_in_larger).
Qed.

Theorem span_dimension_unique : forall d (set : QSet d) left right,
    SpanDimension set left -> SpanDimension set right -> left = right.
Proof.
  intros d set left right
    [left_generators [Hleft ->]] [right_generators [Hright ->]].
  apply/eqP. rewrite eqn_leq. apply/andP. split; apply dimvS.
  - apply span_presentation_subspace_inclusion with
      (left := set) (right := set); try assumption. apply face_subset_refl.
  - apply span_presentation_subspace_inclusion with
      (left := set) (right := set); try assumption. apply face_subset_refl.
Qed.

Theorem span_dimension_le_presentation : forall d (set : QSet d)
    generators dimension,
    SpanPresentation set generators ->
    SpanDimension set dimension ->
    (dimension <= length generators)%coq_nat.
Proof.
  intros d set generators dimension Hpresentation
    [actual [Hactual ->]].
  apply Nat.le_trans with
    (m := \dim <<qrow_generators generators>>%VS).
  - apply/leP/dimvS.
    apply span_presentation_subspace_inclusion with
      (left := set) (right := set); try assumption.
    apply face_subset_refl.
  - have Hspan := leP (dim_span (qrow_generators generators)).
    rewrite /qrow_generators size_map in Hspan.
    exact Hspan.
Qed.

Theorem span_dimension_monotone : forall d (left right : QSet d)
    left_dimension right_dimension,
    FaceSubset left right ->
    SpanDimension left left_dimension ->
    SpanDimension right right_dimension ->
    (left_dimension <= right_dimension)%coq_nat.
Proof.
  intros d left right left_dimension right_dimension Hsubset
    [left_generators [Hleft ->]] [right_generators [Hright ->]].
  apply/leP/dimvS.
  now apply span_presentation_subspace_inclusion with
    (left := left) (right := right).
Qed.

Theorem span_dimension_same_set : forall d (left right : QSet d)
    left_dimension right_dimension,
    SameSet left right ->
    SpanDimension left left_dimension ->
    SpanDimension right right_dimension ->
    left_dimension = right_dimension.
Proof.
  intros d left right left_dimension right_dimension Heq Hleft Hright.
  apply Nat.le_antisymm.
  - apply (span_dimension_monotone d left right); try assumption.
    intros point Hpoint. apply (proj1 (Heq point)), Hpoint.
  - apply (span_dimension_monotone d right left); try assumption.
    intros point Hpoint. apply (proj2 (Heq point)), Hpoint.
Qed.

Theorem proper_face_dimension_lt : forall d
    (cone face larger : QSet d) face_dimension larger_dimension,
    RationalPolyhedralCone cone ->
    FaceOf cone face -> FaceOf cone larger ->
    ProperFaceSubset face larger ->
    SpanDimension face face_dimension ->
    SpanDimension larger larger_dimension ->
    (face_dimension < larger_dimension)%coq_nat.
Proof.
  intros d cone face larger face_dimension larger_dimension _
    Hface Hlarger Hproper
    [face_generators [Hface_span ->]]
    [larger_generators [Hlarger_span ->]].
  destruct (proper_face_span_strict d cone face larger
    face_generators larger_generators Hface Hlarger Hproper
    Hface_span Hlarger_span) as [Hsub Hnot_reverse].
  assert (Hle : (\dim <<qrow_generators face_generators>>%VS <=
      \dim <<qrow_generators larger_generators>>%VS)%coq_nat).
  { exact (leP (dimvS Hsub)). }
  assert (Hneq : \dim <<qrow_generators face_generators>>%VS <>
      \dim <<qrow_generators larger_generators>>%VS).
  { intro Heq.
    apply Hnot_reverse.
    rewrite -(dimv_leqif_sup Hsub) Heq. apply eqxx. }
  lia.
Qed.

Theorem proper_face_of_cone_dimension_lt : forall d
    (cone face : QSet d) face_dimension cone_dimension,
    RationalPolyhedralCone cone ->
    FaceOf cone face -> ~ SameSet face cone ->
    SpanDimension face face_dimension ->
    SpanDimension cone cone_dimension ->
    (face_dimension < cone_dimension)%coq_nat.
Proof.
  intros d cone face face_dimension cone_dimension Hpoly Hface Hproper
    Hface_dimension Hcone_dimension.
  apply (proper_face_dimension_lt d cone face cone
    face_dimension cone_dimension).
  - exact Hpoly.
  - exact Hface.
  - apply face_self.
  - split.
    + unfold FaceSubset. now apply (face_subset d cone face Hface).
    + exact Hproper.
  - exact Hface_dimension.
  - exact Hcone_dimension.
Qed.

Theorem linearized_proper_faces_index_and_dimension : forall d
    (cone : QSet d) faces,
    (forall i j face_i face_j,
      nth_error faces i = Some face_i ->
      nth_error faces j = Some face_j ->
      FaceSubset face_j face_i -> (i <= j)%coq_nat) ->
    (forall i j face_i face_j,
      nth_error faces i = Some face_i ->
      nth_error faces j = Some face_j ->
      i <> j -> ~ SameSet face_i face_j) ->
    (forall face, List.In face faces -> FaceOf cone face) ->
    RationalPolyhedralCone cone ->
    forall i j face_i face_j dim_i dim_j,
      nth_error faces i = Some face_i ->
      nth_error faces j = Some face_j ->
      ProperFaceSubset face_j face_i ->
      SpanDimension face_i dim_i ->
      SpanDimension face_j dim_j ->
      (i < j)%coq_nat /\ (dim_j < dim_i)%coq_nat.
Proof.
  intros d cone faces Horder Hnodup Hfaces Hpoly
    i j face_i face_j dim_i dim_j Hi Hj [Hsubset Hproper] Hdim_i Hdim_j.
  assert (Hneq : i <> j).
  { intro Heq. subst j. rewrite Hi in Hj. injection Hj as ->.
    apply Hproper, same_set_refl. }
  split.
  - specialize (Horder i j face_i face_j Hi Hj Hsubset). lia.
  - apply (proper_face_dimension_lt d cone face_j face_i dim_j dim_i).
    + exact Hpoly.
    + apply Hfaces, nth_error_In with (n := j). exact Hj.
    + apply Hfaces, nth_error_In with (n := i). exact Hi.
    + now split.
    + exact Hdim_j.
    + exact Hdim_i.
Qed.
