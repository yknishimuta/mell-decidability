From Coq Require Import Fin Lia List Lra QArith Qring Vector VectorSpec.
From Mell.Geometry Require Import LatticeGordanInterface LatticeGordanV
  MathCompBridge QConeCore RationalDefinability RationalHToV.

Import ListNotations.
Open Scope Q_scope.

Definition qinner {d} (left right : QVec d) : Q :=
  qrow_apply (qvec_to_vector d left) right.

Definition SupportingNormal {d} (cone : QSet d) (normal : QVec d) : Prop :=
  forall point, cone point -> 0 <= qinner normal point.

Definition NormalOrthogonal {d} (normals : list (QVec d))
    (point : QVec d) : Prop :=
  forall normal, List.In normal normals -> qinner normal point == 0.

Definition FaceOf {d} (cone face : QSet d) : Prop :=
  exists normals : list (QVec d),
    List.Forall (SupportingNormal cone) normals /\
    SameSet face
      (fun point => cone point /\ NormalOrthogonal normals point).

Definition generator_on_normals {d} (normals : list (QVec d))
    (generator : QVec d) : bool :=
  forallb
    (fun normal => Qeq_bool (qinner normal generator) 0)
    normals.

Definition face_generators {d} (normals generators : list (QVec d)) :=
  List.filter (generator_on_normals normals) generators.

Lemma qinner_qvec_ext_right : forall d (normal left right : QVec d),
    QVecEq left right -> qinner normal left == qinner normal right.
Proof.
  intros d normal left right Heq. unfold qinner.
  now apply qrow_apply_qvec_ext.
Qed.

Lemma qinner_zero_right : forall d (normal : QVec d),
    qinner normal (qvec_zero d) == 0.
Proof. intros; unfold qinner; apply qrow_apply_zero. Qed.

Lemma qinner_add_right : forall d (normal left right : QVec d),
    qinner normal (qvec_add left right) ==
      qinner normal left + qinner normal right.
Proof. intros; unfold qinner; apply qrow_apply_add. Qed.

Lemma qinner_scale_right : forall d (normal : QVec d) coefficient point,
    qinner normal (qvec_scale coefficient point) ==
      coefficient * qinner normal point.
Proof. intros; unfold qinner; apply qrow_apply_scale. Qed.

Lemma normal_orthogonal_qvec_ext : forall d normals
    (left right : QVec d),
    QVecEq left right ->
    (NormalOrthogonal normals left <-> NormalOrthogonal normals right).
Proof.
  intros d normals left right Heq. split; intros H normal Hin.
  - transitivity (qinner normal left).
    + symmetry. now apply qinner_qvec_ext_right.
    + apply H; assumption.
  - transitivity (qinner normal right).
    + now apply qinner_qvec_ext_right.
    + apply H; assumption.
Qed.

Lemma generator_on_normals_spec : forall d normals (generator : QVec d),
    generator_on_normals normals generator = true <->
    NormalOrthogonal normals generator.
Proof.
  intros d normals generator. unfold generator_on_normals,
    NormalOrthogonal. rewrite forallb_forall. split; intros H normal Hin.
  - apply Qeq_bool_iff, H; assumption.
  - apply Qeq_bool_iff, H; assumption.
Qed.

Lemma qnonnegative_sum_zero_left : forall left right : Q,
    0 <= left -> 0 <= right -> left + right == 0 -> left == 0.
Proof.
  intros left right Hleft Hright Hsum.
  assert (Hleft_le_sum : left <= left + right).
  { apply (proj2 (Qplus_le_r 0 right left)) in Hright.
    setoid_replace (left + 0) with left in Hright by ring.
    exact Hright. }
  setoid_rewrite Hsum in Hleft_le_sum.
  now apply Qle_antisym.
Qed.

Lemma qnonnegative_sum_zero_right : forall left right : Q,
    0 <= left -> 0 <= right -> left + right == 0 -> right == 0.
Proof.
  intros left right Hleft Hright Hsum.
  apply qnonnegative_sum_zero_left with (right := left); try assumption.
  transitivity (left + right); [ring|exact Hsum].
Qed.

Lemma qcone_combination_weaken : forall d
    (source target : list (QVec d)) point,
    (forall generator, List.In generator source ->
      List.In generator target) ->
    QConeCombination source point -> QConeCombination target point.
Proof.
  intros d source target point Hsubset Hpoint. induction Hpoint.
  - constructor.
  - constructor; [assumption|now apply Hsubset|assumption].
Qed.

Lemma qcone_combination_face_orthogonal : forall d
    (generators normals : list (QVec d)) point,
    QConeCombination (face_generators normals generators) point ->
    NormalOrthogonal normals point.
Proof.
  intros d generators normals point Hpoint. induction Hpoint;
    intros normal Hnormal.
  - apply qinner_zero_right.
  - apply filter_In in H0 as [_ Hgenerator].
    apply generator_on_normals_spec in Hgenerator.
    transitivity
      (coefficient * qinner normal generator + qinner normal tail).
    + transitivity
        (qinner normal (qvec_scale coefficient generator) +
          qinner normal tail).
      * apply qinner_add_right.
      * apply Qplus_comp; [apply qinner_scale_right|reflexivity].
    + setoid_rewrite (Hgenerator normal Hnormal).
      setoid_rewrite (IHHpoint normal Hnormal). ring.
Qed.

Lemma qcone_combination_as_generated : forall d
    (generators : list (QVec d)) point,
    QConeCombination generators point -> qcone_generated generators point.
Proof.
  intros d generators point Hpoint. exists point. split;
    [exact Hpoint|apply qvec_eq_refl].
Qed.

Lemma supporting_normal_of_generators : forall d
    (generators : list (QVec d)) normal,
    (forall generator, List.In generator generators ->
      0 <= qinner normal generator) ->
    SupportingNormal (qcone_generated generators) normal.
Proof.
  intros d generators normal Hgenerators point
    [generated [Hgenerated Hpoint]].
  assert (Hnonnegative : 0 <= qinner normal generated).
  { clear Hpoint point. induction Hgenerated.
    - setoid_rewrite qinner_zero_right. apply Qle_refl.
    - setoid_rewrite qinner_add_right.
      setoid_rewrite qinner_scale_right.
      setoid_replace 0 with (0 + 0) by ring.
      apply Qplus_le_compat; [|exact IHHgenerated].
      apply Qmult_le_0_compat; [exact H|now apply Hgenerators]. }
  setoid_rewrite (qinner_qvec_ext_right d normal point generated Hpoint).
  exact Hnonnegative.
Qed.

Lemma qcone_combination_filter : forall d
    (generators normals : list (QVec d)),
    List.Forall (SupportingNormal (qcone_generated generators)) normals ->
    forall point,
      QConeCombination generators point ->
      NormalOrthogonal normals point ->
      qcone_generated (face_generators normals generators) point.
Proof.
  intros d generators normals Hsupport point Hpoint.
  induction Hpoint; intro Horthogonal.
  - apply qcone_generated_zero.
  - assert (Htail_orthogonal : NormalOrthogonal normals tail).
    { intros normal Hnormal.
      assert (Hsupports : SupportingNormal
          (qcone_generated generators) normal).
      { exact (proj1 (List.Forall_forall _ _) Hsupport normal Hnormal). }
      assert (Hgenerator_nonnegative : 0 <= qinner normal generator).
      { apply Hsupports, qcone_generated_generator. exact H0. }
      assert (Htail_nonnegative : 0 <= qinner normal tail).
      { apply Hsupports. now apply qcone_combination_as_generated. }
      assert (Hsum :
          coefficient * qinner normal generator + qinner normal tail == 0).
      { transitivity
          (qinner normal
            (qvec_add (qvec_scale coefficient generator) tail)).
        - transitivity
            (qinner normal (qvec_scale coefficient generator) +
              qinner normal tail).
          + apply Qplus_comp;
              [symmetry; apply qinner_scale_right|reflexivity].
          + symmetry. apply qinner_add_right.
        - apply Horthogonal. exact Hnormal. }
      assert (Hproduct_nonnegative :
          0 <= coefficient * qinner normal generator).
      { now apply Qmult_le_0_compat. }
      assert (Htail_le_sum :
          qinner normal tail <=
            coefficient * qinner normal generator + qinner normal tail).
      { apply (proj2 (Qplus_le_r
          0 (coefficient * qinner normal generator)
          (qinner normal tail))) in Hproduct_nonnegative.
        setoid_replace (qinner normal tail + 0)
          with (qinner normal tail) in Hproduct_nonnegative by ring.
        setoid_replace
          (qinner normal tail +
            coefficient * qinner normal generator)
          with
          (coefficient * qinner normal generator +
            qinner normal tail) in Hproduct_nonnegative by ring.
        exact Hproduct_nonnegative. }
      setoid_rewrite Hsum in Htail_le_sum.
      now apply Qle_antisym. }
    specialize (IHHpoint Htail_orthogonal).
    destruct (Qeq_dec coefficient 0) as [Hzero|Hnonzero].
    + assert (Heq : QVecEq
          (qvec_add (qvec_scale coefficient generator) tail) tail).
      { intro index. unfold qvec_add, qvec_scale.
        setoid_rewrite Hzero. ring. }
      apply (proj2 (qcone_generated_qvec_ext d
        (face_generators normals generators)
        (qvec_add (qvec_scale coefficient generator) tail) tail Heq)).
      exact IHHpoint.
    + assert (Hcoefficient_positive : 0 < coefficient).
      { destruct (Qlt_le_dec 0 coefficient) as [Hpositive|Hnegative];
          [exact Hpositive|].
        exfalso. apply Hnonzero. apply Qle_antisym; assumption. }
      assert (Hgenerator_orthogonal : NormalOrthogonal normals generator).
      { intros normal Hnormal.
        assert (Hsupports : SupportingNormal
            (qcone_generated generators) normal).
        { exact (proj1 (List.Forall_forall _ _) Hsupport normal Hnormal). }
        assert (Hgenerator_nonnegative : 0 <= qinner normal generator).
        { apply Hsupports, qcone_generated_generator. exact H0. }
        assert (Htail_nonnegative : 0 <= qinner normal tail).
        { apply Hsupports. now apply qcone_combination_as_generated. }
        assert (Hsum :
            coefficient * qinner normal generator + qinner normal tail == 0).
        { transitivity
            (qinner normal
              (qvec_add (qvec_scale coefficient generator) tail)).
          - transitivity
              (qinner normal (qvec_scale coefficient generator) +
                qinner normal tail).
            + apply Qplus_comp;
                [symmetry; apply qinner_scale_right|reflexivity].
            + symmetry. apply qinner_add_right.
          - apply Horthogonal. exact Hnormal. }
        assert (Htail_zero : qinner normal tail == 0).
        { apply Htail_orthogonal. exact Hnormal. }
        assert (Hproduct_zero :
            coefficient * qinner normal generator == 0).
        { transitivity
            (coefficient * qinner normal generator + qinner normal tail).
          - setoid_rewrite Htail_zero. ring.
          - exact Hsum. }
        destruct (Qmult_integral _ _ Hproduct_zero) as
          [Hcoefficient_zero|Hgenerator_zero].
        - contradiction.
        - exact Hgenerator_zero. }
      apply qcone_generated_add.
      * apply qcone_generated_scale; [exact H|].
        apply qcone_generated_generator, filter_In. split; [exact H0|].
        now apply generator_on_normals_spec.
      * exact IHHpoint.
Qed.

Theorem face_generator_filter : forall d
    (generators normals : list (QVec d)),
    List.Forall
      (SupportingNormal (qcone_generated generators)) normals ->
    SameSet
      (qcone_generated (face_generators normals generators))
      (fun point =>
        qcone_generated generators point /\
        NormalOrthogonal normals point).
Proof.
  intros d generators normals Hsupport point. split.
  - intros [generated [Hgenerated Hpoint]]. split.
    + exists generated. split.
      * apply qcone_combination_weaken with
          (source := face_generators normals generators).
        -- intros generator Hin. apply filter_In in Hin. exact (proj1 Hin).
        -- exact Hgenerated.
      * exact Hpoint.
    + apply (proj2 (normal_orthogonal_qvec_ext d normals point generated
        Hpoint)).
      now apply qcone_combination_face_orthogonal with
        (generators := generators).
  - intros [[generated [Hgenerated Hpoint]] Horthogonal].
    assert (Hgenerated_orthogonal : NormalOrthogonal normals generated).
    { apply (proj1 (normal_orthogonal_qvec_ext d normals point generated
        Hpoint)). exact Horthogonal. }
    apply (proj2 (qcone_generated_qvec_ext d
      (face_generators normals generators) point generated Hpoint)).
    now apply qcone_combination_filter.
Qed.

Theorem face_self : forall d (cone : QSet d), FaceOf cone cone.
Proof.
  intros d cone. exists []. split; [constructor|]. intro point. split.
  - intro Hpoint. split; [exact Hpoint|intros normal Hnormal; contradiction].
  - intros [Hpoint _]. exact Hpoint.
Qed.

Theorem face_subset : forall d (cone face : QSet d),
    FaceOf cone face -> forall point, face point -> cone point.
Proof.
  intros d cone face [normals [_ Hface]] point Hpoint.
  exact (proj1 (proj1 (Hface point) Hpoint)).
Qed.

Theorem face_contains_zero : forall d (cone face : QSet d),
    IsCone cone -> FaceOf cone face -> face (qvec_zero d).
Proof.
  intros d cone face Hcone [normals [_ Hface]].
  apply (proj2 (Hface (qvec_zero d))). split.
  - exact (cone_contains_zero _ Hcone).
  - intros normal _. apply qinner_zero_right.
Qed.

Theorem face_is_cone : forall d (cone face : QSet d),
    IsCone cone -> FaceOf cone face -> IsCone face.
Proof.
  intros d cone face Hcone Hface.
  destruct Hface as [normals [Hsupport Hface]]. constructor.
  - apply (proj2 (Hface (qvec_zero d))). split.
    + exact (cone_contains_zero _ Hcone).
    + intros normal _. apply qinner_zero_right.
  - intros left right Hleft Hright.
    apply (proj2 (Hface (qvec_add left right))).
    apply (proj1 (Hface left)) in Hleft as [Hleft Hleft_orthogonal].
    apply (proj1 (Hface right)) in Hright as [Hright Hright_orthogonal].
    split.
    + now apply (cone_closed_add _ Hcone).
    + intros normal Hnormal. transitivity
        (qinner normal left + qinner normal right).
      * apply qinner_add_right.
      * setoid_rewrite (Hleft_orthogonal normal Hnormal).
        setoid_rewrite (Hright_orthogonal normal Hnormal). ring.
  - intros coefficient point Hcoefficient Hpoint.
    apply (proj2 (Hface (qvec_scale coefficient point))).
    apply (proj1 (Hface point)) in Hpoint as [Hpoint Horthogonal]. split.
    + now apply (cone_closed_scale _ Hcone).
    + intros normal Hnormal. transitivity
        (coefficient * qinner normal point).
      * apply qinner_scale_right.
      * setoid_rewrite (Horthogonal normal Hnormal). ring.
Qed.

Lemma face_qvec_ext : forall d (cone face : QSet d),
    FaceOf cone face ->
    (forall left right, QVecEq left right -> (cone left <-> cone right)) ->
    forall left right, QVecEq left right -> (face left <-> face right).
Proof.
  intros d cone face [normals [_ Hface]] Hcone left right Heq.
  rewrite (Hface left), (Hface right), (Hcone left right Heq),
    (normal_orthogonal_qvec_ext d normals left right Heq).
  reflexivity.
Qed.

Theorem polyhedral_face_finitely_generated : forall d
    (cone face : QSet d),
    RationalPolyhedralCone cone -> FaceOf cone face ->
    RationalPolyhedralCone face.
Proof.
  intros d cone face [generators Hcone]
    [normals [Hsupport Hface]].
  assert (Hsupport_generated : List.Forall
      (SupportingNormal (qcone_generated generators)) normals).
  { apply (proj2 (List.Forall_forall _ _)). intros normal Hnormal.
    assert (Hnormal_support : SupportingNormal cone normal).
    { exact (proj1 (List.Forall_forall _ _) Hsupport normal Hnormal). }
    intros point Hpoint. apply Hnormal_support.
    exact (proj2 (Hcone point) Hpoint). }
  exists (face_generators normals generators). intro point. split.
  - intro Hpoint. apply (proj2 (face_generator_filter d generators normals
      Hsupport_generated point)).
    apply (proj1 (Hface point)) in Hpoint as [Hpoint Horthogonal]. split.
    + exact (proj1 (Hcone point) Hpoint).
    + exact Horthogonal.
  - intro Hpoint. apply (proj2 (Hface point)).
    apply (proj1 (face_generator_filter d generators normals
      Hsupport_generated point)) in Hpoint as [Hpoint Horthogonal]. split.
    + exact (proj2 (Hcone point) Hpoint).
    + exact Horthogonal.
Qed.
