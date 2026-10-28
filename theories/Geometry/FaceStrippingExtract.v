From Coq Require Import Classical_Prop Fin Lia List QArith Qring Vector
  VectorSpec ZArith.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone Faces LatticeGordanV
  MathCompBridge Periodic QConeCore RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Definition QCylindric {d} (period set : ZSet d) : Prop :=
  forall base increment,
    set base -> period increment -> set (zvec_add base increment).

Definition FinitaryQCylindric {d} (period set : ZSet d) : Prop :=
  exists bases : list (ZVec d),
    SameSet set
      (fun value => exists base increment,
        List.In base bases /\ period increment /\
        value = zvec_add base increment).

Definition FacePeriod {d} (period : ZSet d) (face : QSet d) : ZSet d :=
  fun value => period value /\ face (zvec_to_qvec value).

Definition face_zgenerators {d} (normals : list (QVec d))
    (generators : list (ZVec d)) : list (ZVec d) :=
  List.filter
    (fun generator => generator_on_normals normals
      (zvec_to_qvec generator)) generators.

Fixpoint face_ncoefficients {d} (normals : list (QVec d))
    (generators : list (ZVec d)) (coefficients : list nat) : list nat :=
  match generators, coefficients with
  | generator :: generators', coefficient :: coefficients' =>
      if generator_on_normals normals (zvec_to_qvec generator)
      then coefficient :: face_ncoefficients normals generators' coefficients'
      else face_ncoefficients normals generators' coefficients'
  | _, _ => []
  end.

Lemma face_ncoefficients_length : forall d normals
    (generators : list (ZVec d)) coefficients,
    length coefficients = length generators ->
    length (face_ncoefficients normals generators coefficients) =
      length (face_zgenerators normals generators).
Proof.
  intros d normals generators. induction generators as [|generator generators IH];
    intros coefficients Hlength.
  - destruct coefficients; [reflexivity|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    unfold face_zgenerators in *. cbn.
    destruct (generator_on_normals normals (zvec_to_qvec generator));
      cbn; f_equal; now apply IH.
Qed.

Lemma q_of_nat_nonnegative : forall value, 0 <= q_of_nat value.
Proof. intro value. unfold q_of_nat, Qle. cbn. lia. Qed.

Lemma face_linear_combination_filter : forall d
    (period : ZSet d) normals generators coefficients,
    Periodic period ->
    List.Forall period generators ->
    List.Forall (SupportingNormal (Cone period)) normals ->
    length coefficients = length generators ->
    NormalOrthogonal normals
      (zvec_to_qvec (zvec_linear_combination generators coefficients)) ->
    zvec_linear_combination (face_zgenerators normals generators)
      (face_ncoefficients normals generators coefficients) =
    zvec_linear_combination generators coefficients.
Proof.
  intros d period normals generators. induction generators as
      [|generator generators IH]; intros coefficients Hperiodic Hall Hsupport
      Hlength Horthogonal.
  - destruct coefficients; [reflexivity|discriminate].
  - destruct coefficients as [|coefficient coefficients]; [discriminate|].
    cbn in Hlength. injection Hlength as Hlength.
    inversion Hall as [|generator' generators' Hgenerator Hgenerators]; subst.
    assert (Htail_period :
        period (zvec_linear_combination generators coefficients)).
    { apply (generated_in_periodic d period generators
        (zvec_linear_combination generators coefficients) Hperiodic).
      - intros value Hin. now apply (proj1 (List.Forall_forall _ _)
          Hgenerators value Hin).
      - now apply zvec_generated_list_coefficients. }
    assert (Htail_orthogonal : NormalOrthogonal normals
        (zvec_to_qvec (zvec_linear_combination generators coefficients))).
    { intros normal Hnormal.
      assert (Hnormal_support : SupportingNormal (Cone period) normal).
      { now apply (proj1 (List.Forall_forall _ _) Hsupport normal Hnormal). }
      assert (Hgenerator_nonnegative :
          0 <= qinner normal (zvec_to_qvec generator)).
      { apply Hnormal_support, cone_contains_source. exact Hgenerator. }
      assert (Htail_nonnegative :
          0 <= qinner normal
            (zvec_to_qvec (zvec_linear_combination generators coefficients))).
      { apply Hnormal_support, cone_contains_source. exact Htail_period. }
      assert (Hdecompose : QVecEq
          (zvec_to_qvec
            (zvec_linear_combination (generator :: generators)
              (coefficient :: coefficients)))
          (qvec_add
            (qvec_scale (q_of_nat coefficient) (zvec_to_qvec generator))
            (zvec_to_qvec
              (zvec_linear_combination generators coefficients)))).
      { cbn [zvec_linear_combination].
        eapply qvec_eq_trans; [apply zvec_to_qvec_add|].
        apply qvec_eq_add; [apply zvec_nsmul_to_qvec|apply qvec_eq_refl]. }
      assert (Hsum :
          q_of_nat coefficient * qinner normal (zvec_to_qvec generator) +
            qinner normal
              (zvec_to_qvec
                (zvec_linear_combination generators coefficients)) == 0).
      { transitivity (qinner normal
          (qvec_add
            (qvec_scale (q_of_nat coefficient) (zvec_to_qvec generator))
            (zvec_to_qvec
              (zvec_linear_combination generators coefficients)))).
        - symmetry. transitivity
            (qinner normal
              (qvec_scale (q_of_nat coefficient)
                (zvec_to_qvec generator)) +
             qinner normal
              (zvec_to_qvec
                (zvec_linear_combination generators coefficients))).
          + apply qinner_add_right.
          + apply Qplus_comp; [apply qinner_scale_right|reflexivity].
        - transitivity (qinner normal
            (zvec_to_qvec
              (zvec_linear_combination (generator :: generators)
                (coefficient :: coefficients)))).
          + symmetry. now apply qinner_qvec_ext_right.
          + apply Horthogonal. exact Hnormal. }
      apply qnonnegative_sum_zero_right with
        (left := q_of_nat coefficient *
          qinner normal (zvec_to_qvec generator)).
      - apply Qmult_le_0_compat; [apply q_of_nat_nonnegative|assumption].
      - exact Htail_nonnegative.
      - exact Hsum. }
    specialize (IH coefficients Hperiodic Hgenerators Hsupport Hlength
      Htail_orthogonal).
    unfold face_zgenerators in *. cbn.
    destruct (generator_on_normals normals (zvec_to_qvec generator))
      eqn:Hgenerator_face.
    + cbn. now rewrite IH.
    + assert (Hnot_orthogonal :
          ~ NormalOrthogonal normals (zvec_to_qvec generator)).
      { intro Hcontra. apply generator_on_normals_spec in Hcontra.
        now rewrite Hgenerator_face in Hcontra. }
      assert (Hexists_normal : exists normal,
          List.In normal normals /\
          ~ qinner normal (zvec_to_qvec generator) == 0).
      { destruct (classic (exists normal,
            List.In normal normals /\
            ~ qinner normal (zvec_to_qvec generator) == 0)) as [H|H];
          [exact H|].
        exfalso. apply Hnot_orthogonal. intros normal Hnormal.
        destruct (classic (qinner normal (zvec_to_qvec generator) == 0));
          [assumption|].
        exfalso. apply H. now exists normal. }
      destruct Hexists_normal as [normal [Hnormal Hnormal_nonzero]].
      assert (Hnormal_support : SupportingNormal (Cone period) normal).
      { now apply (proj1 (List.Forall_forall _ _) Hsupport normal Hnormal). }
      assert (Hgenerator_nonnegative :
          0 <= qinner normal (zvec_to_qvec generator)).
      { apply Hnormal_support, cone_contains_source. exact Hgenerator. }
      assert (Htail_nonnegative :
          0 <= qinner normal
            (zvec_to_qvec (zvec_linear_combination generators coefficients))).
      { apply Hnormal_support, cone_contains_source. exact Htail_period. }
      assert (Hdecompose : QVecEq
          (zvec_to_qvec
            (zvec_linear_combination (generator :: generators)
              (coefficient :: coefficients)))
          (qvec_add
            (qvec_scale (q_of_nat coefficient) (zvec_to_qvec generator))
            (zvec_to_qvec
              (zvec_linear_combination generators coefficients)))).
      { cbn [zvec_linear_combination].
        eapply qvec_eq_trans; [apply zvec_to_qvec_add|].
        apply qvec_eq_add; [apply zvec_nsmul_to_qvec|apply qvec_eq_refl]. }
      assert (Hsum :
          q_of_nat coefficient * qinner normal (zvec_to_qvec generator) +
            qinner normal
              (zvec_to_qvec
                (zvec_linear_combination generators coefficients)) == 0).
      { transitivity (qinner normal
          (qvec_add
            (qvec_scale (q_of_nat coefficient) (zvec_to_qvec generator))
            (zvec_to_qvec
              (zvec_linear_combination generators coefficients)))).
        - symmetry. transitivity
            (qinner normal
              (qvec_scale (q_of_nat coefficient)
                (zvec_to_qvec generator)) +
             qinner normal
              (zvec_to_qvec
                (zvec_linear_combination generators coefficients))).
          + apply qinner_add_right.
          + apply Qplus_comp; [apply qinner_scale_right|reflexivity].
        - transitivity (qinner normal
            (zvec_to_qvec
              (zvec_linear_combination (generator :: generators)
                (coefficient :: coefficients)))).
          + symmetry. now apply qinner_qvec_ext_right.
          + apply Horthogonal. exact Hnormal. }
      assert (Hproduct_zero :
          q_of_nat coefficient *
            qinner normal (zvec_to_qvec generator) == 0).
      { apply qnonnegative_sum_zero_left with
          (right := qinner normal
            (zvec_to_qvec (zvec_linear_combination generators coefficients))).
        - apply Qmult_le_0_compat; [apply q_of_nat_nonnegative|assumption].
        - exact Htail_nonnegative.
        - exact Hsum. }
      destruct (Qmult_integral _ _ Hproduct_zero) as
        [Hcoefficient_zero|Hnormal_zero]; [|contradiction].
      assert (Hcoefficient : coefficient = 0%nat).
      { unfold q_of_nat in Hcoefficient_zero.
        apply (proj1 (inject_Z_injective (Z.of_nat coefficient) 0%Z))
          in Hcoefficient_zero. lia. }
      subst coefficient. cbn. rewrite zvec_add_zero_left. exact IH.
Qed.

Lemma face_periodic : forall d (period : ZSet d) (face : QSet d),
    Periodic period ->
    FaceOf (Cone period) face ->
    Periodic (FacePeriod period face).
Proof.
  intros d period face Hperiodic Hface.
  pose proof (face_is_cone d (Cone period) face
    (cone_is_cone d period) Hface) as Hface_cone.
  split.
  - split; [exact (proj1 Hperiodic)|].
    apply (proj2 (face_qvec_ext d (Cone period) face Hface
      (fun x y Heq => cone_qvec_extensional d period x y Heq)
      (zvec_to_qvec (zvec_zero d)) (qvec_zero d)
      (zvec_to_qvec_zero_v d))).
    apply (cone_contains_zero face Hface_cone).
  - intros left right [Hleft_period Hleft_face]
      [Hright_period Hright_face]. split.
    + now apply (proj2 Hperiodic left right).
    + apply (proj2 (face_qvec_ext d (Cone period) face Hface
        (fun x y Heq => cone_qvec_extensional d period x y Heq)
        (zvec_to_qvec (zvec_add left right))
        (qvec_add (zvec_to_qvec left) (zvec_to_qvec right))
        (zvec_to_qvec_add d left right))).
      now apply (cone_closed_add face Hface_cone).
Qed.

Lemma face_periodic_finitely_generated : forall d
    (period : ZSet d) (face : QSet d),
    FinitelyGeneratedPeriodic period ->
    FaceOf (Cone period) face ->
    FinitelyGeneratedPeriodic (FacePeriod period face).
Proof.
  intros d period face [generators [Hgenerators Hgenerated]] Hface.
  destruct Hface as [normals [Hsupport Hface]].
  set (selected := face_zgenerators normals generators).
  assert (Hperiodic : Periodic period).
  { apply finitely_generated_periodic_is_periodic.
    exists generators. now split. }
  assert (Hface_original : FaceOf (Cone period) face).
  { exists normals. now split. }
  assert (Hselected : forall generator,
      List.In generator selected -> FacePeriod period face generator).
  { intros generator Hin. unfold selected, face_zgenerators in Hin.
    apply filter_In in Hin as [Hin Hfilter]. split.
    - now apply Hgenerators.
    - apply (proj2 (Hface (zvec_to_qvec generator))). split.
      + apply cone_contains_source. now apply Hgenerators.
      + now apply generator_on_normals_spec. }
  exists selected. split; [exact Hselected|]. intro value. split.
  - intros [Hvalue_period Hvalue_face].
    apply (proj1 (Hgenerated value)) in Hvalue_period.
    destruct Hvalue_period as [coefficients Hcoefficients].
    unfold zvec_generated.
    assert (Hselected_length :
        length (face_ncoefficients normals generators
          (Vector.to_list coefficients)) = length selected).
    { unfold selected. apply face_ncoefficients_length, length_to_list. }
    rewrite <- Hselected_length.
    exists (Vector.of_list
      (face_ncoefficients normals generators
        (Vector.to_list coefficients))).
    rewrite to_list_of_list_opp.
    unfold selected.
    rewrite (face_linear_combination_filter d period normals generators
      (Vector.to_list coefficients) Hperiodic).
    + exact Hcoefficients.
    + apply List.Forall_forall. intros generator Hin.
      now apply Hgenerators.
    + exact Hsupport.
    + apply length_to_list.
    + apply (proj1 (Hface (zvec_to_qvec value))) in Hvalue_face.
      rewrite Hcoefficients. exact (proj2 Hvalue_face).
  - intro Hvalue_generated.
    apply (generated_in_periodic d (FacePeriod period face) selected value).
    + exact (face_periodic d period face Hperiodic Hface_original).
    + exact Hselected.
    + exact Hvalue_generated.
Qed.

Definition ExtractFace {d} (period : ZSet d) (face : QSet d)
    (excluded remaining : ZSet d) : ZSet d :=
  fun value => forall increment,
    FacePeriod period face increment ->
    remaining (zvec_add value increment) /\
    ~ excluded (zvec_add value increment).

Lemma extract_face_subset_difference : forall d
    (period excluded remaining : ZSet d) (face : QSet d),
    Periodic (FacePeriod period face) ->
    forall value,
      ExtractFace period face excluded remaining value ->
      remaining value /\ ~ excluded value.
Proof.
  intros d period excluded remaining face Hperiodic value Hextract.
  specialize (Hextract (zvec_zero d) (proj1 Hperiodic)).
  now rewrite zvec_add_zero_right in Hextract.
Qed.

Lemma extract_face_cylindric : forall d
    (period excluded remaining : ZSet d) (face : QSet d),
    Periodic (FacePeriod period face) ->
    QCylindric (FacePeriod period face)
      (ExtractFace period face excluded remaining).
Proof.
  intros d period excluded remaining face Hperiodic
    base increment Hbase Hincrement tail Htail.
  specialize (Hbase (zvec_add increment tail)
    (proj2 Hperiodic increment tail Hincrement Htail)).
  now rewrite zvec_add_assoc.
Qed.

Lemma face_period_self : forall d (period : ZSet d),
    Periodic period ->
    SameSet (FacePeriod period (Cone period)) period.
Proof.
  intros d period Hperiodic value. split.
  - now intros [Hvalue _].
  - intro Hvalue. split; [exact Hvalue|now apply cone_contains_source].
Qed.

Lemma extract_empty_excluded_face_period : forall d
    (period : ZSet d) (face : QSet d),
    Periodic (FacePeriod period face) ->
    SameSet
      (ExtractFace period face (fun _ => False) (FacePeriod period face))
      (FacePeriod period face).
Proof.
  intros d period face Hperiodic value. split.
  - intro Hextract. exact (proj1 (extract_face_subset_difference d period
      (fun _ => False) (FacePeriod period face) face Hperiodic value Hextract)).
  - intros Hvalue increment Hincrement. split.
    + now apply (proj2 Hperiodic value increment).
    + tauto.
Qed.

Lemma extract_equal_excluded_empty : forall d
    (period remaining : ZSet d) (face : QSet d),
    Periodic (FacePeriod period face) ->
    forall value, ~ ExtractFace period face remaining remaining value.
Proof.
  intros d period remaining face Hperiodic value Hextract.
  specialize (Hextract (zvec_zero d) (proj1 Hperiodic)).
  tauto.
Qed.

Lemma extract_face_not_period_cylindric_if_proper : forall d
    (period : ZSet d) (face : QSet d),
    Periodic period ->
    FaceOf (Cone period) face ->
    (exists outside, period outside /\ ~ face (zvec_to_qvec outside)) ->
    ~ QCylindric period
      (ExtractFace period face (fun _ => False) (FacePeriod period face)).
Proof.
  intros d period face Hperiodic Hface
    [outside [Houtside_period Houtside_face]] Hcylindric.
  assert (Hface_periodic : Periodic (FacePeriod period face)).
  { now apply face_periodic. }
  assert (Hzero_extract :
      ExtractFace period face (fun _ => False) (FacePeriod period face)
        (zvec_zero d)).
  { apply (proj2 (extract_empty_excluded_face_period d period face
      Hface_periodic (zvec_zero d))).
    exact (proj1 Hface_periodic). }
  specialize (Hcylindric (zvec_zero d) outside Hzero_extract Houtside_period).
  rewrite zvec_add_zero_left in Hcylindric.
  apply (extract_face_subset_difference d period (fun _ => False)
    (FacePeriod period face) face Hface_periodic outside) in Hcylindric.
  exact (Houtside_face (proj2 (proj1 Hcylindric))).
Qed.

Lemma excluded_subset_extract_remainder : forall d
    (period excluded remaining : ZSet d) (face : QSet d),
    Periodic period ->
    FaceOf (Cone period) face ->
    (forall value, excluded value -> remaining value) ->
    forall value, excluded value ->
      remaining value /\
      ~ ExtractFace period face excluded remaining value.
Proof.
  intros d period excluded remaining face Hperiodic Hface Hsubset
    value Hexcluded. split; [now apply Hsubset|].
  intro Hextract.
  pose proof (face_periodic d period face Hperiodic Hface) as Hface_periodic.
  specialize (Hextract (zvec_zero d) (proj1 Hface_periodic)).
  rewrite zvec_add_zero_right in Hextract. now apply (proj2 Hextract).
Qed.

Lemma not_all_ex_not_classic : forall (A : Type) (property : A -> Prop),
    ~ (forall value, property value) ->
    exists value, ~ property value.
Proof.
  intros A property Hnotall.
  destruct (classic (exists value, ~ property value)) as [Hexists|Hnone];
    [exact Hexists|].
  exfalso. apply Hnotall. intro value.
  destruct (classic (property value)); [assumption|].
  exfalso. apply Hnone. now exists value.
Qed.

Lemma extract_remainder_cylindric : forall d
    (period excluded remaining : ZSet d) (face : QSet d),
    Periodic period ->
    FaceOf (Cone period) face ->
    QCylindric period excluded ->
    QCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    QCylindric period
      (fun value => remaining value /\
        ~ ExtractFace period face excluded remaining value).
Proof.
  intros d period excluded remaining face Hperiodic Hface
    Hexcluded_cyl Hremaining_cyl Hsubset base increment
    [Hbase_remaining Hbase_not_extract] Hincrement.
  split; [now apply Hremaining_cyl|].
  destruct (not_all_ex_not_classic _ _ Hbase_not_extract)
    as [face_increment Hfailure].
  assert (Hface_periodic : Periodic (FacePeriod period face)).
  { now apply face_periodic. }
  assert (Hface_increment : FacePeriod period face face_increment).
  { destruct (classic (FacePeriod period face face_increment)) as [H|H];
      [exact H|].
    exfalso. apply Hfailure. intro Hcontra. contradiction. }
  assert (Hshift_remaining :
      remaining (zvec_add base face_increment)).
  { apply Hremaining_cyl; [exact Hbase_remaining|].
    exact (proj1 Hface_increment). }
  assert (Hshift_excluded : excluded (zvec_add base face_increment)).
  { destruct (classic (excluded (zvec_add base face_increment))) as [H|H];
      [exact H|].
    exfalso. apply Hfailure. intro Hignored. split; assumption. }
  intro Hextract_shifted.
  specialize (Hextract_shifted face_increment Hface_increment).
  apply (proj2 Hextract_shifted).
  replace (zvec_add (zvec_add base increment) face_increment)
    with (zvec_add (zvec_add base face_increment) increment).
  - now apply Hexcluded_cyl.
  - rewrite !zvec_add_assoc. f_equal. apply zvec_add_comm.
Qed.
