From Coq Require Import Classical_Prop List Vector ZArith.
From KruskalAfProp Require Import af.af.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import Cone Faces FaceStrippingExtract Periodic
  RationalDefinability.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.

Definition CylindricSlice {d} (period set : ZSet d)
    (base increment : ZVec d) : Prop :=
  period increment /\ set (zvec_add base increment).

Lemma finitary_qcylindric_implies_cylindric : forall d
    (period set : ZSet d),
    Periodic period ->
    FinitaryQCylindric period set ->
    QCylindric period set.
Proof.
  intros d period set Hperiodic [bases Hbases]
    value increment Hvalue Hincrement.
  apply (proj2 (Hbases (zvec_add value increment))).
  apply (proj1 (Hbases value)) in Hvalue.
  destruct Hvalue as [base [tail [Hbase [Htail Hvalue]]]].
  exists base, (zvec_add tail increment). repeat split.
  - exact Hbase.
  - now apply (proj2 Hperiodic tail increment).
  - subst value. apply zvec_add_assoc.
Qed.

Lemma slice_subset_period : forall d (period set : ZSet d) base increment,
    CylindricSlice period set base increment -> period increment.
Proof. firstorder. Qed.

Lemma slice_upward_closed : forall d (period set : ZSet d) base,
    Periodic period ->
    QCylindric period set ->
    forall left right,
      CylindricSlice period set base left ->
      PeriodicLe period left right ->
      CylindricSlice period set base right.
Proof.
  intros d period set base Hperiodic Hcylindric left right
    [Hleft_period Hleft_set] Hle. split.
  - unfold PeriodicLe in Hle.
    replace right with (zvec_add left (zvec_sub right left)).
    + now apply (proj2 Hperiodic).
    + apply zvec_sub_add_cancel.
  - unfold PeriodicLe in Hle.
    replace (zvec_add base right)
      with (zvec_add (zvec_add base left) (zvec_sub right left)).
    + now apply Hcylindric.
    + rewrite zvec_add_assoc, zvec_sub_add_cancel. reflexivity.
Qed.

Lemma slice_finite_cover : forall d (period set : ZSet d) base,
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    QCylindric period set ->
    exists basis : list {increment : ZVec d |
        CylindricSlice period set base increment},
      forall increment,
        CylindricSlice period set base increment ->
        exists minimum,
          List.In minimum basis /\
          PeriodicLe period (proj1_sig minimum) increment.
Proof.
  intros d period set base Hperiodic Hfinite Hcylindric.
  assert (Hwqo : @KruskalAfProp.af.af.afs (ZVec d) period
      (PeriodicLe period)).
  { apply (proj2 (periodic_order_wqo_iff_finitely_generated
      d period Hperiodic)). exact Hfinite. }
  assert (Hslice_wqo : @KruskalAfProp.af.af.afs (ZVec d)
      (CylindricSlice period set base) (PeriodicLe period)).
  { eapply afs_mono with (3 := Hwqo); firstorder. }
  destruct (restricted_af_finite_cover_classic _ _ _ Hslice_wqo)
    as [basis Hcover]. exists basis.
  intros increment Hincrement.
  destruct (Hcover (exist _ increment Hincrement))
    as [minimum [Hminimum Hle]].
  now exists minimum.
Qed.

Definition translated_slice_basis {d} (base : ZVec d)
    {period set : ZSet d}
    (basis : list {increment : ZVec d |
      CylindricSlice period set base increment}) : list (ZVec d) :=
  List.map (fun minimum => zvec_add base (proj1_sig minimum)) basis.

Lemma finite_base_translation : forall d (period set : ZSet d) base,
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    QCylindric period set ->
    exists translated : list (ZVec d),
      (forall value, List.In value translated -> set value) /\
      forall increment,
        CylindricSlice period set base increment ->
        exists translated_base remainder,
          List.In translated_base translated /\
          period remainder /\
          zvec_add base increment =
            zvec_add translated_base remainder.
Proof.
  intros d period set base Hperiodic Hfinite Hcylindric.
  destruct (slice_finite_cover d period set base Hperiodic Hfinite
    Hcylindric) as [basis Hcover].
  exists (translated_slice_basis base basis). split.
  - intros value Hvalue. apply in_map_iff in Hvalue.
    destruct Hvalue as [minimum [Hvalue Hminimum]]. subst value.
    exact (proj2 (proj2_sig minimum)).
  - intros increment Hincrement.
    destruct (Hcover increment Hincrement) as
      [minimum [Hminimum Hle]].
    exists (zvec_add base (proj1_sig minimum)),
      (zvec_sub increment (proj1_sig minimum)). repeat split.
    + unfold translated_slice_basis. apply in_map_iff.
      exists minimum. now split.
    + exact Hle.
    + rewrite zvec_add_assoc, zvec_sub_add_cancel. reflexivity.
Qed.

Lemma finite_base_union : forall d (period set : ZSet d) bases,
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    QCylindric period set ->
    exists generated_bases : list (ZVec d),
      (forall value, List.In value generated_bases -> set value) /\
      forall base increment,
        List.In base bases ->
        CylindricSlice period set base increment ->
        exists generated_base remainder,
          List.In generated_base generated_bases /\
          period remainder /\
          zvec_add base increment =
            zvec_add generated_base remainder.
Proof.
  intros d period set bases. induction bases as [|base bases IH];
    intros Hperiodic Hfinite Hcylindric.
  - exists []. split; [firstorder|]. intros base increment Hbase.
    contradiction.
  - destruct (finite_base_translation d period set base Hperiodic Hfinite
      Hcylindric) as [head_bases [Hhead_sound Hhead_cover]].
    destruct (IH Hperiodic Hfinite Hcylindric)
      as [tail_bases [Htail_sound Htail_cover]].
    exists (head_bases ++ tail_bases). split.
    + intros value Hvalue. apply in_app_iff in Hvalue.
      destruct Hvalue; [now apply Hhead_sound|now apply Htail_sound].
    + intros source increment Hsource Hincrement.
      destruct Hsource as [Hsource|Hsource].
      * subst source.
        destruct (Hhead_cover increment Hincrement) as
          [generated_base [remainder [Hin [Hremainder Heq]]]].
        exists generated_base, remainder. repeat split; try assumption.
        now apply in_or_app; left.
      * destruct (Htail_cover source increment Hsource Hincrement) as
          [generated_base [remainder [Hin [Hremainder Heq]]]].
        exists generated_base, remainder. repeat split; try assumption.
        now apply in_or_app; right.
Qed.

Theorem finitary_qcylindric_sub :
  forall d (period A B : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    QCylindric period A ->
    FinitaryQCylindric period B ->
    (forall x, A x -> B x) ->
    FinitaryQCylindric period A.
Proof.
  intros d period A B Hperiodic Hfinite HA_cylindric
    [bases HB] Hsubset.
  destruct (finite_base_union d period A bases Hperiodic Hfinite
    HA_cylindric) as [generated_bases [Hsound Hcover]].
  exists generated_bases. intro value. split.
  - intro Hvalue.
    assert (HBvalue : B value) by now apply Hsubset.
    apply (proj1 (HB value)) in HBvalue.
    destruct HBvalue as [base [increment [Hbase [Hincrement Hvalue_eq]]]].
    assert (Hslice : CylindricSlice period A base increment).
    { split; [exact Hincrement|]. now rewrite <- Hvalue_eq. }
    destruct (Hcover base increment Hbase Hslice) as
      [generated_base [remainder [Hgenerated [Hremainder Heq]]]].
    exists generated_base, remainder. repeat split; try assumption.
    now rewrite Hvalue_eq, Heq.
  - intros [base [increment [Hbase [Hincrement Hvalue]]]].
    rewrite Hvalue. apply HA_cylindric.
    + now apply Hsound.
    + exact Hincrement.
Qed.

Lemma period_finitary_self : forall d (period : ZSet d),
    Periodic period -> FinitaryQCylindric period period.
Proof.
  intros d period Hperiodic. exists [zvec_zero d]. intro value. split.
  - intro Hvalue. exists (zvec_zero d), value. repeat split.
    + now left.
    + exact Hvalue.
    + now rewrite zvec_add_zero_left.
  - intros [base [increment [[Hbase|Hbase] [Hincrement Hvalue]]]].
    + subst base. rewrite zvec_add_zero_left in Hvalue.
      subst value. exact Hincrement.
    + contradiction.
Qed.

Lemma empty_finitary_qcylindric : forall d (period : ZSet d),
    FinitaryQCylindric period (fun _ => False).
Proof.
  intros d period. exists []. intro value. split; [contradiction|].
  intros [base [increment [Hbase _]]]. contradiction.
Qed.

Theorem extract_remainder_finitary :
  forall d
    (period excluded remaining : ZSet d)
    (face : QSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FaceOf (Cone period) face ->
    QCylindric period excluded ->
    FinitaryQCylindric period remaining ->
    (forall value,
      excluded value -> remaining value) ->
    FinitaryQCylindric period
      (fun value =>
        remaining value /\
        ~ ExtractFace period face excluded remaining value).
Proof.
  intros d period excluded remaining face Hperiodic Hfinite Hface
    Hexcluded Hremaining Hsubset.
  assert (Hremaining_cylindric : QCylindric period remaining).
  { now apply finitary_qcylindric_implies_cylindric. }
  apply (finitary_qcylindric_sub d period
    (fun value => remaining value /\
      ~ ExtractFace period face excluded remaining value)
    remaining Hperiodic Hfinite).
  - now apply extract_remainder_cylindric.
  - exact Hremaining.
  - firstorder.
Qed.
