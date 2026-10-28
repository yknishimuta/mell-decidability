From Coq Require Import Arith.PeanoNat Arith.Wf_nat Classical_Pred_Type
  Classical_Prop Lia List Permutation QArith Vector ZArith.
From KruskalAfProp Require Import af.af af.af_eq af.af_good af.af_tools.
From Mell.Core Require Import Vector.
From Mell.Geometry Require Import ClosedLinearization Cone Corollary67Finitary FaceOrder
  Faces FaceStrippingBases FaceStrippingExtract FaceStrippingFinitary FiniteFaces
  LatticeGordanH LatticeGordanInterface MathCompBridge Periodic QConeCore
  RationalDefinability RationalSpan.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.
Open Scope Q_scope.

Definition MaximalNonemptyExtractFace {d}
    (period excluded remaining : ZSet d)
    (face : QSet d) : Prop :=
  FaceOf (Cone period) face /\
  (exists value,
    ExtractFace period face excluded remaining value) /\
  forall larger,
    FaceOf (Cone period) larger ->
    FaceSubset face larger ->
    (exists value,
      ExtractFace period larger excluded remaining value) ->
    SameSet face larger.

Lemma face_period_subset : forall d (period : ZSet d)
    (smaller larger : QSet d),
    FaceSubset smaller larger ->
    forall value,
      FacePeriod period smaller value ->
      FacePeriod period larger value.
Proof. firstorder. Qed.

Theorem extract_face_antitone : forall d
    (period excluded remaining : ZSet d)
    (smaller larger : QSet d),
    FaceSubset smaller larger ->
    forall value,
      ExtractFace period larger excluded remaining value ->
      ExtractFace period smaller excluded remaining value.
Proof.
  intros d period excluded remaining smaller larger Hsubset value Hextract
    increment Hincrement.
  apply Hextract, (face_period_subset d period smaller larger Hsubset).
  exact Hincrement.
Qed.

Theorem extract_face_same_set : forall d
    (period excluded remaining : ZSet d)
    (left right : QSet d),
    SameSet left right ->
    SameSet
      (ExtractFace period left excluded remaining)
      (ExtractFace period right excluded remaining).
Proof.
  intros d period excluded remaining left right Hsame value. split;
    intro Hextract; intros increment [Hperiod Hface].
  - apply Hextract. split; [exact Hperiod|].
    now apply (proj2 (Hsame (zvec_to_qvec increment))).
  - apply Hextract. split; [exact Hperiod|].
    now apply (proj1 (Hsame (zvec_to_qvec increment))).
Qed.

Theorem maximal_nonempty_extract_face_exists : forall d
    (period excluded remaining : ZSet d),
    RationalPolyhedralCone (Cone period) ->
    (exists face value,
      FaceOf (Cone period) face /\
      ExtractFace period face excluded remaining value) ->
    exists face,
      MaximalNonemptyExtractFace period excluded remaining face.
Proof.
  intros d period excluded remaining Hpolyhedral
    [initial [initial_value [Hinitial_face Hinitial_extract]]].
  destruct (polyhedral_faces_finite d (Cone period) Hpolyhedral) as
    [faces [Hfaces_sound Hfaces_complete]].
  destruct (select_property_subsequence (QSet d)
    (fun face => exists value,
      ExtractFace period face excluded remaining value) faces) as
    [selected [Hselected_sub [Hselected_sound Hselected_complete]]].
  destruct (Hfaces_complete initial Hinitial_face) as
    [initial_rep [Hinitial_rep Hinitial_same]].
  assert (Hinitial_rep_extract : exists value,
      ExtractFace period initial_rep excluded remaining value).
  { exists initial_value.
    apply (proj1 (extract_face_same_set d period excluded remaining
      initial initial_rep Hinitial_same initial_value)).
    exact Hinitial_extract. }
  assert (Hselected_nonempty : selected <> []).
  { intro Heq. subst selected.
    specialize (Hselected_complete initial_rep Hinitial_rep
      Hinitial_rep_extract). contradiction. }
  destruct (finite_list_has_maximal (QSet d) (@ProperFaceSubset d)
    (proper_face_subset_irreflexive_relation d)
    (proper_face_subset_transitive_relation d)
    selected Hselected_nonempty) as
    [maximal [rest [Hpermutation Hmaximal]]].
  assert (Hmaximal_selected : List.In maximal selected).
  { eapply Permutation_in; [apply Permutation_sym; exact Hpermutation|].
    now left. }
  exists maximal. split.
  - apply Hfaces_sound.
    now apply list_subsequence_in with (selected := selected).
  - split.
    + now apply Hselected_sound.
    + intros larger Hlarger Hsubset Hlarger_extract.
    destruct (Hfaces_complete larger Hlarger) as
      [representative [Hrepresentative Hsame]].
    assert (Hrepresentative_extract : exists value,
        ExtractFace period representative excluded remaining value).
    { destruct Hlarger_extract as [value Hvalue]. exists value.
      apply (proj1 (extract_face_same_set d period excluded remaining
        larger representative Hsame value)). exact Hvalue. }
    assert (Hrepresentative_selected : List.In representative selected).
    { now apply Hselected_complete. }
    assert (Hsubset_rep : FaceSubset maximal representative).
    { intros point Hpoint. apply (proj1 (Hsame point)), Hsubset, Hpoint. }
      destruct (classic (SameSet maximal representative)) as
        [Hmax_rep|Hnot_same].
      * now apply same_set_trans with (middle := representative).
      * assert (Hproper : ProperFaceSubset maximal representative).
      { now split. }
        assert (Hin_cons : List.In representative (maximal :: rest)).
      { eapply Permutation_in; [exact Hpermutation|].
        exact Hrepresentative_selected. }
        destruct Hin_cons as [Heq|Hin].
        -- subst representative. exfalso.
           apply Hnot_same, same_set_refl.
        -- exfalso. now apply (Hmaximal representative Hin).
Qed.

Lemma finite_bases_afs_eq : forall d (bases : list (ZVec d)),
    @afs (ZVec d) (fun base => List.In base bases) eq.
Proof.
  intros d bases. apply afs_eq_fin. exists bases. auto.
Qed.

Theorem finitary_qcylindric_afs : forall d (period set : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FinitaryQCylindric period set ->
    @afs (ZVec d) set (PeriodicLe period).
Proof.
  intros d period set Hperiodic Hfinite [bases Hset].
  assert (Hbase : @afs (ZVec d) (fun base => List.In base bases) eq).
  { apply finite_bases_afs_eq. }
  assert (Hperiod : @afs (ZVec d) period (PeriodicLe period)).
  { apply (proj2 (periodic_order_wqo_iff_finitely_generated
      d period Hperiodic)). exact Hfinite. }
  apply af_sub_rel_afs.
  eapply af_rel_morph with
    (X := ({base : ZVec d | List.In base bases} *
      {increment : ZVec d | period increment})%type)
    (f := fun pair value =>
      proj1_sig value =
        zvec_add (proj1_sig (fst pair)) (proj1_sig (snd pair)))
    (R := fun '(base_left, increment_left)
              '(base_right, increment_right) =>
      proj1_sig base_left = proj1_sig base_right /\
      PeriodicLe period
        (proj1_sig increment_left) (proj1_sig increment_right)).
  - intros [value Hvalue]. cbn in *.
    apply (proj1 (Hset value)) in Hvalue.
    destruct Hvalue as [base [increment [Hbase_in [Hincrement Heq]]]].
    exists (exist _ base Hbase_in, exist _ increment Hincrement).
    cbn. exact Heq.
  - intros [[base_left Hbase_left] [increment_left Hincrement_left]]
      [[base_right Hbase_right] [increment_right Hincrement_right]]
      [value_left Hvalue_left] [value_right Hvalue_right]
      Hleft Hright [Hbase_eq Hincrement_le].
    cbn in Hbase_eq, Hincrement_le. subst base_right.
    cbn in Hleft, Hright. subst value_left value_right.
    unfold PeriodicLe in Hincrement_le |- *.
    change (period (Vector.map2 Z.sub
      (Vector.map2 Z.add base_left increment_right)
      (Vector.map2 Z.add base_left increment_left))).
    assert (Heq : Vector.map2 Z.sub
        (Vector.map2 Z.add base_left increment_right)
        (Vector.map2 Z.add base_left increment_left) =
        Vector.map2 Z.sub increment_right increment_left).
    { apply zvec_ext. intro index.
      repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl).
      lia. }
    rewrite Heq. exact Hincrement_le.
  - exact (@af_product
      {base : ZVec d | List.In base bases}
      {increment : ZVec d | period increment}
      (fun left right => proj1_sig left = proj1_sig right)
      (fun left right => PeriodicLe period
        (proj1_sig left) (proj1_sig right))
      (afs_af_sub_rel Hbase) (afs_af_sub_rel Hperiod)).
Qed.

Corollary finitary_qcylindric_good_pair : forall d
    (period set : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FinitaryQCylindric period set ->
    forall sequence : nat -> ZVec d,
      (forall n, set (sequence n)) ->
      exists n i j,
        (i < j < n)%nat /\
        PeriodicLe period (sequence i) (sequence j).
Proof.
  intros d period set Hperiodic Hfinite Hfinitary sequence Hsequence.
  pose proof (finitary_qcylindric_afs d period set Hperiodic Hfinite
    Hfinitary) as Hafs.
  pose proof (af_good_pair
    (R := fun left right : {value : ZVec d | set value} =>
      PeriodicLe period (proj1_sig left) (proj1_sig right))
    (fun n => exist _ (sequence n) (Hsequence n))
    (afs_af_sub_rel Hafs)) as Hpair.
  destruct Hpair as [n [i [j [Hij Hle]]]].
  exists n, i, j. now split.
Qed.

Definition EventuallyConstantIntegerSequence (sequence : nat -> Z) : Prop :=
  exists N, forall n, (N <= n)%nat -> sequence n = sequence N.

Definition TailUnboundedIntegerSequence (sequence : nat -> Z) : Prop :=
  forall bound N, exists n,
    (N <= n)%nat /\ (bound <= sequence n)%Z.

Lemma monotone_integer_le : forall (sequence : nat -> Z),
    (forall n, (sequence n <= sequence (S n))%Z) ->
    forall n m, (n <= m)%nat -> (sequence n <= sequence m)%Z.
Proof.
  intros sequence Hstep n m Hle. induction Hle.
  - apply Z.le_refl.
  - eapply Z.le_trans; [exact IHHle|apply Hstep].
Qed.

Lemma monotone_integer_bounded_tail_eventually_constant :
  forall (sequence : nat -> Z),
    (forall n, (sequence n <= sequence (S n))%Z) ->
    forall upper N,
      (forall n, (N <= n)%nat -> (sequence n <= upper)%Z) ->
      exists M, forall n, (M <= n)%nat -> sequence n = sequence M.
Proof.
  intros sequence Hstep upper.
  refine (well_founded_induction
    (well_founded_ltof nat
      (fun N => Z.to_nat (upper - sequence N)))
    (fun N =>
      (forall n, (N <= n)%nat -> (sequence n <= upper)%Z) ->
      exists M, forall n, (M <= n)%nat -> sequence n = sequence M) _).
  intros N IH Hbound.
  destruct (classic (forall n, (N <= n)%nat -> sequence n = sequence N))
    as [Hconstant|Hchanges].
  - now exists N.
  - apply not_all_ex_not in Hchanges as [M Hchanges].
    assert (HNM : (N <= M)%nat).
    { destruct (le_dec N M); [assumption|]. exfalso. apply Hchanges.
      intro. contradiction. }
    assert (Hstrict : (sequence N < sequence M)%Z).
    { pose proof (monotone_integer_le sequence Hstep N M HNM) as Hle.
      destruct (Z.eq_dec (sequence M) (sequence N)).
      - exfalso. apply Hchanges. intro. now symmetry.
      - lia. }
    assert (HNupper : (sequence N <= upper)%Z) by now apply Hbound.
    assert (HMupper : (sequence M <= upper)%Z) by now apply Hbound.
    assert (Hmeasure :
        (Z.to_nat (upper - sequence M) <
         Z.to_nat (upper - sequence N))%nat).
    { apply (proj1 (Z2Nat.inj_lt (upper - sequence M)
        (upper - sequence N) ltac:(lia) ltac:(lia))). lia. }
    apply (IH M Hmeasure).
    intros n HMn. apply Hbound. now apply Nat.le_trans with (m := M).
Qed.

Theorem monotone_integer_tail_dichotomy :
  forall (sequence : nat -> Z),
    (forall n, (sequence n <= sequence (S n))%Z) ->
    (exists N,
      forall n, (N <= n)%nat -> sequence n = sequence N) \/
    (forall bound N,
      exists n, (N <= n)%nat /\ (bound <= sequence n)%Z).
Proof.
  intros sequence Hstep.
  destruct (classic (EventuallyConstantIntegerSequence sequence))
    as [Heventual|Hnot_eventual]; [now left|right].
  intros bound N.
  destruct (classic (exists n,
      (N <= n)%nat /\ (bound <= sequence n)%Z)) as [Hexists|Hbounded].
  - exact Hexists.
  - exfalso. apply Hnot_eventual.
    apply monotone_integer_bounded_tail_eventually_constant
      with (upper := (bound - 1)%Z) (N := N); [exact Hstep|].
    intros n HNn. assert (Hnot_ge : ~ (bound <= sequence n)%Z).
    { intro Hge. apply Hbounded. exists n. now split. }
    lia.
Qed.

Lemma zinner_opp_right : forall d (normal value : ZVec d),
    zinner normal (zvec_opp value) = (- zinner normal value)%Z.
Proof.
  intros d normal value.
  replace (zvec_opp value) with (zvec_zsmul (-1) value).
  - rewrite zinner_zsmul. ring.
  - apply zvec_ext. intro index. unfold zvec_opp, zvec_zsmul.
    repeat rewrite (nth_map _ _ index index eq_refl). lia.
Qed.

Lemma zinner_sub_right : forall d (normal left right : ZVec d),
    zinner normal (zvec_sub left right) =
      (zinner normal left - zinner normal right)%Z.
Proof.
  intros d normal left right. rewrite zvec_sub_as_add_opp, zinner_add,
    zinner_opp_right. ring.
Qed.

Theorem supporting_normal_monotone : forall d
    (period : ZSet d) (normal left right : ZVec d),
    SupportingNormal (Cone period) (zvec_to_qvec normal) ->
    PeriodicLe period left right ->
    (zinner normal left <= zinner normal right)%Z.
Proof.
  intros d period normal left right Hsupport Hle.
  assert (Hnonnegative :
      (0 <= zinner normal (zvec_sub right left))%Z).
  { apply (proj1 (integer_qinner_nonnegative_iff d normal
      (zvec_sub right left))).
    apply Hsupport, cone_contains_source. exact Hle. }
  rewrite zinner_sub_right in Hnonnegative. lia.
Qed.

Theorem supporting_normal_monotone_sequence : forall d
    (period : ZSet d) (normal : ZVec d)
    (sequence : nat -> ZVec d),
    SupportingNormal (Cone period) (zvec_to_qvec normal) ->
    (forall n, PeriodicLe period (sequence n) (sequence (S n))) ->
    forall n,
      (zinner normal (sequence n) <=
       zinner normal (sequence (S n)))%Z.
Proof.
  intros d period normal sequence Hsupport Hsequence n.
  now apply supporting_normal_monotone with (period := period).
Qed.

Corollary supporting_normal_inner_tail_dichotomy : forall d
    (period : ZSet d) (normal : ZVec d)
    (sequence : nat -> ZVec d),
    SupportingNormal (Cone period) (zvec_to_qvec normal) ->
    (forall n, PeriodicLe period (sequence n) (sequence (S n))) ->
    EventuallyConstantIntegerSequence
      (fun n => zinner normal (sequence n)) \/
    TailUnboundedIntegerSequence
      (fun n => zinner normal (sequence n)).
Proof.
  intros d period normal sequence Hsupport Hsequence.
  apply monotone_integer_tail_dichotomy.
  now apply supporting_normal_monotone_sequence with (period := period).
Qed.

Definition NormalEventuallyConstant {d} (sequence : nat -> ZVec d)
    (normal : ZVec d) : Prop :=
  EventuallyConstantIntegerSequence
    (fun n => zinner normal (sequence n)).

Definition NormalTailUnbounded {d} (sequence : nat -> ZVec d)
    (normal : ZVec d) : Prop :=
  TailUnboundedIntegerSequence
    (fun n => zinner normal (sequence n)).

Lemma eventually_constant_not_tail_unbounded : forall sequence,
    EventuallyConstantIntegerSequence sequence ->
    ~ TailUnboundedIntegerSequence sequence.
Proof.
  intros sequence [N Hconstant] Hunbounded.
  destruct (Hunbounded (sequence N + 1)%Z N) as [n [HNn Hlarge]].
  rewrite (Hconstant n HNn) in Hlarge. lia.
Qed.

Theorem finite_supporting_normals_tail_classification : forall d
    (period : ZSet d) (normals : list (ZVec d))
    (sequence : nat -> ZVec d),
    List.Forall
      (fun normal =>
        SupportingNormal (Cone period) (zvec_to_qvec normal)) normals ->
    (forall n, PeriodicLe period (sequence n) (sequence (S n))) ->
    exists unbounded constant N,
      (forall normal,
        List.In normal unbounded <->
        List.In normal normals /\
          NormalTailUnbounded sequence normal) /\
      (forall normal,
        List.In normal constant <->
        List.In normal normals /\
          NormalEventuallyConstant sequence normal) /\
      (forall normal,
        List.In normal constant ->
        forall n, (N <= n)%nat ->
          zinner normal (sequence n) =
          zinner normal (sequence N)).
Proof.
  intros d period normals. induction normals as [|head tail IH];
    intros sequence Hsupport Hsequence.
  - exists [], [], 0%nat. split.
    + intro normal. split.
      * intro Hin. contradiction.
      * intros [Hin _]. contradiction.
    + split.
      * intro normal. split.
        -- intro Hin. contradiction.
        -- intros [Hin _]. contradiction.
      * intros normal Hin. contradiction.
  - pose proof (Forall_inv Hsupport) as Hhead.
    pose proof (Forall_inv_tail Hsupport) as Htail.
    destruct (IH sequence Htail Hsequence) as
      [unbounded [constant [N [Hunbounded [Hconstant Hcommon]]]]].
    destruct (supporting_normal_inner_tail_dichotomy d period head sequence
      Hhead Hsequence) as [Hhead_constant|Hhead_unbounded].
    + destruct Hhead_constant as [Nhead Hhead_constant].
      exists unbounded, (head :: constant), (Nat.max Nhead N).
      split.
      * intro normal. split; intro Hin.
        -- apply Hunbounded in Hin as [Hin Hnormal].
           split; [now right|exact Hnormal].
        -- destruct Hin as [[Heq|Hin] Hnormal].
           ++ subst normal. exfalso.
              apply (eventually_constant_not_tail_unbounded
                (fun n => zinner head (sequence n))
                (ex_intro _ Nhead Hhead_constant)). exact Hnormal.
           ++ apply Hunbounded. now split.
      * split.
        -- intro normal. split; intro Hin.
           ++ destruct Hin as [Heq|Hin].
              ** subst normal. split; [now left|now exists Nhead].
              ** apply Hconstant in Hin as [Hin Hnormal].
                 split; [now right|exact Hnormal].
           ++ destruct Hin as [[Heq|Hin] Hnormal].
              ** now left.
              ** right. apply Hconstant. now split.
        -- intros normal [Heq|Hin] n HNn.
           ++ subst normal. transitivity (zinner head (sequence Nhead)).
              ** apply Hhead_constant. lia.
              ** symmetry. apply Hhead_constant. lia.
           ++ transitivity (zinner normal (sequence N)).
              ** apply Hcommon; [exact Hin|lia].
              ** symmetry. apply Hcommon; [exact Hin|lia].
    + exists (head :: unbounded), constant, N. split.
      * intro normal. split; intro Hin.
        -- destruct Hin as [Heq|Hin].
           ++ subst normal. split; [now left|exact Hhead_unbounded].
           ++ apply Hunbounded in Hin as [Hin Hnormal].
              split; [now right|exact Hnormal].
        -- destruct Hin as [[Heq|Hin] Hnormal].
           ++ now left.
           ++ right. apply Hunbounded. now split.
      * split.
        -- intro normal. split; intro Hin.
           ++ apply Hconstant in Hin as [Hin Hnormal].
              split; [now right|exact Hnormal].
           ++ destruct Hin as [[Heq|Hin] Hnormal].
              ** subst normal. exfalso.
                 apply (eventually_constant_not_tail_unbounded
                   (fun n => zinner head (sequence n)) Hnormal).
                 exact Hhead_unbounded.
              ** apply Hconstant. now split.
        -- exact Hcommon.
Qed.
