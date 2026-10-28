From Coq Require Import Arith.PeanoNat Classical_Pred_Type Classical_Prop Lia List
  Logic.ConstructiveEpsilon Vector VectorSpec ZArith.
From Mell.Core Require Import Code Vector.
From Mell.BVAS Require Import Code RunOrder.
From Mell.Geometry Require Import Cone FaceStrippingBases FaceStrippingExtract
  FaceStrippingOrderFoundation Faces MathCompBridge Periodic QConeCore.
From Mell.Order Require Import PeriodicOrder.

Import ListNotations.
Open Scope Z_scope.

Definition StrictlyIncreasing (indices : nat -> nat) : Prop :=
  forall n, (indices n < indices (S n))%nat.

Definition InfiniteOften (property : nat -> Prop) : Prop :=
  forall N, exists n, (N <= n)%nat /\ property n.

Lemma strictly_increasing_le : forall indices,
    StrictlyIncreasing indices ->
    forall n m, (n <= m)%nat -> (indices n <= indices m)%nat.
Proof.
  intros indices H n m Hnm. induction Hnm.
  - apply Nat.le_refl.
  - eapply Nat.le_trans; [exact IHHnm|]. apply Nat.lt_le_incl, H.
Qed.

Theorem strictly_increasing_unbounded : forall indices,
    StrictlyIncreasing indices ->
    forall bound, exists n, (bound <= indices n)%nat.
Proof.
  intros indices H bound. exists bound.
  assert (Hbase : (indices 0 + bound <= indices bound)%nat).
  { induction bound as [|bound IH]; cbn; [lia|].
    specialize (H bound). lia. }
  lia.
Qed.

Theorem strictly_increasing_compose : forall outer inner,
    StrictlyIncreasing outer -> StrictlyIncreasing inner ->
    StrictlyIncreasing (fun n => outer (inner n)).
Proof.
  intros outer inner Houter Hinner n.
  apply Nat.lt_le_trans with (m := outer (S (inner n))).
  - apply Houter.
  - apply strictly_increasing_le; [exact Houter|].
    exact (Hinner n).
Qed.

Lemma not_infinite_often_eventually_not : forall property,
    ~ InfiniteOften property ->
    exists N, forall n, (N <= n)%nat -> ~ property n.
Proof.
  intros property Hnot.
  unfold InfiniteOften in Hnot.
  apply not_all_ex_not in Hnot. destruct Hnot as [N HN].
  exists N. intros n Hle HP. apply HN. exists n. auto.
Qed.

Lemma infinite_often_after : forall property,
    InfiniteOften property -> forall current,
    exists n, (current < n)%nat /\ property n.
Proof.
  intros property Hoften current.
  destruct (Hoften (S current)) as [n [Hn HP]].
  exists n. split; [lia|exact HP].
Qed.

Definition next_index (property : nat -> Prop)
    (property_dec : forall n, {property n} + {~ property n})
    (often : InfiniteOften property) (current : nat) : nat :=
  proj1_sig (constructive_indefinite_description_nat
    (fun n => (current < n)%nat /\ property n)
    (fun n =>
      match lt_dec current n, property_dec n with
      | left Hlt, left HP => left (conj Hlt HP)
      | left _, right Hnot => right (fun H => Hnot (proj2 H))
      | right Hnot, _ => right (fun H => Hnot (proj1 H))
      end)
    (infinite_often_after property often current)).

Lemma next_index_spec : forall property property_dec often current,
    (current < next_index property property_dec often current)%nat /\
    property (next_index property property_dec often current).
Proof.
  intros. unfold next_index.
  exact (proj2_sig (constructive_indefinite_description_nat
    (fun n => (current < n)%nat /\ property n)
    (fun n =>
      match lt_dec current n, property_dec n with
      | left Hlt, left HP => left (conj Hlt HP)
      | left _, right Hnot => right (fun H => Hnot (proj2 H))
      | right Hnot, _ => right (fun H => Hnot (proj1 H))
      end)
    (infinite_often_after property often current))).
Qed.

Fixpoint iterate_index (next : nat -> nat) (start n : nat) : nat :=
  match n with
  | O => start
  | S n' => next (iterate_index next start n')
  end.

Lemma infinite_often_subsequence : forall property
    (property_dec : forall n, {property n} + {~ property n}),
    InfiniteOften property ->
    exists indices,
      StrictlyIncreasing indices /\ forall n, property (indices n).
Proof.
  intros property property_dec Hoften.
  destruct (Hoften 0%nat) as [start [_ Hstart]].
  set (next := next_index property property_dec Hoften).
  exists (iterate_index next start). split.
  - intro step1. cbn. subst next.
    apply (proj1 (next_index_spec property property_dec Hoften
      (iterate_index (next_index property property_dec Hoften) start step1))).
  - intro step2. destruct step2 as [|step2]; [exact Hstart|].
    cbn. subst next.
    apply (proj2 (next_index_spec property property_dec Hoften
      (iterate_index (next_index property property_dec Hoften) start step2))).
Qed.

Lemma finite_values_eventually_above : forall (sequence : nat -> nat) bound,
    (forall value, (value <= bound)%nat ->
      ~ InfiniteOften (fun n => sequence n = value)) ->
    exists N, forall n, (N <= n)%nat -> (bound < sequence n)%nat.
Proof.
  intros sequence bound. induction bound as [|bound IH]; intro Hfinite.
  - destruct (not_infinite_often_eventually_not
      (fun n => sequence n = 0%nat) (Hfinite 0%nat (Nat.le_refl 0)))
      as [N HN].
    exists N. intros n Hle. specialize (HN n Hle). lia.
  - destruct (IH (fun value Hle => Hfinite value (ltac:(lia))))
      as [Nlower Hlower].
    destruct (not_infinite_often_eventually_not
      (fun n => sequence n = S bound)
      (Hfinite (S bound) (Nat.le_refl _))) as [Nequal Hequal].
    exists (Nat.max Nlower Nequal). intros n Hn.
    specialize (Hlower n ltac:(lia)).
    specialize (Hequal n ltac:(lia)). lia.
Qed.

Theorem nat_monotone_subsequence : forall sequence : nat -> nat,
    exists indices,
      StrictlyIncreasing indices /\
      forall n, (sequence (indices n) <= sequence (indices (S n)))%nat.
Proof.
  intro sequence.
  destruct (classic (exists value,
      InfiniteOften (fun n => sequence n = value))) as
      [[value Hoften]|Hnone].
  - destruct (infinite_often_subsequence
      (fun n => sequence n = value)
      (fun n => Nat.eq_dec (sequence n) value) Hoften) as
      [indices [Hincreasing Hvalue]].
    exists indices. split; [exact Hincreasing|].
    intro n. rewrite (Hvalue n), (Hvalue (S n)). apply Nat.le_refl.
  - assert (Hlater : forall current, exists later,
        (current < later)%nat /\
        (sequence current < sequence later)%nat).
    { intro current.
      destruct (finite_values_eventually_above sequence (sequence current))
        as [N HN].
      - intros value Hvalue Hoften. apply Hnone. now exists value.
      - exists (Nat.max (S current) N). split.
        + pose proof (Nat.le_max_l (S current) N). lia.
        + apply HN, Nat.le_max_r. }
    set (later := fun current =>
      proj1_sig (constructive_indefinite_description_nat
        (fun n => (current < n)%nat /\
          (sequence current < sequence n)%nat)
        (fun n =>
          match lt_dec current n,
                lt_dec (sequence current) (sequence n) with
          | left H1, left H2 => left (conj H1 H2)
          | left _, right H2 => right (fun H => H2 (proj2 H))
          | right H1, _ => right (fun H => H1 (proj1 H))
          end) (Hlater current))).
    exists (iterate_index later 0%nat). split.
    + intro n. cbn. unfold later.
      exact (proj1 (proj2_sig (constructive_indefinite_description_nat
        (fun m => (iterate_index later 0 n < m)%nat /\
          (sequence (iterate_index later 0 n) < sequence m)%nat)
        (fun m =>
          match lt_dec (iterate_index later 0 n) m,
                lt_dec (sequence (iterate_index later 0 n)) (sequence m) with
          | left H1, left H2 => left (conj H1 H2)
          | left _, right H2 => right (fun H => H2 (proj2 H))
          | right H1, _ => right (fun H => H1 (proj1 H))
          end) (Hlater (iterate_index later 0 n))))).
    + intro n. cbn. unfold later.
      apply Nat.lt_le_incl.
      exact (proj2 (proj2_sig (constructive_indefinite_description_nat
        (fun m => (iterate_index later 0 n < m)%nat /\
          (sequence (iterate_index later 0 n) < sequence m)%nat)
        (fun m =>
          match lt_dec (iterate_index later 0 n) m,
                lt_dec (sequence (iterate_index later 0 n)) (sequence m) with
          | left H1, left H2 => left (conj H1 H2)
          | left _, right H2 => right (fun H => H2 (proj2 H))
          | right H1, _ => right (fun H => H1 (proj1 H))
          end) (Hlater (iterate_index later 0 n))))).
Qed.

Lemma adjacent_nat_le : forall sequence,
    (forall n, (sequence n <= sequence (S n))%nat) ->
    forall n m, (n <= m)%nat -> (sequence n <= sequence m)%nat.
Proof.
  intros sequence Hstep n m Hle. induction Hle.
  - apply Nat.le_refl.
  - eapply Nat.le_trans; [exact IHHle|apply Hstep].
Qed.

Theorem nvec_monotone_subsequence : forall d (sequence : nat -> NVec d),
    exists indices,
      StrictlyIncreasing indices /\
      forall n, nvec_le (sequence (indices n)) (sequence (indices (S n))).
Proof.
  induction d as [|d IH]; intro sequence.
  - exists (fun n => n). split; [intro n; lia|].
    intros n index. inversion index.
  - destruct (nat_monotone_subsequence
      (fun n => Vector.hd (sequence n))) as [outer [Houter Hhead]].
    destruct (IH (fun n => Vector.tl (sequence (outer n)))) as
      [inner [Hinner Htail]].
    exists (fun n => outer (inner n)). split.
    + now apply strictly_increasing_compose.
    + intro n.
      rewrite (eta (sequence (outer (inner n)))),
        (eta (sequence (outer (inner (S n))))).
      intro index. refine (Fin.caseS' index (fun index => _) _ _).
      * cbn.
        apply adjacent_nat_le with (sequence := fun k =>
          Vector.hd (sequence (outer k))); [exact Hhead|].
        apply Nat.lt_le_incl, Hinner.
      * intro tail_index. cbn. exact (Htail n tail_index).
Qed.

Definition decoded_or {A} (codec : Codec A) (default : A) (code : nat) : A :=
  match decode codec code with
  | Some value => value
  | None => default
  end.

Lemma decoded_or_encode : forall A (codec : Codec A) default value,
    decoded_or codec default (encode codec value) = value.
Proof.
  intros. unfold decoded_or. now rewrite decode_encode.
Qed.

Lemma decidable_countable_sequence_choice : forall A (codec : Codec A)
    (default : A) (property : nat -> A -> Prop),
    (forall n value, {property n value} + {~ property n value}) ->
    (forall n, exists value, property n value) ->
    exists choice : nat -> A, forall n, property n (choice n).
Proof.
  intros A codec default property Hdec Hexists.
  set (code := fun n =>
    proj1_sig (constructive_indefinite_description_nat
      (fun code => property n (decoded_or codec default code))
      (fun code => Hdec n (decoded_or codec default code))
      (let (value, Hvalue) := Hexists n in
        ex_intro _ (encode codec value)
          (eq_rect value (property n) Hvalue
            (decoded_or codec default (encode codec value))
            (eq_sym (decoded_or_encode A codec default value)))))).
  exists (fun n => decoded_or codec default (code n)). intro n.
  unfold code.
  exact (proj2_sig (constructive_indefinite_description_nat
    (fun code => property n (decoded_or codec default code))
    (fun code => Hdec n (decoded_or codec default code))
    (let (value, Hvalue) := Hexists n in
      ex_intro _ (encode codec value)
        (eq_rect value (property n) Hvalue
          (decoded_or codec default (encode codec value))
          (eq_sym (decoded_or_encode A codec default value)))))).
Qed.

Definition FinitaryGeneratedRepresentation {d}
    (bases generators : list (ZVec d)) (value : ZVec d)
    (representation : nat * NVec (length generators)) : Prop :=
  match List.nth_error bases (fst representation) with
  | Some base =>
      value = zvec_add base
        (zvec_linear_combination generators
          (Vector.to_list (snd representation)))
  | None => False
  end.

Lemma finitary_generated_representation_dec : forall d bases generators
    (value : ZVec d) representation,
    {FinitaryGeneratedRepresentation bases generators value representation} +
    {~ FinitaryGeneratedRepresentation bases generators value representation}.
Proof.
  intros d bases generators value [position coefficients].
  unfold FinitaryGeneratedRepresentation; cbn.
  destruct (List.nth_error bases position) as [base|] eqn:Hbase.
  - apply zvec_eq_dec.
  - now right.
Defined.

Lemma finitary_generated_representation_exists : forall d
    (period set : ZSet d) bases generators (sequence : nat -> ZVec d),
    SameSet set
      (fun value => exists base increment,
        List.In base bases /\ period increment /\
        value = zvec_add base increment) ->
    (forall value, period value <-> zvec_generated generators value) ->
    (forall n, set (sequence n)) ->
    forall n, exists representation,
      FinitaryGeneratedRepresentation bases generators
        (sequence n) representation.
Proof.
  intros d period set bases generators sequence Hset Hperiod Hsequence n.
  apply (proj1 (Hset (sequence n))) in Hsequence.
  destruct Hsequence as [base [increment [Hbase [Hincrement Heq]]]].
  apply (proj1 (Hperiod increment)) in Hincrement.
  destruct Hincrement as [coefficients Hcoefficients].
  apply List.In_nth_error in Hbase.
  destruct Hbase as [position Hposition].
  exists (position, coefficients).
  unfold FinitaryGeneratedRepresentation; cbn. rewrite Hposition.
  rewrite <- Hcoefficients in Heq. exact Heq.
Qed.

Theorem finitary_generated_representation_sequence : forall d
    (period set : ZSet d),
    FinitelyGeneratedPeriodic period ->
    FinitaryQCylindric period set ->
    forall sequence : nat -> ZVec d,
      (forall n, set (sequence n)) ->
      exists bases generators representation,
        (forall value, period value <-> zvec_generated generators value) /\
        (forall n,
          FinitaryGeneratedRepresentation bases generators
            (sequence n) (representation n)).
Proof.
  intros d period set [generators [_ Hperiod]] [bases Hset]
    sequence Hsequence.
  assert (Hexists := finitary_generated_representation_exists d period set
    bases generators sequence Hset Hperiod Hsequence).
  destruct (decidable_countable_sequence_choice
      (nat * NVec (length generators))
      (pair_codec nat_codec (nvec_codec (length generators)))
      (0%nat, nvec_zero (length generators))
      (fun n representation => FinitaryGeneratedRepresentation
        bases generators (sequence n) representation)
      (fun n representation => finitary_generated_representation_dec
        d bases generators (sequence n) representation)
      Hexists) as [representation Hrepresentation].
  exists bases, generators, representation. auto.
Qed.

Lemma bounded_nat_sequence_infinite_value : forall bound sequence,
    (forall n, (sequence n < bound)%nat) ->
    exists value,
      (value < bound)%nat /\ InfiniteOften (fun n => sequence n = value).
Proof.
  induction bound as [|bound IH]; intros sequence Hbound.
  - exfalso. specialize (Hbound 0%nat). lia.
  - destruct (classic (InfiniteOften (fun n => sequence n = bound)))
      as [Hoften|Hfinite].
    + exists bound. split; [lia|exact Hoften].
    + destruct (not_infinite_often_eventually_not
        (fun n => sequence n = bound) Hfinite) as [N HN].
      assert (Htail : forall n, (sequence (N + n) < bound)%nat).
      { intro n. specialize (Hbound (N + n)%nat).
        specialize (HN (N + n)%nat ltac:(lia)). lia. }
      destruct (IH (fun n => sequence (N + n)%nat) Htail) as
        [value [Hvalue Hoften]].
      exists value. split; [lia|]. intros M.
      destruct (Hoften M) as [n [HMn Hn]].
      exists (N + n)%nat. split; [lia|exact Hn].
Qed.

Theorem bounded_nat_constant_subsequence : forall bound sequence,
    (forall n, (sequence n < bound)%nat) ->
    exists value indices,
      (value < bound)%nat /\
      StrictlyIncreasing indices /\
      forall n, sequence (indices n) = value.
Proof.
  intros bound sequence Hbound.
  destruct (bounded_nat_sequence_infinite_value bound sequence Hbound) as
    [value [Hvalue Hoften]].
  destruct (infinite_often_subsequence
      (fun n => sequence n = value)
      (fun n => Nat.eq_dec (sequence n) value) Hoften) as
    [indices [Hincreasing Heq]].
  exists value, indices. auto.
Qed.

Lemma representation_position_bound : forall d bases generators
    (value : ZVec d) representation,
    FinitaryGeneratedRepresentation bases generators value representation ->
    (fst representation < length bases)%nat.
Proof.
  intros d bases generators value [position coefficients] Hrepr.
  unfold FinitaryGeneratedRepresentation in Hrepr; cbn in *.
  destruct (List.nth_error bases position) eqn:Hnth; [|contradiction].
  apply (proj1 (List.nth_error_Some bases position)). congruence.
Qed.

Theorem finitary_qcylindric_monotone_subsequence :
  forall d (period set : ZSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FinitaryQCylindric period set ->
    forall sequence : nat -> ZVec d,
      (forall n, set (sequence n)) ->
      exists indices : nat -> nat,
        (forall n, (indices n < indices (S n))%nat) /\
        (forall n,
          PeriodicLe period
            (sequence (indices n))
            (sequence (indices (S n)))).
Proof.
  intros d period set _ Hfinite Hfinitary sequence Hsequence.
  destruct (finitary_generated_representation_sequence d period set
      Hfinite Hfinitary sequence Hsequence) as
    [bases [generators [representation [Hperiod Hrepresentation]]]].
  destruct (bounded_nat_constant_subsequence (length bases)
      (fun n => fst (representation n))) as
    [position [outer [_ [Houter Hposition]]]].
  { intro n. apply representation_position_bound with
      (generators := generators) (value := sequence n).
    apply Hrepresentation. }
  destruct (nvec_monotone_subsequence (length generators)
      (fun n => snd (representation (outer n)))) as
    [inner [Hinner Hcoefficients]].
  exists (fun n => outer (inner n)). split.
  - now apply strictly_increasing_compose.
  - intro n.
    specialize (Hrepresentation (outer (inner n))) as Hleft.
    specialize (Hrepresentation (outer (inner (S n)))) as Hright.
    unfold FinitaryGeneratedRepresentation in Hleft, Hright.
    rewrite (Hposition (inner n)) in Hleft.
    rewrite (Hposition (inner (S n))) in Hright.
    destruct (List.nth_error bases position) as [base|] eqn:Hbase;
      [|contradiction].
    unfold PeriodicLe. rewrite Hleft, Hright.
    rewrite (zvec_add_comm d base), (zvec_add_comm d base), zvec_sub_add.
    apply (proj2 (Hperiod _)).
    exists (nvec_sub_local
      (snd (representation (outer (inner (S n)))))
      (snd (representation (outer (inner n))))).
    symmetry. apply linear_combination_sub. exact (Hcoefficients n).
Qed.

Lemma zvec_sub_transitive_sum : forall d (x y z : ZVec d),
    zvec_add (zvec_sub y x) (zvec_sub z y) = zvec_sub z x.
Proof.
  intros d x y z. apply zvec_ext. intro index.
  unfold zvec_add, zvec_sub.
  repeat rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl). lia.
Qed.

Lemma periodic_le_trans : forall d (period : ZSet d),
    Periodic period -> forall x y z,
    PeriodicLe period x y -> PeriodicLe period y z ->
    PeriodicLe period x z.
Proof.
  intros d period [_ Hadd] x y z Hxy Hyz.
  unfold PeriodicLe in *.
  rewrite <- (zvec_sub_transitive_sum d x y z).
  now apply Hadd.
Qed.

Theorem periodic_le_sequence : forall d (period : ZSet d),
    Periodic period -> forall sequence : nat -> ZVec d,
    (forall n, PeriodicLe period (sequence n) (sequence (S n))) ->
    forall n m, (n <= m)%nat ->
      PeriodicLe period (sequence n) (sequence m).
Proof.
  intros d period Hperiod sequence Hstep n m Hnm. induction Hnm.
  - unfold PeriodicLe. replace (zvec_sub (sequence n) (sequence n))
      with (zvec_zero d).
    + exact (proj1 Hperiod).
    + apply zvec_ext. intro index. unfold zvec_sub, zvec_zero.
      rewrite (nth_map2 _ _ _ index index index eq_refl eq_refl),
        (const_nth Z 0 d index). lia.
  - eapply periodic_le_trans; [exact Hperiod|exact IHHnm|apply Hstep].
Qed.

Theorem eventually_constant_strict_subsequence : forall sequence indices,
    EventuallyConstantIntegerSequence sequence ->
    StrictlyIncreasing indices ->
    EventuallyConstantIntegerSequence (fun n => sequence (indices n)).
Proof.
  intros sequence indices [N Hconstant] Hincreasing.
  destruct (strictly_increasing_unbounded indices Hincreasing N) as [K HK].
  exists K. intros n HKn.
  rewrite (Hconstant (indices n)), (Hconstant (indices K)); [reflexivity| |].
  - exact HK.
  - eapply Nat.le_trans; [exact HK|].
    now apply strictly_increasing_le.
Qed.

Theorem tail_unbounded_strict_subsequence : forall sequence indices,
    (forall n, (sequence n <= sequence (S n))%Z) ->
    TailUnboundedIntegerSequence sequence ->
    StrictlyIncreasing indices ->
    TailUnboundedIntegerSequence (fun n => sequence (indices n)).
Proof.
  intros sequence indices Hmonotone Hunbounded Hincreasing bound N.
  destruct (Hunbounded bound (indices N)) as [position [HNposition Hbound]].
  destruct (strictly_increasing_unbounded indices Hincreasing position) as
    [candidate Hcandidate].
  exists (Nat.max N candidate). split; [apply Nat.le_max_l|].
  assert (Hposition : (position <= indices (Nat.max N candidate))%nat).
  { eapply Nat.le_trans; [exact Hcandidate|].
    apply strictly_increasing_le; [exact Hincreasing|apply Nat.le_max_r]. }
  eapply Z.le_trans; [exact Hbound|].
  now apply monotone_integer_le.
Qed.

Definition tail_reindex {A : Type} (sequence : nat -> A) (start : nat) :
    nat -> A := fun n => sequence (start + n)%nat.

Lemma tail_reindex_strict : forall start,
    StrictlyIncreasing (fun n => (start + n)%nat).
Proof. intros start n. lia. Qed.

Theorem finite_supporting_normals_tail_reindex : forall d
    (period : ZSet d) (normals : list (ZVec d))
    (sequence : nat -> ZVec d),
    List.Forall
      (fun normal =>
        SupportingNormal (Cone period) (zvec_to_qvec normal)) normals ->
    (forall n, PeriodicLe period (sequence n) (sequence (S n))) ->
    exists unbounded constant N,
      (forall normal,
        List.In normal unbounded <->
        List.In normal normals /\ NormalTailUnbounded sequence normal) /\
      (forall normal,
        List.In normal constant <->
        List.In normal normals /\ NormalEventuallyConstant sequence normal) /\
      (forall normal,
        List.In normal constant -> forall n,
          zinner normal (tail_reindex sequence N n) =
          zinner normal (tail_reindex sequence N 0)) /\
      (forall normal,
        List.In normal unbounded ->
        NormalTailUnbounded (tail_reindex sequence N) normal) /\
      (forall normal,
        List.In normal normals -> forall n,
          (zinner normal (tail_reindex sequence N n) <=
           zinner normal (tail_reindex sequence N (S n)))%Z).
Proof.
  intros d period normals sequence Hsupport Hsequence.
  destruct (finite_supporting_normals_tail_classification d period normals
      sequence Hsupport Hsequence) as
    [unbounded [constant [N [Hunbounded [Hconstant Hcommon]]]]].
  exists unbounded, constant, N. split; [exact Hunbounded|].
  split; [exact Hconstant|]. split.
  - intros normal Hin n. unfold tail_reindex.
    transitivity (zinner normal (sequence N)).
    + apply Hcommon; [exact Hin|lia].
    + symmetry. apply Hcommon; [exact Hin|lia].
  - split.
    + intros normal Hin bound M.
      apply Hunbounded in Hin as [_ Htail].
      destruct (Htail bound (N + M)%nat) as [position [Hposition Hbound]].
      exists (position - N)%nat. split; [lia|].
      unfold tail_reindex. replace (N + (position - N))%nat with position
        by lia. exact Hbound.
    + intros normal Hin n. unfold tail_reindex.
      apply supporting_normal_monotone with (period := period).
      * apply (proj1 (List.Forall_forall _ _) Hsupport normal Hin).
      * replace (N + S n)%nat with (S (N + n)) by lia. apply Hsequence.
Qed.
