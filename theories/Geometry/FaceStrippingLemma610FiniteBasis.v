From Coq Require Import Arith.Cantor Bool Classical_Prop Lia List
  Logic.ConstructiveEpsilon Vector VectorSpec ZArith.
From Mell.Core Require Import Code Vector.
From Mell.BVAS Require Import Code RunOrder.
From Mell.Geometry Require Import ClosedLinearization Cone FaceStrippingExtract
  FaceStrippingFinitary FaceStrippingLemma610 FaceStrippingMonotoneSubsequence
  FaceStrippingOrderFoundation Faces Periodic RationalDefinability.
From Mell.Order Require Import PeriodicOrder.
From Mell.Presburger Require Import Decide Semantics Syntax.
From Mell.Semilinear Require Import Formula.

Import ListNotations.
Open Scope Z_scope.

Definition zvec_entry {d} (value : ZVec d) (coordinate : nat) : Z :=
  List.nth coordinate (Vector.to_list value) 0%Z.

Lemma zvec_entry_nth_order : forall d (value : ZVec d) coordinate
    (Hcoordinate : (coordinate < d)%nat),
    zvec_entry value coordinate = Vector.nth_order value Hcoordinate.
Proof.
  intros. unfold zvec_entry. symmetry. apply to_list_nth_order.
Qed.

Lemma zvec_entry_nth : forall d (value : ZVec d) (index : Fin.t d),
    zvec_entry value (proj1_sig (Fin.to_nat index)) = Vector.nth value index.
Proof.
  intros d value index. unfold zvec_entry.
  rewrite <- to_list_nth_order with
    (H := proj2_sig (Fin.to_nat index)) (d := 0%Z).
  unfold Vector.nth_order. now rewrite Fin.of_nat_to_nat_inv.
Qed.

Lemma zvec_entry_add : forall d (left right : ZVec d) coordinate,
    (coordinate < d)%nat ->
    zvec_entry (zvec_add left right) coordinate =
      zvec_entry left coordinate + zvec_entry right coordinate.
Proof.
  intros d left right coordinate Hcoordinate.
  repeat rewrite zvec_entry_nth_order with (Hcoordinate := Hcoordinate).
  unfold zvec_add, Vector.nth_order.
  apply Vector.nth_map2; reflexivity.
Qed.

Lemma zvec_entry_nsmul : forall d coefficient (value : ZVec d) coordinate,
    (coordinate < d)%nat ->
    zvec_entry (zvec_nsmul coefficient value) coordinate =
      Z.of_nat coefficient * zvec_entry value coordinate.
Proof.
  intros d coefficient value coordinate Hcoordinate.
  repeat rewrite zvec_entry_nth_order with (Hcoordinate := Hcoordinate).
  unfold Vector.nth_order. apply nth_zvec_nsmul.
Qed.

Lemma zvec_entry_zero : forall d coordinate,
    (coordinate < d)%nat -> zvec_entry (zvec_zero d) coordinate = 0.
Proof.
  intros d coordinate Hcoordinate.
  rewrite zvec_entry_nth_order with (Hcoordinate := Hcoordinate).
  unfold zvec_zero, Vector.nth_order. apply Vector.const_nth.
Qed.

Fixpoint zcoefficient_sum {d} (coordinate : nat)
    (coefficients : list nat) (generators : list (ZVec d)) : Z :=
  match coefficients, generators with
  | coefficient :: coefficients', generator :: generators' =>
      Z.of_nat coefficient * zvec_entry generator coordinate +
        zcoefficient_sum coordinate coefficients' generators'
  | _, _ => 0
  end.

Lemma zvec_entry_linear_combination : forall d coordinate
    (generators : list (ZVec d)) coefficients,
    (coordinate < d)%nat ->
    length coefficients = length generators ->
    zvec_entry (zvec_linear_combination generators coefficients) coordinate =
      zcoefficient_sum coordinate coefficients generators.
Proof.
  intros d coordinate generators. induction generators as [|generator generators IH];
    intros coefficients Hcoordinate Hlength;
    destruct coefficients as [|coefficient coefficients];
    simpl in Hlength; try discriminate; cbn [zvec_linear_combination
      zcoefficient_sum].
  - now apply zvec_entry_zero.
  - injection Hlength as Hlength.
    rewrite zvec_entry_add by exact Hcoordinate.
    rewrite zvec_entry_nsmul by exact Hcoordinate.
    rewrite IH by assumption. reflexivity.
Qed.

Fixpoint zperiod_sum {d} (coordinate coefficient_index : nat)
    (generators : list (ZVec d)) : Syntax.term :=
  match generators with
  | [] => Syntax.Num 0
  | generator :: generators' =>
      Syntax.Plus
        (Syntax.Scale (zvec_entry generator coordinate)
          (Syntax.Var (coefficient_index + length generators')%nat))
        (zperiod_sum coordinate coefficient_index generators')
  end.

Definition zgenerated_body {d} (generators : list (ZVec d))
    (value : ZVec d) : Syntax.formula :=
  formula_and
    (List.map (fun index => Syntax.Le (Syntax.Num 0) (Syntax.Var index))
       (seq 0 (length generators)) ++
     List.map (fun coordinate =>
       Syntax.Eq (zperiod_sum coordinate 0 generators)
         (Syntax.Num (zvec_entry value coordinate)))
       (seq 0 d)).

Definition zgenerated_formula {d} (generators : list (ZVec d))
    (value : ZVec d) : Syntax.formula :=
  exists_many (length generators) (zgenerated_body generators value).

Lemma zperiod_sum_closed : forall d coordinate start
    (generators : list (ZVec d)),
    Syntax.term_closed (start + length generators)
      (zperiod_sum coordinate start generators) = true.
Proof.
  intros d coordinate start generators.
  induction generators as [|generator generators IH]; simpl.
  - reflexivity.
  - apply Bool.andb_true_iff. split.
    + apply Nat.ltb_lt. lia.
    + eapply term_closed_monotone; [exact IH|lia].
Qed.

Lemma zgenerated_formula_closed : forall d generators (value : ZVec d),
    Syntax.formula_closed 0 (zgenerated_formula generators value) = true.
Proof.
  intros d generators value. unfold zgenerated_formula.
  apply exists_many_closed. unfold zgenerated_body.
  apply formula_and_closed, List.Forall_app. split.
  - apply List.Forall_forall. intros formula Hin.
    apply in_map_iff in Hin as [index [<- Hin]]. simpl.
    apply in_seq in Hin. apply Nat.ltb_lt. lia.
  - apply List.Forall_forall. intros formula Hin.
    apply in_map_iff in Hin as [coordinate [<- Hin]]. simpl.
    apply Bool.andb_true_iff. split; [|reflexivity].
    eapply term_closed_monotone; [apply zperiod_sum_closed|lia].
Qed.

Lemma zperiod_sum_semantics : forall d coordinate
    (generators : list (ZVec d)) env values,
    length values = length generators ->
    (forall value, List.In value values -> 0 <= value) ->
    term_semantics (extend_many env values)
      (zperiod_sum coordinate 0 generators) =
    zcoefficient_sum coordinate (List.map Z.to_nat values) generators.
Proof.
  intros d coordinate generators. induction generators as [|generator generators IH];
    intros env values Hlength Hnonnegative;
    destruct values as [|value values]; simpl in Hlength; try discriminate; simpl.
  - reflexivity.
  - replace (length generators) with (length values) by lia.
    replace (length values) with (length values + 0)%nat by lia.
    rewrite extend_many_tail_lookup. simpl.
    rewrite Z2Nat.id by (apply Hnonnegative; now left).
    rewrite IH with (values := values); [ring|lia|].
    intros item Hin. apply Hnonnegative. now right.
Qed.

Lemma zgenerated_formula_correct : forall d generators (value : ZVec d),
    formula_semantics empty_environment (zgenerated_formula generators value) <->
    zvec_generated generators value.
Proof.
  intros d generators value. unfold zgenerated_formula.
  rewrite exists_many_semantics. split.
  - intros [values [Hlength Hbody]]. unfold zgenerated_body in Hbody.
    apply formula_and_semantics in Hbody.
    apply List.Forall_app in Hbody as [Hnonnegative Hequations].
    pose proof (proj1 (nonnegative_formulas_correct (length generators)
      (extend_many empty_environment values)) Hnonnegative) as Hnonnegative_at.
    assert (Hvalues_nonnegative : forall item,
        List.In item values -> 0 <= item).
    { intros item Hin. apply In_nth_error in Hin as [index Hindex].
      assert (Hindex_lt : (index < length values)%nat).
      { apply nth_error_Some. rewrite Hindex. discriminate. }
      specialize (Hnonnegative_at (length values - S index)%nat ltac:(lia)).
      rewrite extend_many_lookup in Hnonnegative_at by lia.
      replace (length values - S (length values - S index))%nat with index
        in Hnonnegative_at by lia.
      rewrite (@nth_error_nth Z values index item 0 Hindex)
        in Hnonnegative_at. exact Hnonnegative_at. }
    set (coefficients := List.map Z.to_nat values).
    assert (Hcoefficients_length : length coefficients = length generators).
    { unfold coefficients. now rewrite length_map. }
    unfold zvec_generated. rewrite <- Hcoefficients_length.
    exists (Vector.of_list coefficients). rewrite to_list_of_list_opp.
    apply zvec_ext. intro index.
    set (coordinate := proj1_sig (Fin.to_nat index)).
    pose proof (proj2_sig (Fin.to_nat index)) as Hindex.
    repeat rewrite <- zvec_entry_nth.
    assert (Hequation : formula_semantics (extend_many empty_environment values)
        (Syntax.Eq (zperiod_sum coordinate 0 generators)
          (Syntax.Num (zvec_entry value coordinate)))).
    { apply (proj1 (List.Forall_forall _ _) Hequations).
      apply in_map_iff. exists coordinate. split; [reflexivity|].
      apply in_seq. split; [lia|]. unfold coordinate. exact Hindex. }
    cbn in Hequation.
    rewrite zperiod_sum_semantics in Hequation by assumption.
    unfold coefficients.
    rewrite zvec_entry_linear_combination by assumption. exact Hequation.
  - intros [coefficients Hgenerated].
    exists (List.map Z.of_nat (Vector.to_list coefficients)). split.
    + rewrite length_map, length_to_list. reflexivity.
    + unfold zgenerated_body. apply formula_and_semantics, List.Forall_app.
      split.
      * apply nonnegative_formulas_correct. intros index Hindex.
        rewrite extend_many_lookup by (rewrite length_map, length_to_list; lia).
        rewrite length_map, length_to_list.
        rewrite map_nth with (d := 0%nat). apply Nat2Z.is_nonneg.
      * apply List.Forall_forall. intros formula Hin.
        apply in_map_iff in Hin as [coordinate [<- Hin]].
        apply in_seq in Hin. cbn.
        rewrite zperiod_sum_semantics.
        -- rewrite List.map_map.
           replace (List.map (fun x => Z.to_nat (Z.of_nat x))
             (Vector.to_list coefficients))
             with (Vector.to_list coefficients).
           2: { symmetry. rewrite <- List.map_id. apply List.map_ext.
                intros. apply Nat2Z.id. }
           rewrite <- zvec_entry_linear_combination.
           ++ now rewrite Hgenerated.
           ++ lia.
           ++ apply length_to_list.
        -- rewrite length_map, length_to_list. reflexivity.
        -- intros item Hitem. apply in_map_iff in Hitem as [natural [<- _]].
           apply Nat2Z.is_nonneg.
Qed.

Definition zgenerated_sentence {d} (generators : list (ZVec d))
    (value : ZVec d) : Syntax.sentence :=
  Syntax.close_sentence (zgenerated_formula generators value)
    (zgenerated_formula_closed d generators value).

Definition zvec_generated_dec_explicit {d}
    (generators : list (ZVec d)) (value : ZVec d) :
    {zvec_generated generators value} + {~ zvec_generated generators value}.
Proof.
  destruct (presburger_decide (zgenerated_sentence generators value))
    eqn:Hdecision.
  - left. apply (proj1 (zgenerated_formula_correct d generators value)).
    change (sentence_semantics (zgenerated_sentence generators value)).
    apply (proj1 (presburger_decide_correct _)). exact Hdecision.
  - right. intro Hgenerated.
    apply (proj2 (zgenerated_formula_correct d generators value)) in Hgenerated.
    change (sentence_semantics (zgenerated_sentence generators value))
      in Hgenerated.
    apply (proj2 (presburger_decide_correct _)) in Hgenerated.
    rewrite Hdecision in Hgenerated. discriminate.
Defined.

Definition FinitelyPresented {d} (generators bases : list (ZVec d))
    (value : ZVec d) : Prop :=
  exists base,
    List.In base bases /\ zvec_generated generators (zvec_sub value base).

Fixpoint finitary_presentation_dec_explicit {d}
    (generators bases : list (ZVec d)) (value : ZVec d) :
    {FinitelyPresented generators bases value} +
    {~ FinitelyPresented generators bases value}.
Proof.
  destruct bases as [|base bases].
  - right. intros [candidate [Hin _]]. contradiction.
  - destruct (zvec_generated_dec_explicit generators (zvec_sub value base))
      as [Hhead|Hhead].
    + left. exists base. now split; [left|].
    + destruct (finitary_presentation_dec_explicit d generators bases value)
        as [Htail|Htail].
      * left. destruct Htail as [candidate [Hin Hgenerated]].
        exists candidate. now split; [right|].
      * right. intros [candidate [[<-|Hin] Hgenerated]].
        -- contradiction.
        -- apply Htail. exists candidate. tauto.
Defined.

Lemma finitely_presented_spec : forall d generators bases (value : ZVec d),
    FinitelyPresented generators bases value <->
    exists base increment,
      List.In base bases /\ zvec_generated generators increment /\
      value = zvec_add base increment.
Proof.
  intros d generators bases value. split.
  - intros [base [Hbase Hgenerated]].
    exists base, (zvec_sub value base). repeat split; try assumption.
    symmetry. apply zvec_sub_add_cancel.
  - intros [base [increment [Hbase [Hgenerated ->]]]].
    exists base. split; [exact Hbase|].
    replace (zvec_sub (zvec_add base increment) base) with increment;
      [exact Hgenerated|].
    apply zvec_ext. intro index. unfold zvec_sub, zvec_add.
    repeat rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl).
    ring.
Qed.

Definition zvec_generated_difference_dec_explicit {d}
    (generators : list (ZVec d)) (left right : ZVec d) :
    {zvec_generated generators (zvec_sub right left)} +
    {~ zvec_generated generators (zvec_sub right left)} :=
  zvec_generated_dec_explicit generators (zvec_sub right left).

Theorem extract_face_cylindric_characterization : forall d
    (period excluded remaining : ZSet d) (face : QSet d),
    Periodic (FacePeriod period face) ->
    QCylindric period remaining ->
    forall value,
      ExtractFace period face excluded remaining value <->
      remaining value /\
      ~ (exists increment,
          FacePeriod period face increment /\
          excluded (zvec_add value increment)).
Proof.
  intros d period excluded remaining face Hface_periodic Hremaining value.
  split.
  - intro Hextract. split.
    + specialize (Hextract (zvec_zero d) (proj1 Hface_periodic)).
      now rewrite zvec_add_zero_right in Hextract.
    + intros [increment [Hincrement Hexcluded]].
      exact (proj2 (Hextract increment Hincrement) Hexcluded).
  - intros [Hvalue Havoids] increment Hincrement. split.
    + apply Hremaining; [exact Hvalue|exact (proj1 Hincrement)].
    + intro Hexcluded. apply Havoids. now exists increment.
Qed.

Lemma zvec_generated_app_decompose : forall d
    (left right : list (ZVec d)) value,
    zvec_generated (left ++ right) value <->
    exists left_value right_value,
      zvec_generated left left_value /\
      zvec_generated right right_value /\
      value = zvec_add left_value right_value.
Proof.
  intros d left right value. split.
  - intros [coefficients Hvalue].
    set (all := Vector.to_list coefficients).
    set (left_coefficients := firstn (length left) all).
    set (right_coefficients := skipn (length left) all).
    assert (Hall : length all = (length left + length right)%nat).
    { unfold all. rewrite length_to_list, length_app. reflexivity. }
    assert (Hleft : length left_coefficients = length left).
    { unfold left_coefficients. rewrite length_firstn. lia. }
    assert (Hright : length right_coefficients = length right).
    { unfold right_coefficients. rewrite length_skipn. lia. }
    exists (zvec_linear_combination left left_coefficients),
      (zvec_linear_combination right right_coefficients).
    repeat split.
    + unfold zvec_generated. rewrite <- Hleft.
      exists (Vector.of_list left_coefficients). now rewrite to_list_of_list_opp.
    + unfold zvec_generated. rewrite <- Hright.
      exists (Vector.of_list right_coefficients). now rewrite to_list_of_list_opp.
    + rewrite <- Hvalue. unfold all, left_coefficients, right_coefficients.
      rewrite <- firstn_skipn with (n := length left)
        (l := Vector.to_list coefficients) at 1.
      apply linear_combination_app; assumption.
  - intros [left_value [right_value [Hleft [Hright ->]]]].
    apply generated_add.
    + now apply generated_append_left.
    + now apply generated_append_right.
Qed.

Lemma zvec_linear_combination_map_opp : forall d generators coefficients,
    length coefficients = length generators ->
    zvec_linear_combination (List.map (@zvec_opp d) generators) coefficients =
      zvec_opp (zvec_linear_combination generators coefficients).
Proof.
  intros d generators. induction generators as [|generator generators IH];
    intros coefficients Hlength; destruct coefficients as [|coefficient coefficients];
    simpl in Hlength; try discriminate; cbn [zvec_linear_combination List.map].
  - apply zvec_ext. intro index. unfold zvec_opp, zvec_zero.
    rewrite (Vector.nth_map _ _ index index eq_refl), !Vector.const_nth. lia.
  - injection Hlength as Hlength. specialize (IH coefficients Hlength).
    apply zvec_ext. intro index.
    apply (f_equal (fun vector => Vector.nth vector index)) in IH.
    unfold zvec_add, zvec_opp in *.
    repeat first
      [rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl)
      |rewrite (Vector.nth_map _ _ index index eq_refl)
      |rewrite (nth_zvec_nsmul d coefficient _ index)].
    rewrite IH.
    repeat first
      [rewrite (Vector.nth_map2 _ _ _ index index index eq_refl eq_refl)
      |rewrite (Vector.nth_map _ _ index index eq_refl)
      |rewrite (nth_zvec_nsmul d coefficient _ index)].
    lia.
Qed.

Lemma zvec_generated_map_opp : forall d generators value,
    zvec_generated generators value ->
    zvec_generated (List.map (@zvec_opp d) generators) (zvec_opp value).
Proof.
  intros d generators value [coefficients Hvalue].
  unfold zvec_generated. rewrite length_map. exists coefficients.
  rewrite zvec_linear_combination_map_opp;
    [now rewrite Hvalue|apply length_to_list].
Qed.

Definition ExtractCollisionPresented {d}
    (period_generators face_generators excluded_bases : list (ZVec d))
    (value : ZVec d) : Prop :=
  FinitelyPresented
    (period_generators ++ List.map (@zvec_opp d) face_generators)
    excluded_bases value.

Lemma extract_collision_presented_spec : forall d
    period_generators face_generators excluded_bases (value : ZVec d),
    ExtractCollisionPresented period_generators face_generators
      excluded_bases value <->
    exists increment,
      zvec_generated face_generators increment /\
      FinitelyPresented period_generators excluded_bases
        (zvec_add value increment).
Proof.
  intros d period_generators face_generators excluded_bases value.
  unfold ExtractCollisionPresented. split.
  - intros [base [Hbase Hcombined]].
    apply zvec_generated_app_decompose in Hcombined.
    destruct Hcombined as [period_part [negative_part
      [Hperiod [Hnegative Hdifference]]]].
    destruct Hnegative as [coefficients Hnegative].
    set (increment := zvec_linear_combination face_generators
      (Vector.to_list coefficients)).
    assert (Hcoefficient_length :
        length (Vector.to_list coefficients) = length face_generators).
    { rewrite length_to_list, length_map. reflexivity. }
    assert (Hnegative_eq : negative_part = zvec_opp increment).
    { unfold increment. rewrite <- zvec_linear_combination_map_opp
        by exact Hcoefficient_length. symmetry. exact Hnegative. }
    exists increment. split.
    + unfold zvec_generated. rewrite <- Hcoefficient_length.
      exists (Vector.of_list (Vector.to_list coefficients)).
      now rewrite to_list_of_list_opp.
    + exists base. split; [exact Hbase|].
      replace (zvec_sub (zvec_add value increment) base) with period_part;
        [exact Hperiod|].
      rewrite Hnegative_eq in Hdifference.
      apply zvec_ext. intro index.
      apply (f_equal (fun vector => Vector.nth vector index)) in Hdifference.
      unfold zvec_sub, zvec_add, zvec_opp in *.
      repeat rewrite (Vector.nth_map2 _ _ _ index index index
        eq_refl eq_refl) in *.
      repeat rewrite (Vector.nth_map _ _ index index eq_refl) in *.
      lia.
  - intros [increment [Hface [base [Hbase Hperiod]]]].
    exists base. split; [exact Hbase|].
    apply zvec_generated_app_decompose.
    exists (zvec_sub (zvec_add value increment) base), (zvec_opp increment).
    repeat split; try assumption.
    + now apply zvec_generated_map_opp.
    + apply zvec_ext. intro index. unfold zvec_sub, zvec_add, zvec_opp.
      repeat rewrite (Vector.nth_map2 _ _ _ index index index
        eq_refl eq_refl).
      repeat rewrite (Vector.nth_map _ _ index index eq_refl). lia.
Qed.

Definition face_periodic_le_dec_explicit {d} (face_period : ZSet d)
    (face_generators : list (ZVec d))
    (Hface : forall value,
      face_period value <-> zvec_generated face_generators value)
    (left right : ZVec d) :
    {PeriodicLe face_period left right} +
    {~ PeriodicLe face_period left right}.
Proof.
  destruct (zvec_generated_dec_explicit face_generators
    (zvec_sub right left)) as [Hgenerated|Hgenerated].
  - left. unfold PeriodicLe. now apply (proj2 (Hface _)).
  - right. unfold PeriodicLe. intro Hperiod.
    apply Hgenerated. now apply (proj1 (Hface _)).
Defined.

Definition extract_face_dec_explicit {d}
    (period excluded remaining : ZSet d) (face : QSet d)
    (period_generators face_generators
      excluded_bases remaining_bases : list (ZVec d))
    (Hface_periodic : Periodic (FacePeriod period face))
    (Hremaining_cylindric : QCylindric period remaining)
    (Hperiod : forall value,
      period value <-> zvec_generated period_generators value)
    (Hface : forall value,
      FacePeriod period face value <->
        zvec_generated face_generators value)
    (Hexcluded : forall value,
      excluded value <->
        FinitelyPresented period_generators excluded_bases value)
    (Hremaining : forall value,
      remaining value <->
        FinitelyPresented period_generators remaining_bases value)
    (value : ZVec d) :
    {ExtractFace period face excluded remaining value} +
    {~ ExtractFace period face excluded remaining value}.
Proof.
  destruct (finitary_presentation_dec_explicit period_generators
    remaining_bases value) as [Hvalue|Hvalue].
  - destruct (finitary_presentation_dec_explicit
      (period_generators ++ List.map (@zvec_opp d) face_generators)
      excluded_bases value) as [Hcollision|Hcollision].
    + right. intro Hextract.
      apply (proj1 (extract_face_cylindric_characterization d period excluded
        remaining face Hface_periodic Hremaining_cylindric value)) in Hextract.
      destruct Hextract as [_ Havoids]. apply Havoids.
      apply (proj1 (extract_collision_presented_spec d period_generators
        face_generators excluded_bases value)) in Hcollision.
      destruct Hcollision as [increment [Hincrement Hexcluded_value]].
      exists increment. split.
      * now apply (proj2 (Hface _)).
      * apply (proj2 (Hexcluded _)). exact Hexcluded_value.
    + left. apply (proj2 (extract_face_cylindric_characterization d period
        excluded remaining face Hface_periodic Hremaining_cylindric value)).
      split.
      * now apply (proj2 (Hremaining _)).
      * intros [increment [Hincrement Hexcluded_value]]. apply Hcollision.
        apply (proj2 (extract_collision_presented_spec d period_generators
          face_generators excluded_bases value)).
        exists increment. split.
        -- now apply (proj1 (Hface _)).
        -- now apply (proj1 (Hexcluded _)).
  - right. intro Hextract. apply Hvalue.
    apply (proj1 (Hremaining _)).
    exact (proj1 (proj1 (extract_face_cylindric_characterization d period
      excluded remaining face Hface_periodic Hremaining_cylindric value)
      Hextract)).
Defined.

(** The signed-coordinate codec and the recursive fixed-vector codec avoid
    dependent equality casts: vector length is consumed structurally by the
    decoder. *)
Definition z_codec_pair (value : Z) : nat * nat :=
  match value with
  | Z0 => (0%nat, 0%nat)
  | Zpos positive => (1%nat, Pos.to_nat positive)
  | Zneg positive => (2%nat, Pos.to_nat positive)
  end.

Definition z_codec_unpair (code : nat * nat) : Z :=
  match code with
  | (1%nat, magnitude) => Z.of_nat magnitude
  | (2%nat, magnitude) => Z.opp (Z.of_nat magnitude)
  | _ => 0
  end.

Lemma z_codec_pair_cancel : forall value,
    z_codec_unpair (z_codec_pair value) = value.
Proof.
  intros [|positive|positive]; cbn; [reflexivity| |].
  - apply positive_nat_Z.
  - now rewrite positive_nat_Z.
Qed.

Definition z_codec : Codec Z.
Proof.
  refine {| encode := fun value =>
      encode (pair_codec nat_codec nat_codec) (z_codec_pair value);
    decode := fun code =>
      match decode (pair_codec nat_codec nat_codec) code with
      | Some value => Some (z_codec_unpair value)
      | None => None
      end |}.
  intro value. rewrite decode_encode. now rewrite z_codec_pair_cancel.
Defined.

Fixpoint encode_zvec {d} (value : ZVec d) : nat :=
  match value with
  | Vector.nil => 0%nat
  | Vector.cons head tail_length tail =>
      S (Cantor.to_nat (encode z_codec head, encode_zvec tail))
  end.

Fixpoint decode_zvec (d : nat) (code : nat) : option (ZVec d) :=
  match d, code with
  | O, O => Some (@Vector.nil Z)
  | O, S _ => None
  | S d', O => None
  | S d', S packed =>
      let '(head_code, tail_code) := Cantor.of_nat packed in
      match decode z_codec head_code, decode_zvec d' tail_code with
      | Some head, Some tail => Some (@Vector.cons Z head d' tail)
      | _, _ => None
      end
  end.

Lemma decode_zvec_encode : forall d (value : ZVec d),
    decode_zvec d (encode_zvec value) = Some value.
Proof.
  intros d value. induction value as [|head d tail IH].
  - reflexivity.
  - change (decode_zvec (S d)
      (S (Cantor.to_nat (encode z_codec head, encode_zvec tail))) =
      Some (@Vector.cons Z head d tail)).
    cbn [decode_zvec].
    rewrite Cantor.cancel_of_to, decode_encode, IH. reflexivity.
Qed.

Definition zvec_codec (d : nat) : Codec (ZVec d) :=
  {| encode := @encode_zvec d;
     decode := decode_zvec d;
     decode_encode := decode_zvec_encode d |}.

Section DecidableMonotoneFiniteCover.

Context {X : Type}.
Variable codec : Codec X.
Variable predicate : X -> Prop.
Variable relation : X -> X -> Prop.
Variable predicate_dec : forall value, {predicate value} + {~ predicate value}.
Variable relation_dec : forall left right,
    {relation left right} + {~ relation left right}.

Definition decoded_predicate_value (code : nat) : option X :=
  match decode codec code with
  | Some value => if predicate_dec value then Some value else None
  | None => None
  end.

Definition avoids_prefix (basis : list {value : X | predicate value})
    (candidate : X) : Prop :=
  forall base, List.In base basis ->
    ~ relation (proj1_sig base) candidate.

Fixpoint avoids_prefixb (basis : list {value : X | predicate value})
    (candidate : X) : bool :=
  match basis with
  | [] => true
  | base :: tail =>
      if relation_dec (proj1_sig base) candidate
      then false
      else avoids_prefixb tail candidate
  end.

Lemma avoids_prefixb_true_iff : forall basis candidate,
    avoids_prefixb basis candidate = true <->
    avoids_prefix basis candidate.
Proof.
  intros basis candidate. induction basis as [|base tail IH]; cbn.
  - split; [intros _ element Hin; contradiction|reflexivity].
  - destruct (relation_dec (proj1_sig base) candidate) as [Hrel|Hrel].
    + split; [discriminate|].
      intro Havoid. exfalso.
      exact (Havoid base (or_introl eq_refl) Hrel).
    + rewrite IH. split.
      * intros Htail element [<-|Hin]; [exact Hrel|now apply Htail].
      * intro Hall. intros element Hin. apply Hall. now right.
Qed.

Definition escaping_code
    (basis : list {value : X | predicate value}) (code : nat) : Prop :=
  match decoded_predicate_value code with
  | Some candidate => avoids_prefix basis candidate
  | None => False
  end.

Definition escaping_code_dec
    (basis : list {value : X | predicate value}) (code : nat) :
    {escaping_code basis code} + {~ escaping_code basis code}.
Proof.
  unfold escaping_code.
  destruct (decoded_predicate_value code) as [candidate|] eqn:Hdecode.
  - destruct (avoids_prefixb basis candidate) eqn:Havoid.
    + left. now apply avoids_prefixb_true_iff.
    + right. intro H. apply avoids_prefixb_true_iff in H. congruence.
  - right. tauto.
Defined.

Lemma decoded_predicate_value_sound : forall code value,
    decoded_predicate_value code = Some value -> predicate value.
Proof.
  intros code value. unfold decoded_predicate_value.
  destruct (decode codec code) as [candidate|] eqn:Hdecode; [|discriminate].
  destruct (predicate_dec candidate) as [Hcandidate|Hcandidate];
    intro Heq; try discriminate. now injection Heq as <-.
Qed.

Lemma decoded_predicate_value_complete : forall value,
    predicate value -> exists code,
      decoded_predicate_value code = Some value.
Proof.
  intros value Hvalue. exists (encode codec value).
  unfold decoded_predicate_value. rewrite decode_encode.
  destruct (predicate_dec value); [reflexivity|contradiction].
Qed.

Theorem decidable_monotone_subsequence_finite_cover :
    (forall sequence : nat -> X,
      (forall n, predicate (sequence n)) ->
      exists indices : nat -> nat,
        StrictlyIncreasing indices /\
        forall n, relation
          (sequence (indices n)) (sequence (indices (S n)))) ->
    exists basis : list {value : X | predicate value},
      forall value : {value : X | predicate value},
        exists base, List.In base basis /\
          relation (proj1_sig base) (proj1_sig value).
Proof.
  intro Hsubsequence.
  destruct (classic (exists basis : list {value : X | predicate value},
      forall value : {value : X | predicate value},
        exists base, List.In base basis /\
          relation (proj1_sig base) (proj1_sig value)))
    as [Hcover|Hno]; [exact Hcover|].
  exfalso.
  assert (Hescape : forall basis : list {value : X | predicate value},
      exists value, predicate value /\
        avoids_prefix basis value).
  { intro basis. apply NNPP. intro Hnone. apply Hno. exists basis.
    intros [value Hvalid]. apply NNPP. intro Hnotcovered. apply Hnone.
    exists value. split; [exact Hvalid|].
    intros base Hin Hrel. apply Hnotcovered. exists base. auto. }
  assert (Hescaping_code : forall basis : list {value : X | predicate value},
      exists code, escaping_code basis code).
  { intro basis. destruct (Hescape basis) as [value [Hvalid Hvalue]].
    destruct (decoded_predicate_value_complete value Hvalid)
      as [code Hcode].
    exists code. unfold escaping_code. now rewrite Hcode. }
  assert (choose_escape : forall basis : list {value : X | predicate value},
      {value : X | predicate value /\
        avoids_prefix basis value}).
  { intro basis.
    destruct (@constructive_indefinite_ground_description_nat
      (escaping_code basis) (escaping_code_dec basis)
      (Hescaping_code basis)) as [code Hcode].
    unfold escaping_code in Hcode.
    destruct (decoded_predicate_value code) as [value|] eqn:Hdecode;
      [|contradiction].
    exists value. split.
    - eapply decoded_predicate_value_sound; eauto.
    - exact Hcode. }
  set (build := fix build (count : nat) :
      list {value : X | predicate value} :=
    match count with
    | O => []
    | S count' =>
        let prefix := build count' in
        prefix ++ [exist _ (proj1_sig (choose_escape prefix))
          (proj1 (proj2_sig (choose_escape prefix)))]
    end).
  set (bad := fun index =>
    exist predicate (proj1_sig (choose_escape (build index)))
      (proj1 (proj2_sig (choose_escape (build index))))).
  assert (Hbuild_succ : forall index,
      build (S index) = build index ++ [bad index]).
  { intro index. unfold bad. cbn. reflexivity. }
  assert (Hbuild_prefix : forall earlier later, (earlier <= later)%nat ->
      exists suffix, build later = build earlier ++ suffix).
  { intros earlier later Hle. induction Hle.
    - exists []. now rewrite app_nil_r.
    - destruct IHHle as [suffix Hsuffix].
      rewrite Hbuild_succ, Hsuffix.
      exists (suffix ++ [bad m]). symmetry. apply app_assoc. }
  assert (Hbad_member : forall earlier later, (earlier < later)%nat ->
      List.In (bad earlier) (build later)).
  { intros earlier later Hlt.
    destruct (Hbuild_prefix (S earlier) later ltac:(lia))
      as [suffix Hsuffix].
    rewrite Hsuffix, Hbuild_succ, in_app_iff. left.
    apply in_app_iff. right. cbn. auto. }
  destruct (Hsubsequence (fun index => proj1_sig (bad index)))
    as [indices [Hincreasing Hrelated]].
  - intro index. exact (proj2_sig (bad index)).
  - specialize (Hrelated 0%nat).
    exact ((proj2 (proj2_sig (choose_escape (build (indices 1%nat)))))
      (bad (indices 0%nat))
      (Hbad_member (indices 0%nat) (indices 1%nat) (Hincreasing 0%nat))
      Hrelated).
Qed.

End DecidableMonotoneFiniteCover.

Theorem monotone_subsequence_implies_finitary :
  forall d (period set : ZSet d),
    Periodic period ->
    QCylindric period set ->
    (forall x, {set x} + {~ set x}) ->
    (forall x y,
      {PeriodicLe period x y} + {~ PeriodicLe period x y}) ->
    (forall sequence : nat -> ZVec d,
      (forall n, set (sequence n)) ->
      exists indices : nat -> nat,
        StrictlyIncreasing indices /\
        forall n,
          PeriodicLe period
            (sequence (indices n))
            (sequence (indices (S n)))) ->
    FinitaryQCylindric period set.
Proof.
  intros d period set Hperiodic Hcylindric Hset_dec Hle_dec Hsubsequence.
  destruct (@decidable_monotone_subsequence_finite_cover
      (ZVec d) (zvec_codec d) set (PeriodicLe period)
      Hset_dec Hle_dec Hsubsequence) as [basis Hcover].
  exists (List.map (@proj1_sig _ set) basis).
  intro value. split.
  - intro Hvalue.
    destruct (Hcover (exist set value Hvalue))
      as [base [Hbase Hle]].
    exists (proj1_sig base), (zvec_sub value (proj1_sig base)).
    repeat split.
    + apply in_map. exact Hbase.
    + exact Hle.
    + symmetry. apply zvec_sub_add_cancel.
  - intros [base [increment [Hbase [Hincrement ->]]]].
    apply in_map_iff in Hbase.
    destruct Hbase as [presented [Hpresented Hpresented_in]].
    subst base. apply Hcylindric.
    + exact (proj2_sig presented).
    + exact Hincrement.
Qed.

Theorem lemma_6_10_maximal_extract_finitary :
  forall d
    (period excluded remaining : ZSet d)
    (face : QSet d),
    Periodic period ->
    FinitelyGeneratedPeriodic period ->
    FullPeriodic period ->
    FinitaryQCylindric period excluded ->
    FinitaryQCylindric period remaining ->
    (forall value, excluded value -> remaining value) ->
    MaximalNonemptyExtractFace
      period excluded remaining face ->
    FinitaryQCylindric
      (FacePeriod period face)
      (ExtractFace period face excluded remaining).
Proof.
  intros d period excluded remaining face Hperiodic Hperiod_finite Hfull
    Hexcluded_finite Hremaining_finite Hsubset Hmaximal.
  assert (Hface : FaceOf (Cone period) face) by exact (proj1 Hmaximal).
  assert (Hface_periodic : Periodic (FacePeriod period face)).
  { now apply face_periodic. }
  assert (Hface_finite :
      FinitelyGeneratedPeriodic (FacePeriod period face)).
  { now apply face_periodic_finitely_generated. }
  assert (Hremaining_cylindric : QCylindric period remaining).
  { now apply finitary_qcylindric_implies_cylindric. }
  pose proof Hperiod_finite as Hperiod_presentation.
  pose proof Hface_finite as Hface_presentation.
  pose proof Hexcluded_finite as Hexcluded_presentation.
  pose proof Hremaining_finite as Hremaining_presentation.
  destruct Hperiod_presentation as
    [period_generators [Hperiod_generators Hperiod_spec]].
  destruct Hface_presentation as
    [face_generators [Hface_generators Hface_spec]].
  destruct Hexcluded_presentation as [excluded_bases Hexcluded_bases].
  destruct Hremaining_presentation as [remaining_bases Hremaining_bases].
  assert (Hexcluded_spec : forall value,
      excluded value <->
        FinitelyPresented period_generators excluded_bases value).
  { intro value. rewrite finitely_presented_spec.
    rewrite (Hexcluded_bases value).
    split.
    - intros [base [increment [Hbase [Hincrement ->]]]].
      exists base, increment. repeat split; try assumption.
      now apply (proj1 (Hperiod_spec increment)).
    - intros [base [increment [Hbase [Hincrement ->]]]].
      exists base, increment. repeat split; try assumption.
      now apply (proj2 (Hperiod_spec increment)). }
  assert (Hremaining_spec : forall value,
      remaining value <->
        FinitelyPresented period_generators remaining_bases value).
  { intro value. rewrite finitely_presented_spec.
    rewrite (Hremaining_bases value).
    split.
    - intros [base [increment [Hbase [Hincrement ->]]]].
      exists base, increment. repeat split; try assumption.
      now apply (proj1 (Hperiod_spec increment)).
    - intros [base [increment [Hbase [Hincrement ->]]]].
      exists base, increment. repeat split; try assumption.
      now apply (proj2 (Hperiod_spec increment)). }
  apply monotone_subsequence_implies_finitary.
  - exact Hface_periodic.
  - now apply extract_face_cylindric.
  - intro value. exact (extract_face_dec_explicit period excluded remaining
      face period_generators face_generators excluded_bases remaining_bases
      Hface_periodic Hremaining_cylindric Hperiod_spec Hface_spec
      Hexcluded_spec Hremaining_spec value).
  - intros left right.
    exact (face_periodic_le_dec_explicit (FacePeriod period face)
      face_generators Hface_spec left right).
  - exact (maximal_extract_monotone_subsequence d period excluded remaining
      face Hperiodic Hperiod_finite Hfull Hexcluded_finite Hremaining_finite
      Hsubset Hmaximal).
Qed.
