From Coq Require Import List Vector ZArith Lia.
From Mell.Core Require Import Vector.
From Mell.Semilinear Require Import Presentation.
From Mell.Presburger Require Import Syntax Semantics.

Import ListNotations.
Open Scope Z_scope.

Fixpoint formula_and (formulas : list formula) : formula :=
  match formulas with
  | [] => Top
  | f :: fs => ANd f (formula_and fs)
  end.

Fixpoint formula_or (formulas : list formula) : formula :=
  match formulas with
  | [] => Bot
  | f :: fs => Or f (formula_or fs)
  end.

Fixpoint exists_many (count : nat) (body : formula) : formula :=
  match count with
  | O => body
  | S count' => Exists (exists_many count' body)
  end.

Fixpoint lift_term (amount cutoff : nat) (t : term) : term :=
  match t with
  | Num value => Num value
  | Var index => if Nat.leb cutoff index then Var (amount + index)%nat else Var index
  | Plus lhs rhs => Plus (lift_term amount cutoff lhs) (lift_term amount cutoff rhs)
  | Neg body => Neg (lift_term amount cutoff body)
  | Scale coefficient body => Scale coefficient (lift_term amount cutoff body)
  end.

Definition vector_entry {d} (value : NVec d) (coordinate : nat) : nat :=
  List.nth coordinate (Vector.to_list value) 0%nat.

Fixpoint period_sum {d} (coordinate coefficient_index : nat)
    (periods : list (NVec d)) : term :=
  match periods with
  | [] => Num 0
  | period :: periods' =>
      Plus
        (Scale (Z.of_nat (vector_entry period coordinate))
          (Var (coefficient_index + length periods')%nat))
        (period_sum coordinate coefficient_index periods')
  end.

Definition coordinate_equation {d} (coefficient_count coordinate : nat)
    (point : term) (component : LinearComponent d) : formula :=
  Eq (lift_term coefficient_count 0 point)
    (Plus (Num (Z.of_nat (vector_entry (fst component) coordinate)))
      (period_sum coordinate 0 (snd component))).

Definition component_body {d} (points : list term)
    (component : LinearComponent d) : formula :=
  let coefficient_count := length (snd component) in
  formula_and
    (List.map (fun index => Le (Num 0) (Var index)) (seq 0 coefficient_count) ++
     List.map (fun '(coordinate, point) =>
       coordinate_equation coefficient_count coordinate point component)
       (List.combine (seq 0 d) points)).

Definition compile_component {d} (points : list term)
    (component : LinearComponent d) : formula :=
  exists_many (length (snd component)) (component_body points component).

Definition compile_membership_terms {d} (points : list term)
    (code : SemiCode d) : formula :=
  formula_or (List.map (compile_component points) code).

Definition compile_membership {d} (code : SemiCode d) : formula :=
  compile_membership_terms (List.map Var (seq 0 d)) code.

Fixpoint extend_many (env : environment) (values : list Z) : environment :=
  match values with
  | [] => env
  | value :: values' => extend_many (extend env value) values'
  end.

Lemma formula_and_semantics : forall env formulas,
    formula_semantics env (formula_and formulas) <->
    List.Forall (formula_semantics env) formulas.
Proof.
  intros env formulas; induction formulas as [|f fs IH]; simpl.
  - split; intro H; constructor.
  - rewrite IH. split.
    + intros [Hf Hfs]. constructor; assumption.
    + intros H. inversion H; subst. tauto.
Qed.

Lemma formula_or_semantics : forall env formulas,
    formula_semantics env (formula_or formulas) <->
    List.Exists (formula_semantics env) formulas.
Proof.
  intros env formulas; induction formulas as [|f fs IH]; simpl.
  - split; intro H; inversion H.
  - rewrite IH. split.
    + intros [Hf|Hfs]; [constructor 1|constructor 2]; assumption.
    + intros H. inversion H; subst; tauto.
Qed.

Lemma exists_many_semantics : forall count env body,
    formula_semantics env (exists_many count body) <->
    exists values, length values = count /\
      formula_semantics (extend_many env values) body.
Proof.
  induction count as [|count IH]; intros env body; simpl.
  - split.
    + intros H. exists []; simpl; tauto.
    + intros [values [Hlength H]]. destruct values; simpl in *; [assumption|discriminate].
  - split.
    + intros [value H]. apply IH in H.
      destruct H as [values [Hlength Hbody]].
      exists (value :: values). simpl. split; [lia|exact Hbody].
    + intros [values [Hlength Hbody]].
      destruct values as [|value values]; simpl in Hlength; [discriminate|].
      exists value. apply IH. exists values. split; [lia|exact Hbody].
Qed.

Lemma extend_many_app : forall env left right,
    extend_many env (left ++ right) =
    extend_many (extend_many env left) right.
Proof.
  intros env left; revert env.
  induction left as [|value left IH]; intros env right; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma extend_many_lookup : forall (env : environment) values (index : nat),
    (index < length values)%nat ->
    extend_many env values index = List.nth (length values - S index) values 0.
Proof.
  intros env values.
  induction values using rev_ind; intros index Hlt.
  - simpl in Hlt. lia.
  - rewrite extend_many_app. simpl.
    rewrite app_length in Hlt. simpl in Hlt.
    destruct index as [|index]; simpl.
    + rewrite length_app. simpl.
      replace (length values + 1 - 1)%nat with (length values) by lia.
      symmetry. apply nth_middle.
    + assert (Hindex : (index < length values)%nat) by lia.
      rewrite IHvalues by exact Hindex.
      rewrite length_app. simpl.
      replace (length values + 1 - S (S index))%nat with
        (length values - S index)%nat by lia.
      symmetry. apply app_nth1. lia.
Qed.

Lemma exists_many_closed : forall count bound body,
    formula_closed (count + bound) body = true ->
    formula_closed bound (exists_many count body) = true.
Proof.
  induction count as [|count IH]; intros bound body Hclosed; simpl in *.
  - exact Hclosed.
  - apply IH. replace (count + S bound)%nat with (S count + bound)%nat by lia.
    exact Hclosed.
Qed.

Lemma formula_and_closed : forall bound formulas,
    List.Forall (fun f => formula_closed bound f = true) formulas ->
    formula_closed bound (formula_and formulas) = true.
Proof.
  intros bound formulas H; induction H; simpl; [reflexivity|].
  rewrite H, IHForall. reflexivity.
Qed.

Lemma formula_or_closed : forall bound formulas,
    List.Forall (fun f => formula_closed bound f = true) formulas ->
    formula_closed bound (formula_or formulas) = true.
Proof.
  intros bound formulas H; induction H; simpl; [reflexivity|].
  rewrite H, IHForall. reflexivity.
Qed.

(* The semantic preservation theorem is stated after its component arithmetic
   lemmas; this module never relies on an unfinished proposition. *)

Lemma vector_entry_nth_order : forall d (value : NVec d) coordinate
    (Hcoordinate : (coordinate < d)%nat),
    vector_entry value coordinate = Vector.nth_order value Hcoordinate.
Proof.
  intros. unfold vector_entry.
  symmetry. apply to_list_nth_order.
Qed.

Lemma vector_entry_add : forall d (left right : NVec d) coordinate,
    (coordinate < d)%nat ->
    vector_entry (nvec_add left right) coordinate =
    (vector_entry left coordinate + vector_entry right coordinate)%nat.
Proof.
  intros d left right coordinate Hcoordinate.
  repeat rewrite vector_entry_nth_order with (Hcoordinate := Hcoordinate).
  unfold nvec_add. apply Vector.nth_map2; reflexivity.
Qed.

Lemma vector_entry_scale : forall d coefficient (value : NVec d) coordinate,
    (coordinate < d)%nat ->
    vector_entry (nvec_scale coefficient value) coordinate =
    (coefficient * vector_entry value coordinate)%nat.
Proof.
  intros d coefficient value coordinate Hcoordinate.
  repeat rewrite vector_entry_nth_order with (Hcoordinate := Hcoordinate).
  unfold nvec_scale. apply Vector.nth_map; reflexivity.
Qed.

Lemma vector_entry_zero : forall d coordinate,
    (coordinate < d)%nat -> vector_entry (nvec_zero d) coordinate = 0%nat.
Proof.
  intros d coordinate Hcoordinate.
  rewrite vector_entry_nth_order with (Hcoordinate := Hcoordinate).
  apply Vector.const_nth.
Qed.

Fixpoint coefficient_sum {d} (coordinate : nat) (coefficients : list nat)
    (periods : list (NVec d)) : option Z :=
  match coefficients, periods with
  | [], [] => Some 0
  | coefficient :: coefficients', period :: periods' =>
      match coefficient_sum coordinate coefficients' periods' with
      | Some tail => Some
          (Z.of_nat coefficient * Z.of_nat (vector_entry period coordinate) + tail)
      | None => None
      end
  | _, _ => None
  end.

Lemma coefficient_sum_exists_of_length : forall d coordinate
    (coefficients : list nat) (periods : list (NVec d)),
    length coefficients = length periods ->
    exists result, coefficient_sum coordinate coefficients periods = Some result.
Proof.
  intros d coordinate coefficients; induction coefficients as [|coefficient coefficients IH];
    intros periods Hlength; destruct periods as [|period periods];
    simpl in Hlength; try discriminate.
  - exists 0. reflexivity.
  - destruct (IH periods ltac:(lia)) as [tail Htail].
    exists (Z.of_nat coefficient * Z.of_nat (vector_entry period coordinate) + tail).
    simpl. rewrite Htail. reflexivity.
Qed.

Lemma weighted_sum_coordinate : forall d (coefficients : list nat)
    (periods : list (NVec d)) (contribution : NVec d) (coordinate : nat),
    (coordinate < d)%nat ->
    weighted_sum coefficients periods = Some contribution ->
    coefficient_sum coordinate coefficients periods =
      Some (Z.of_nat (vector_entry contribution coordinate)).
Proof.
  intros d coefficients; induction coefficients as [|coefficient coefficients IH];
    intros periods contribution coordinate Hcoordinate Hsum;
    destruct periods as [|period periods]; simpl in *; try discriminate.
  - inversion Hsum; subst. rewrite vector_entry_zero by exact Hcoordinate.
    reflexivity.
  - destruct (weighted_sum coefficients periods) as [tail|] eqn:Htail;
      [|discriminate].
    inversion Hsum; subst contribution.
    rewrite vector_entry_add by exact Hcoordinate.
    rewrite vector_entry_scale by exact Hcoordinate.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
    rewrite (IH periods tail coordinate Hcoordinate Htail). reflexivity.
Qed.

Lemma weighted_sum_exists_of_length : forall d (periods : list (NVec d))
    coefficients,
    length coefficients = length periods ->
    exists contribution, weighted_sum coefficients periods = Some contribution.
Proof.
  intros d periods; induction periods as [|period periods IH];
    intros coefficients Hlength; destruct coefficients as [|coefficient coefficients];
    simpl in Hlength; try discriminate.
  - exists (nvec_zero d). reflexivity.
  - destruct (IH coefficients ltac:(lia)) as [tail Htail].
    exists (nvec_add (nvec_scale coefficient period) tail).
    simpl. rewrite Htail. reflexivity.
Qed.

Lemma weighted_sum_length : forall d coefficients (periods : list (NVec d))
    contribution,
    weighted_sum coefficients periods = Some contribution ->
    length coefficients = length periods.
Proof.
  intros d coefficients; induction coefficients as [|coefficient coefficients IH];
    intros periods contribution Hsum; destruct periods as [|period periods];
    simpl in Hsum; try discriminate; auto.
  destruct (weighted_sum coefficients periods) eqn:Htail; [|discriminate].
  inversion Hsum. simpl. f_equal. eapply IH; eauto.
Qed.

Lemma extend_many_tail_lookup : forall (env : environment) values index,
    extend_many env values (length values + index)%nat = env index.
Proof.
  intros env values.
  induction values using rev_ind; intros index.
  - reflexivity.
  - rewrite extend_many_app. simpl.
    rewrite length_app. simpl.
    replace (length values + 1 + index)%nat with
      (S (length values + index)) by lia.
    simpl. apply IHvalues.
Qed.

Lemma lift_term_semantics : forall t amount env values,
    length values = amount ->
    term_semantics (extend_many env values) (lift_term amount 0 t) =
    term_semantics env t.
Proof.
  induction t; intros amount env values Hlength; simpl.
  - reflexivity.
  - rewrite <- Hlength. apply extend_many_tail_lookup.
  - rewrite IHt1 with (values := values) by exact Hlength.
    rewrite IHt2 with (values := values) by exact Hlength. reflexivity.
  - rewrite IHt with (values := values) by exact Hlength. reflexivity.
  - rewrite IHt with (values := values) by exact Hlength. reflexivity.
Qed.

Lemma period_sum_semantics : forall d (coordinate : nat)
    (periods : list (NVec d)) (env : environment) (values : list Z),
    length values = length periods ->
    (forall value, List.In value values -> 0 <= value) ->
    term_semantics (extend_many env values)
      (period_sum coordinate 0 periods) =
    match coefficient_sum coordinate (List.map Z.to_nat values) periods with
    | Some result => result
    | None => 0
    end.
Proof.
  intros d coordinate periods; induction periods as [|period periods IH];
    intros env values Hlength Hnonnegative; destruct values as [|value values];
    simpl in Hlength; try discriminate; simpl.
  - reflexivity.
  - replace (length periods) with (length values) by lia.
    replace (length values) with (length values + 0)%nat by lia.
    rewrite extend_many_tail_lookup. simpl.
    rewrite Z2Nat.id by (apply Hnonnegative; left; reflexivity).
    rewrite IH with (values := values).
    + destruct (coefficient_sum_exists_of_length d coordinate
        (List.map Z.to_nat values) periods) as [tail Htail].
      * rewrite map_length. lia.
      * rewrite Htail. simpl. ring.
    + lia.
    + intros item Hin. apply Hnonnegative. right. exact Hin.
Qed.

Definition terms_match {d} (env : environment) (points : list term)
    (value : NVec d) : Prop :=
  length points = d /\
  forall coordinate, (coordinate < d)%nat ->
    term_semantics env (List.nth coordinate points (Num 0)) =
    Z.of_nat (vector_entry value coordinate).

Lemma seq_point_in_combine : forall d (points : list term) coordinate,
    length points = d -> (coordinate < d)%nat ->
    List.In (coordinate, List.nth coordinate points (Num 0))
      (List.combine (seq 0 d) points).
Proof.
  intros d points coordinate Hlength Hcoordinate.
  assert (Hcombined : (coordinate <
      length (List.combine (seq 0 d) points))%nat).
  { rewrite combine_length, seq_length, Hlength, Nat.min_id. exact Hcoordinate. }
  pose proof (@nth_In (nat * term) coordinate
    (List.combine (seq 0 d) points) (0%nat, Num 0) Hcombined) as Hin.
  rewrite combine_nth in Hin.
  - rewrite seq_nth in Hin by exact Hcoordinate. simpl in Hin. exact Hin.
  - rewrite seq_length. symmetry. exact Hlength.
Qed.

Lemma point_of_seq_combine : forall start d (points : list term)
    coordinate point,
    length points = d ->
    List.In ((start + coordinate)%nat, point)
      (List.combine (seq start d) points) ->
    point = List.nth coordinate points (Num 0).
Proof.
  intros start d; revert start.
  induction d as [|d IH]; intros start points coordinate point Hlength Hin;
    destruct points as [|head points]; simpl in Hlength; try discriminate;
    simpl in Hin; [contradiction|].
  inversion Hlength; subst.
  destruct Hin as [Hequal|Hin].
  - inversion Hequal; subst. assert (coordinate = 0%nat) by lia. subst.
    reflexivity.
  - destruct coordinate as [|coordinate].
    + exfalso.
      apply in_combine_l in Hin. apply in_seq in Hin. lia.
    + simpl. apply (IH (S start) points coordinate point eq_refl).
      replace (start + S coordinate)%nat with (S start + coordinate)%nat in Hin by lia.
      exact Hin.
Qed.

Lemma nonnegative_formulas_correct : forall count env,
    List.Forall (formula_semantics env)
      (List.map (fun index => Le (Num 0) (Var index)) (seq 0 count)) <->
    forall index, (index < count)%nat -> 0 <= env index.
Proof.
  intros count env. split.
  - intros Hall index Hindex.
    apply (proj1 (List.Forall_forall _ _) Hall (Le (Num 0) (Var index))).
    apply in_map_iff. exists index. split; [reflexivity|]. apply in_seq. lia.
  - intros Hall. apply List.Forall_forall.
    intros f Hin. apply in_map_iff in Hin as [index [<- Hin]]. simpl.
    apply Hall. apply in_seq in Hin. lia.
Qed.

Theorem compile_component_correct : forall d (points : list term)
    (component : LinearComponent d) env,
    length points = d ->
    formula_semantics env (compile_component points component) <->
    exists value, linear_denote component value /\ terms_match env points value.
Proof.
  intros d points [base periods] env Hpoints.
  unfold compile_component. simpl snd.
  rewrite exists_many_semantics. split.
  - intros [values [Hvalues Hbody]].
    unfold component_body in Hbody. simpl fst in Hbody. simpl snd in Hbody.
    apply formula_and_semantics in Hbody.
    apply Forall_app in Hbody as [Hnonnegative Hequations].
    pose proof (proj1 (nonnegative_formulas_correct (length periods)
      (extend_many env values)) Hnonnegative) as Hnonnegative_at.
    assert (Hvalues_nonnegative : forall value,
        List.In value values -> 0 <= value).
    { intros value Hin.
      apply In_nth_error in Hin as [index Hindex].
      assert (Hlt : (index < length values)%nat).
      { apply nth_error_Some. rewrite Hindex. discriminate. }
      specialize (Hnonnegative_at (length values - S index)%nat ltac:(lia)).
      rewrite extend_many_lookup in Hnonnegative_at by lia.
      replace (length values - S (length values - S index))%nat with index
        in Hnonnegative_at by lia.
      rewrite (@nth_error_nth Z values index value 0 Hindex) in Hnonnegative_at.
      exact Hnonnegative_at. }
    set (coefficients := List.map Z.to_nat values).
    assert (Hcoeff_length : length coefficients = length periods).
    { unfold coefficients. rewrite length_map. exact Hvalues. }
    destruct (weighted_sum_exists_of_length d periods coefficients Hcoeff_length)
      as [contribution Hcontribution].
    exists (nvec_add base contribution). split.
    + exists coefficients, contribution. split; [exact Hcontribution|reflexivity].
    + split; [exact Hpoints|].
      intros coordinate Hcoordinate.
      assert (Hin_equation : List.In
        (coordinate_equation (length periods) coordinate
          (List.nth coordinate points (Num 0)) (base, periods))
        (List.map
          (fun '(coordinate, point) => coordinate_equation
            (length periods) coordinate point (base, periods))
          (List.combine (seq 0 d) points))).
      { apply in_map_iff.
        exists (coordinate, List.nth coordinate points (Num 0)).
        split; [reflexivity|]. apply seq_point_in_combine; assumption. }
      pose proof (proj1 (List.Forall_forall _ _) Hequations _ Hin_equation)
        as Hequation.
      unfold coordinate_equation in Hequation. simpl fst in Hequation.
      simpl snd in Hequation. simpl in Hequation.
      rewrite lift_term_semantics with (values := values) in Hequation by exact Hvalues.
      rewrite period_sum_semantics with (values := values) in Hequation;
        [|exact Hvalues|exact Hvalues_nonnegative].
      unfold coefficients in Hcontribution, Hcoeff_length.
      pose proof (weighted_sum_coordinate d (List.map Z.to_nat values)
        periods contribution coordinate Hcoordinate Hcontribution) as Hcoordinate_sum.
      rewrite Hcoordinate_sum in Hequation. simpl in Hequation.
      rewrite vector_entry_add by exact Hcoordinate.
      rewrite Nat2Z.inj_add. exact Hequation.
  - intros [value [[coefficients [contribution [Hsum ->]]]
      [Hpoint_length Hmatches]]].
    pose proof (weighted_sum_length d coefficients periods contribution Hsum)
      as Hcoefficients_length.
    exists (List.map Z.of_nat coefficients). split.
    + rewrite length_map. exact Hcoefficients_length.
    + unfold component_body. simpl fst. simpl snd.
      apply formula_and_semantics. apply Forall_app. split.
      * apply nonnegative_formulas_correct.
        intros index Hindex.
        rewrite extend_many_lookup by (rewrite length_map; lia).
        rewrite length_map.
        rewrite map_nth with (d := 0%nat).
        apply Nat2Z.is_nonneg.
      * apply List.Forall_forall.
        intros f Hin. apply in_map_iff in Hin as [[coordinate point] [Hf Hin]].
        subst f.
        apply in_combine_l in Hin as Hcoordinate_in.
        apply in_seq in Hcoordinate_in.
        assert (Hcoordinate : (coordinate < d)%nat) by lia.
        assert (Hpoint : point = List.nth coordinate points (Num 0)).
        { apply (point_of_seq_combine 0 d points coordinate point Hpoint_length).
          simpl. exact Hin. }
        subst point.
        unfold coordinate_equation. simpl fst. simpl snd. simpl.
        rewrite lift_term_semantics with
          (values := List.map Z.of_nat coefficients).
        2: { rewrite length_map. exact Hcoefficients_length. }
        rewrite period_sum_semantics with
          (values := List.map Z.of_nat coefficients).
        -- rewrite List.map_map.
           replace (List.map (fun x => Z.to_nat (Z.of_nat x)) coefficients)
             with coefficients.
           2: { symmetry. rewrite <- List.map_id.
                apply List.map_ext. intros. apply Nat2Z.id. }
           pose proof (weighted_sum_coordinate d coefficients periods contribution
             coordinate Hcoordinate Hsum) as Hcoordinate_sum.
           rewrite Hcoordinate_sum. simpl.
           rewrite Hmatches by exact Hcoordinate.
           rewrite vector_entry_add by exact Hcoordinate.
           rewrite Nat2Z.inj_add. reflexivity.
        -- rewrite length_map. exact Hcoefficients_length.
        -- intros item Hitem. apply in_map_iff in Hitem as [coefficient [<- _]].
           apply Nat2Z.is_nonneg.
Qed.

Theorem compile_membership_terms_correct : forall d (points : list term)
    (code : SemiCode d) env,
    length points = d ->
    formula_semantics env (compile_membership_terms points code) <->
    exists value, denote code value /\ terms_match env points value.
Proof.
  intros d points code env Hpoints.
  unfold compile_membership_terms. rewrite formula_or_semantics. split.
  - intros Hexists. apply Exists_exists in Hexists as [f [Hin Hsem]].
    apply in_map_iff in Hin as [component [<- Hin]].
    apply compile_component_correct in Hsem; [|exact Hpoints].
    destruct Hsem as [value [Hlinear Hmatches]].
    exists value. split; [exists component; tauto|exact Hmatches].
  - intros [value [[component [Hin Hlinear]] Hmatches]].
    apply Exists_exists. exists (compile_component points component). split.
    + apply in_map. exact Hin.
    + apply compile_component_correct; [exact Hpoints|].
      exists value. tauto.
Qed.

Lemma variable_points_match : forall d env (value : NVec d),
    terms_match env (List.map Var (seq 0 d)) value <->
    forall coordinate, (coordinate < d)%nat ->
      env coordinate = Z.of_nat (vector_entry value coordinate).
Proof.
  intros d env value. unfold terms_match. split.
  - intros [_ Hmatch] coordinate Hcoordinate.
    specialize (Hmatch coordinate Hcoordinate).
    rewrite nth_indep with (d' := Var 0) in Hmatch.
    2: { rewrite length_map, seq_length. exact Hcoordinate. }
    rewrite map_nth with (d := 0%nat) in Hmatch.
    rewrite seq_nth in Hmatch by exact Hcoordinate. simpl in Hmatch.
    exact Hmatch.
  - intros Hmatch. split.
    + rewrite length_map, seq_length. reflexivity.
    + intros coordinate Hcoordinate.
      rewrite nth_indep with (d' := Var 0).
      2: { rewrite length_map, seq_length. exact Hcoordinate. }
      rewrite map_nth with (d := 0%nat).
      rewrite seq_nth by exact Hcoordinate. simpl.
      apply Hmatch. exact Hcoordinate.
Qed.

Theorem compile_membership_correct : forall d (code : SemiCode d) env,
    formula_semantics env (compile_membership code) <->
    exists value, denote code value /\
      forall coordinate, (coordinate < d)%nat ->
        env coordinate = Z.of_nat (vector_entry value coordinate).
Proof.
  intros d code env. unfold compile_membership.
  rewrite compile_membership_terms_correct.
  - split.
    + intros [value [Hdenote Hmatch]]. exists value. split.
      * exact Hdenote.
      * apply variable_points_match. exact Hmatch.
    + intros [value [Hdenote Hmatch]]. exists value. split.
      * exact Hdenote.
      * apply variable_points_match. exact Hmatch.
  - rewrite length_map, seq_length. reflexivity.
Qed.

Lemma lift_term_closed : forall t bound amount,
    term_closed bound t = true ->
    term_closed (amount + bound) (lift_term amount 0 t) = true.
Proof.
  induction t; intros bound amount Hclosed; simpl in *; try reflexivity.
  - apply Nat.ltb_lt in Hclosed. apply Nat.ltb_lt.
    lia.
  - apply Bool.andb_true_iff in Hclosed as [Hleft Hright].
    rewrite IHt1 by exact Hleft. rewrite IHt2 by exact Hright. reflexivity.
  - apply IHt. exact Hclosed.
  - apply IHt. exact Hclosed.
Qed.

Lemma term_closed_monotone : forall t lower upper,
    term_closed lower t = true -> (lower <= upper)%nat ->
    term_closed upper t = true.
Proof.
  induction t; intros lower upper Hclosed Hle; simpl in *; try reflexivity.
  - apply Nat.ltb_lt in Hclosed. apply Nat.ltb_lt. lia.
  - apply Bool.andb_true_iff in Hclosed as [Hleft Hright].
    rewrite IHt1 with (lower := lower) by assumption.
    rewrite IHt2 with (lower := lower) by assumption. reflexivity.
  - apply IHt with (lower := lower); assumption.
  - apply IHt with (lower := lower); assumption.
Qed.

Lemma period_sum_closed : forall d coordinate start (periods : list (NVec d)),
    term_closed (start + length periods) (period_sum coordinate start periods) = true.
Proof.
  intros d coordinate start periods; induction periods as [|period periods IH]; simpl.
  - reflexivity.
  - apply Bool.andb_true_iff. split.
    + apply Nat.ltb_lt. lia.
    + eapply term_closed_monotone; [exact IH|lia].
Qed.

Lemma coordinate_equation_closed : forall d bound (points : list term)
    (component : LinearComponent d) (coordinate : nat) (point : term),
    length points = d -> List.In (coordinate, point)
      (List.combine (seq 0 d) points) ->
    term_closed bound point = true ->
    formula_closed (length (snd component) + bound)
      (coordinate_equation (length (snd component)) coordinate point component) = true.
Proof.
  intros d bound points [base periods] coordinate point Hlength Hin Hpoint.
  unfold coordinate_equation. simpl fst. simpl snd. simpl.
  apply Bool.andb_true_iff. split.
  - apply lift_term_closed. exact Hpoint.
  - eapply term_closed_monotone.
    + apply period_sum_closed.
    + lia.
Qed.

Lemma compile_component_closed : forall d bound (points : list term)
    (component : LinearComponent d),
    length points = d ->
    List.Forall (fun point => term_closed bound point = true) points ->
    formula_closed bound (compile_component points component) = true.
Proof.
  intros d bound points [base periods] Hlength Hpoints.
  unfold compile_component. simpl snd. apply exists_many_closed.
  unfold component_body. simpl fst. simpl snd. apply formula_and_closed.
  apply Forall_app. split.
  - apply List.Forall_forall. intros f Hin.
    apply in_map_iff in Hin as [index [<- Hin]]. simpl.
    apply in_seq in Hin. apply Nat.ltb_lt. lia.
  - apply List.Forall_forall. intros f Hin.
    apply in_map_iff in Hin as [[coordinate point] [<- Hin]].
    eapply (coordinate_equation_closed d bound points (base, periods)
      coordinate point); try assumption.
    apply (proj1 (List.Forall_forall _ _) Hpoints point).
    apply in_combine_r in Hin. exact Hin.
Qed.

Lemma compile_membership_terms_closed : forall d bound (points : list term)
    (code : SemiCode d),
    length points = d ->
    List.Forall (fun point => term_closed bound point = true) points ->
    formula_closed bound (compile_membership_terms points code) = true.
Proof.
  intros d bound points code Hlength Hpoints.
  unfold compile_membership_terms. apply formula_or_closed.
  apply List.Forall_forall. intros f Hin.
  apply in_map_iff in Hin as [component [<- Hin]].
  apply compile_component_closed; assumption.
Qed.

Lemma compile_membership_closed : forall d (code : SemiCode d),
    formula_closed d (compile_membership code) = true.
Proof.
  intros d code. unfold compile_membership.
  apply compile_membership_terms_closed.
  - rewrite length_map, seq_length. reflexivity.
  - apply List.Forall_forall. intros point Hin.
    apply in_map_iff in Hin as [index [<- Hin]].
    apply in_seq in Hin. simpl. apply Nat.ltb_lt. lia.
Qed.
