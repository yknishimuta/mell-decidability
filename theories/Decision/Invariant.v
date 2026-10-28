From Coq Require Import List Vector ZArith Lia Bool Classical_Prop.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs RunOrder.
From Mell.Semilinear Require Import Presentation Formula.
From Mell.Presburger Require Import Syntax Semantics Decide.

Import ListNotations.
Open Scope Z_scope.

Definition InitialIncluded {d} (S : IBVAS d) (P : NVec d -> Prop) : Prop :=
  forall value, List.In value (initial_vectors S) -> P value.

Definition Closed {d} (S : IBVAS d) (P : NVec d -> Prop) : Prop :=
  forall action children value,
    List.In action (system_actions S) ->
    List.Forall P children ->
    apply_action action children = Some value ->
    P value.

Definition decide_closed_formula (f : formula) : bool :=
  match Bool.bool_dec (formula_closed 0 f) true with
  | left Hclosed => presburger_decide (close_sentence f Hclosed)
  | right _ => false
  end.

Lemma decide_closed_formula_correct : forall f,
    formula_closed 0 f = true ->
    decide_closed_formula f = true <-> formula_semantics empty_environment f.
Proof.
  intros f Hclosed. unfold decide_closed_formula.
  destruct (Bool.bool_dec (formula_closed 0 f) true) as [Hcheck|Hcheck].
  - apply presburger_decide_correct.
  - contradiction.
Qed.

Definition constant_points {d} (value : NVec d) : list term :=
  List.map (fun coordinate =>
    Num (Z.of_nat (vector_entry value coordinate))) (seq 0 d).

Definition membership_sentence_formula {d} (code : SemiCode d)
    (value : NVec d) : formula :=
  compile_membership_terms (constant_points value) code.

Definition check_membership {d} (code : SemiCode d) (value : NVec d) : bool :=
  decide_closed_formula (membership_sentence_formula code value).

Lemma constant_points_length : forall d (value : NVec d),
    length (constant_points value) = d.
Proof. intros; unfold constant_points; rewrite length_map, seq_length; reflexivity. Qed.

Lemma constant_points_closed : forall d (value : NVec d),
    List.Forall (fun point => term_closed 0 point = true) (constant_points value).
Proof.
  intros d value. apply List.Forall_forall. intros point Hin.
  unfold constant_points in Hin. apply in_map_iff in Hin as [coordinate [<- _]].
  reflexivity.
Qed.

Lemma membership_sentence_formula_closed : forall d (code : SemiCode d)
    (value : NVec d),
    formula_closed 0 (membership_sentence_formula code value) = true.
Proof.
  intros. unfold membership_sentence_formula.
  apply compile_membership_terms_closed.
  - apply constant_points_length.
  - apply constant_points_closed.
Qed.

Lemma nvec_ext_entry : forall d (left right : NVec d),
    (forall coordinate, (coordinate < d)%nat ->
      vector_entry left coordinate = vector_entry right coordinate) ->
    left = right.
Proof.
  intros d left right Hentry. apply Vector.eq_nth_iff.
  intros index index' Hindex; subst index'.
  pose (coordinate := proj1_sig (Fin.to_nat index)).
  assert (Hcoordinate : (coordinate < d)%nat).
  { unfold coordinate. exact (proj2_sig (Fin.to_nat index)). }
  specialize (Hentry coordinate Hcoordinate).
  repeat rewrite vector_entry_nth_order with (Hcoordinate := Hcoordinate) in Hentry.
  assert (Hfin : Fin.of_nat_lt Hcoordinate = index).
  { apply Fin.to_nat_inj. rewrite Fin.to_nat_of_nat. reflexivity. }
  unfold Vector.nth_order in Hentry. rewrite Hfin in Hentry. exact Hentry.
Qed.

Theorem check_membership_correct : forall d (code : SemiCode d) value,
    check_membership code value = true <-> denote code value.
Proof.
  intros d code value. unfold check_membership.
  rewrite decide_closed_formula_correct by apply membership_sentence_formula_closed.
  unfold membership_sentence_formula.
  rewrite compile_membership_terms_correct by apply constant_points_length.
  split.
  - intros [candidate [Hdenote [_ Hmatch]]].
    assert (candidate = value).
    { apply nvec_ext_entry. intros coordinate Hcoordinate.
      specialize (Hmatch coordinate Hcoordinate).
      unfold constant_points in Hmatch.
      rewrite nth_indep with
        (d' := Num (Z.of_nat (vector_entry value coordinate))) in Hmatch.
      2: { rewrite length_map, seq_length. exact Hcoordinate. }
      rewrite map_nth with (d := coordinate) in Hmatch.
      rewrite seq_nth in Hmatch by exact Hcoordinate. simpl in Hmatch.
      lia. }
    subst. exact Hdenote.
  - intros Hdenote. exists value. split; [exact Hdenote|].
    split; [apply constant_points_length|].
    intros coordinate Hcoordinate. unfold constant_points.
    rewrite nth_indep with
      (d' := Num (Z.of_nat (vector_entry value coordinate))).
    2: { rewrite length_map, seq_length. exact Hcoordinate. }
    rewrite map_nth with (d := coordinate).
    rewrite seq_nth by exact Hcoordinate. reflexivity.
Qed.

Definition check_initials {d} (S : IBVAS d) (code : SemiCode d) : bool :=
  forallb (check_membership code) (initial_vectors S).

Lemma check_initials_correct : forall d (S : IBVAS d) code,
    check_initials S code = true <-> InitialIncluded S (denote code).
Proof.
  intros d S code. unfold check_initials, InitialIncluded.
  rewrite forallb_forall. split; intros H value Hin.
  - apply check_membership_correct. apply H. exact Hin.
  - apply check_membership_correct. apply H. exact Hin.
Qed.

Definition check_target_excluded {d} (code : SemiCode d) (target : NVec d) : bool :=
  negb (check_membership code target).

Lemma check_target_excluded_correct : forall d (code : SemiCode d) target,
    check_target_excluded code target = true <-> ~ denote code target.
Proof.
  intros. unfold check_target_excluded. rewrite negb_true_iff.
  destruct (check_membership code target) eqn:Hmember.
  - split; [discriminate|]. intros Hnot. exfalso. apply Hnot.
    apply check_membership_correct. exact Hmember.
  - split; [intros _ Hdenote|intros; reflexivity].
    apply check_membership_correct in Hdenote. congruence.
Qed.

Definition block_terms (d block : nat) : list term :=
  List.map (fun coordinate => Var (block * d + coordinate)%nat) (seq 0 d).

Fixpoint children_membership_formulas {d} (start count : nat)
    (code : SemiCode d) : list formula :=
  match count with
  | O => []
  | S count' => compile_membership_terms (block_terms d start) code ::
      children_membership_formulas (S start) count' code
  end.

Fixpoint child_sum_term (d start count coordinate : nat) : term :=
  match count with
  | O => Num 0
  | S count' => Plus (Var (start * d + coordinate)%nat)
      (child_sum_term d (S start) count' coordinate)
  end.

Definition zvector_entry {d} (value : ZVec d) (coordinate : nat) : Z :=
  List.nth coordinate (Vector.to_list value) 0.

Definition result_terms {d} (action : Action d) : list term :=
  List.map (fun coordinate =>
    Plus (Num (zvector_entry (action_offset action) coordinate))
      (child_sum_term d 0 (action_arity action) coordinate)) (seq 0 d).

Definition action_counterexample {d} (action : Action d)
    (code : SemiCode d) : formula :=
  let variable_count := (action_arity action * d)%nat in
  exists_many variable_count
    (formula_and
      (List.map (fun index => Le (Num 0) (Var index))
        (seq 0 variable_count) ++
       children_membership_formulas 0 (action_arity action) code ++
       List.map (fun result => Le (Num 0) result) (result_terms action) ++
       [Not (compile_membership_terms (result_terms action) code)])).

Definition check_action_closed {d} (action : Action d)
    (code : SemiCode d) : bool :=
  negb (decide_closed_formula (action_counterexample action code)).

Definition check_actions {d} (S : IBVAS d) (code : SemiCode d) : bool :=
  forallb (fun action => check_action_closed action code) (system_actions S).

Definition invariant_obligation {d} (S : IBVAS d) (code : SemiCode d)
    (target : NVec d) : Prop :=
  InitialIncluded S (denote code) /\
  Closed S (denote code) /\
  ~ denote code target.

Definition check_invariantP {d} (S : IBVAS d) (code : SemiCode d)
    (target : NVec d) : bool :=
  check_initials S code && check_actions S code && check_target_excluded code target.

Lemma block_terms_length : forall d block, length (block_terms d block) = d.
Proof. intros; unfold block_terms; rewrite length_map, seq_length; reflexivity. Qed.

Lemma block_terms_closed : forall d arity block,
    (block < arity)%nat ->
    List.Forall (fun point => term_closed (arity * d) point = true)
      (block_terms d block).
Proof.
  intros d arity block Hblock. apply List.Forall_forall.
  intros point Hin. unfold block_terms in Hin.
  apply in_map_iff in Hin as [coordinate [<- Hin]].
  apply in_seq in Hin. simpl. apply Nat.ltb_lt.
  nia.
Qed.

Lemma child_sum_term_closed : forall d arity start count coordinate,
    (start + count <= arity)%nat -> (coordinate < d)%nat ->
    term_closed (arity * d) (child_sum_term d start count coordinate) = true.
Proof.
  intros d arity start count; revert start.
  induction count as [|count IH]; intros start coordinate Hrange Hcoordinate; simpl.
  - reflexivity.
  - apply Bool.andb_true_iff. split.
    + apply Nat.ltb_lt. nia.
    + apply IH; lia.
Qed.

Lemma result_terms_length : forall d (action : Action d),
    length (result_terms action) = d.
Proof. intros; unfold result_terms; rewrite length_map, seq_length; reflexivity. Qed.

Lemma result_terms_closed : forall d (action : Action d),
    List.Forall
      (fun point => term_closed (action_arity action * d) point = true)
      (result_terms action).
Proof.
  intros d action. apply List.Forall_forall. intros point Hin.
  unfold result_terms in Hin. apply in_map_iff in Hin as [coordinate [<- Hin]].
  apply in_seq in Hin. simpl. apply child_sum_term_closed; lia.
Qed.

Lemma children_membership_formulas_closed : forall d arity start count
    (code : SemiCode d),
    (start + count <= arity)%nat ->
    List.Forall (fun f => formula_closed (arity * d) f = true)
      (children_membership_formulas start count code).
Proof.
  intros d arity start count; revert start.
  induction count as [|count IH]; intros start code Hrange; simpl.
  - constructor.
  - constructor.
    + apply compile_membership_terms_closed.
      * apply block_terms_length.
      * apply block_terms_closed. lia.
    + apply IH. lia.
Qed.

Lemma action_counterexample_closed : forall d (action : Action d) code,
    formula_closed 0 (action_counterexample action code) = true.
Proof.
  intros d action code. unfold action_counterexample.
  apply exists_many_closed. rewrite Nat.add_0_r.
  apply formula_and_closed. apply Forall_app. split.
  - apply List.Forall_forall. intros f Hin.
    apply in_map_iff in Hin as [index [<- Hin]].
    apply in_seq in Hin. simpl. apply Nat.ltb_lt. lia.
  - apply Forall_app. split.
    + apply children_membership_formulas_closed. lia.
    + apply Forall_app. split.
      * apply List.Forall_forall. intros f Hin.
        apply in_map_iff in Hin as [result [<- Hin]]. simpl.
        apply (proj1 (List.Forall_forall _ _)
          (result_terms_closed d action) result Hin).
      * constructor.
        -- simpl. apply compile_membership_terms_closed.
           ++ apply result_terms_length.
           ++ apply result_terms_closed.
        -- constructor.
Qed.

Definition block_denotes {d} (env : environment) (code : SemiCode d)
    (block : nat) (value : NVec d) : Prop :=
  denote code value /\ terms_match env (block_terms d block) value.

Lemma children_membership_formulas_correct : forall d start count
    (code : SemiCode d) env,
    List.Forall (formula_semantics env)
      (children_membership_formulas start count code) <->
    exists children,
      List.Forall2 (block_denotes env code) (seq start count) children.
Proof.
  intros d start count; revert start.
  induction count as [|count IH]; intros start code env; simpl.
  - split.
    + intros. exists []. constructor.
    + intros [children Hchildren]. inversion Hchildren; constructor.
  - split.
    + intros Hforms. inversion Hforms as [|f fs Hhead Htail]; subst.
      apply compile_membership_terms_correct in Hhead.
      2: { apply block_terms_length. }
      destruct Hhead as [value [Hdenote Hmatch]].
      apply IH in Htail. destruct Htail as [children Hchildren].
      exists (value :: children). constructor; [split; assumption|exact Hchildren].
    + intros [children Hchildren].
      inversion Hchildren as [|block blocks child children' Hhead Htail]; subst.
      constructor.
      * apply compile_membership_terms_correct.
        -- apply block_terms_length.
        -- exists blocks. exact Hhead.
      * apply IH. exists children'. exact Htail.
Qed.

Lemma block_terms_match_coordinate : forall d env block (value : NVec d)
    coordinate,
    terms_match env (block_terms d block) value ->
    (coordinate < d)%nat ->
    env (block * d + coordinate)%nat =
      Z.of_nat (vector_entry value coordinate).
Proof.
  intros d env block value coordinate [_ Hmatch] Hcoordinate.
  specialize (Hmatch coordinate Hcoordinate).
  unfold block_terms in Hmatch.
  rewrite nth_indep with (d' := Var (block * d + coordinate)%nat) in Hmatch.
  2: { rewrite length_map, seq_length. exact Hcoordinate. }
  rewrite map_nth with (d := coordinate) in Hmatch.
  rewrite seq_nth in Hmatch by exact Hcoordinate. simpl in Hmatch.
  exact Hmatch.
Qed.

Lemma child_sum_term_semantics_with_code : forall d (code : SemiCode d) env
    start count children coordinate,
    List.Forall2 (block_denotes env code) (seq start count) children ->
    (coordinate < d)%nat ->
    term_semantics env (child_sum_term d start count coordinate) =
      Z.of_nat (vector_entry (nvec_rsum children) coordinate).
Proof.
  intros d code env start count; revert start.
  induction count as [|count IH]; intros start children coordinate Hchildren Hcoordinate.
  - inversion Hchildren; subst; simpl.
    rewrite vector_entry_zero by exact Hcoordinate. reflexivity.
  - inversion Hchildren as [|block child blocks children' Hhead Htail]; subst; simpl.
    destruct Hhead as [_ Hmatch].
    rewrite block_terms_match_coordinate with (value := child) by assumption.
    rewrite IH with (children := children'); [|exact Htail|exact Hcoordinate].
    rewrite vector_entry_add by exact Hcoordinate.
    rewrite Nat2Z.inj_add. reflexivity.
Qed.

Lemma zvector_entry_nth_order : forall d (value : ZVec d) coordinate
    (Hcoordinate : (coordinate < d)%nat),
    zvector_entry value coordinate = Vector.nth_order value Hcoordinate.
Proof.
  intros. unfold zvector_entry. symmetry. apply to_list_nth_order.
Qed.

Lemma zvector_entry_add : forall d (left right : ZVec d) coordinate,
    (coordinate < d)%nat ->
    zvector_entry (zvec_add left right) coordinate =
      zvector_entry left coordinate + zvector_entry right coordinate.
Proof.
  intros d left right coordinate Hcoordinate.
  repeat rewrite zvector_entry_nth_order with (Hcoordinate := Hcoordinate).
  unfold zvec_add. apply Vector.nth_map2; reflexivity.
Qed.

Lemma zvector_entry_of_nvec : forall d (value : NVec d) coordinate,
    (coordinate < d)%nat ->
    zvector_entry (nvec_to_zvec value) coordinate =
      Z.of_nat (vector_entry value coordinate).
Proof.
  intros d value coordinate Hcoordinate.
  rewrite zvector_entry_nth_order with (Hcoordinate := Hcoordinate).
  rewrite vector_entry_nth_order with (Hcoordinate := Hcoordinate).
  unfold nvec_to_zvec. apply Vector.nth_map; reflexivity.
Qed.

Lemma result_terms_semantics : forall d (action : Action d) code env children
    coordinate,
    List.Forall2 (block_denotes env code)
      (seq 0 (action_arity action)) children ->
    (coordinate < d)%nat ->
    term_semantics env
      (List.nth coordinate (result_terms action) (Num 0)) =
    zvector_entry
      (zvec_add (action_offset action) (nvec_to_zvec (nvec_sum children)))
      coordinate.
Proof.
  intros d action code env children coordinate Hchildren Hcoordinate.
  unfold result_terms.
  rewrite nth_indep with
    (d' := Plus (Num (zvector_entry (action_offset action) coordinate))
      (child_sum_term d 0 (action_arity action) coordinate)).
  2: { rewrite length_map, seq_length. exact Hcoordinate. }
  rewrite map_nth with (d := coordinate).
  rewrite seq_nth by exact Hcoordinate. simpl.
  rewrite child_sum_term_semantics_with_code with
    (children := children) (code := code); [|exact Hchildren|exact Hcoordinate].
  rewrite nvec_sum_rsum.
  rewrite zvector_entry_add by exact Hcoordinate.
  rewrite zvector_entry_of_nvec by exact Hcoordinate. reflexivity.
Qed.

Definition environment_values (env : environment) (count : nat) : list Z :=
  List.rev (List.map env (seq 0 count)).

Lemma environment_values_length : forall env count,
    length (environment_values env count) = count.
Proof.
  intros. unfold environment_values. rewrite rev_length, length_map, seq_length.
  reflexivity.
Qed.

Lemma environment_values_lookup : forall env count index,
    (index < count)%nat ->
    extend_many empty_environment (environment_values env count) index = env index.
Proof.
  intros env count index Hindex.
  rewrite extend_many_lookup by (rewrite environment_values_length; exact Hindex).
  unfold environment_values. rewrite rev_length, length_map, seq_length.
  rewrite rev_nth.
  2: { rewrite length_map, seq_length. lia. }
  rewrite length_map, seq_length.
  replace (count - S (count - S index))%nat with index by lia.
  rewrite nth_indep with (d' := env index).
  2: { rewrite length_map, seq_length. exact Hindex. }
  rewrite map_nth with (d := index).
  rewrite seq_nth by exact Hindex. reflexivity.
Qed.

Fixpoint children_environment {d} (children : list (NVec d))
    (index : nat) : Z :=
  match children with
  | [] => 0
  | child :: children' =>
      if Nat.ltb index d
      then Z.of_nat (vector_entry child index)
      else children_environment children' (index - d)%nat
  end.

Lemma children_environment_block : forall d (children : list (NVec d))
    block child coordinate,
    List.nth_error children block = Some child ->
    (coordinate < d)%nat ->
    children_environment children (block * d + coordinate)%nat =
      Z.of_nat (vector_entry child coordinate).
Proof.
  intros d children; induction children as [|head children IH];
    intros block child coordinate Hchild Hcoordinate;
    destruct block as [|block]; simpl in *.
  - discriminate.
  - discriminate.
  - inversion Hchild; subst.
    destruct (Nat.ltb_spec coordinate d); [reflexivity|lia].
  - destruct (Nat.ltb_spec (d + block * d + coordinate) d); [nia|].
    replace (d + block * d + coordinate - d)%nat with
      (block * d + coordinate)%nat by nia.
    apply IH with (child := child); assumption.
Qed.

Lemma children_blocks_from_values_aux : forall d (code : SemiCode d)
    (original remaining : list (NVec d)) start,
    remaining = skipn start original ->
    List.Forall (denote code) remaining ->
    List.Forall2
      (block_denotes
        (extend_many empty_environment
          (environment_values (children_environment original)
            (length original * d))) code)
      (seq start (length remaining)) remaining.
Proof.
  intros d code original remaining; induction remaining as [|child remaining IH];
    intros start Hskip Hdenote; simpl.
  - constructor.
  - inversion Hdenote as [|? ? Hchild Htail]; subst.
    constructor.
    + split; [exact Hchild|].
      split; [apply block_terms_length|].
      intros coordinate Hcoordinate.
      unfold block_terms.
      rewrite nth_indep with (d' := Var (start * d + coordinate)%nat).
      2: { rewrite length_map, seq_length. exact Hcoordinate. }
      rewrite map_nth with (d := coordinate).
      rewrite seq_nth by exact Hcoordinate. simpl.
      rewrite environment_values_lookup.
      2: {
        assert (start < length original)%nat.
        { destruct (Nat.lt_ge_cases start (length original)); [assumption|].
          rewrite skipn_all2 in Hskip by assumption. discriminate. }
        nia. }
      apply children_environment_block with (block := start).
      * pose proof (nth_error_skipn start original 0) as Hnth.
        rewrite <- Hskip in Hnth. simpl in Hnth.
        replace (start + 0)%nat with start in Hnth by lia. symmetry. exact Hnth.
      * exact Hcoordinate.
    + apply IH with (start := S start).
      * replace (S start) with (1 + start)%nat by lia.
        rewrite <- (skipn_skipn 1 start original).
        rewrite <- Hskip. reflexivity.
      * exact Htail.
Qed.

Lemma children_blocks_from_values : forall d (code : SemiCode d)
    (children : list (NVec d)),
    List.Forall (denote code) children ->
    List.Forall2
      (block_denotes
        (extend_many empty_environment
          (environment_values (children_environment children)
            (length children * d))) code)
      (seq 0 (length children)) children.
Proof.
  intros d code children Hchildren.
  apply children_blocks_from_values_aux with
    (remaining := children) (start := 0%nat).
  - reflexivity.
  - exact Hchildren.
Qed.

Lemma nonnegative_terms_correct : forall env terms,
    List.Forall (formula_semantics env)
      (List.map (fun value => Le (Num 0) value) terms) <->
    forall index, (index < length terms)%nat ->
      0 <= term_semantics env (List.nth index terms (Num 0)).
Proof.
  intros env terms. split.
  - intros Hforms index Hindex.
    apply (proj1 (List.Forall_forall _ _) Hforms
      (Le (Num 0) (List.nth index terms (Num 0)))).
    apply in_map_iff. exists (List.nth index terms (Num 0)). split; [reflexivity|].
    apply nth_In. exact Hindex.
  - intros Hterms. apply List.Forall_forall. intros f Hin.
    apply in_map_iff in Hin as [value [<- Hin]]. simpl.
    apply In_nth_error in Hin as [index Hindex].
    assert (Hlt : (index < length terms)%nat).
    { apply nth_error_Some. rewrite Hindex. discriminate. }
    specialize (Hterms index Hlt).
    rewrite (@nth_error_nth term terms index value (Num 0) Hindex) in Hterms.
    exact Hterms.
Qed.

Lemma zvec_nonnegative_correct : forall d (value : ZVec d),
    zvec_nonnegative value = true <->
    forall coordinate, (coordinate < d)%nat ->
      0 <= zvector_entry value coordinate.
Proof.
  intros d value. unfold zvec_nonnegative. rewrite forallb_forall. split.
  - intros Hall coordinate Hcoordinate.
    apply Z.geb_le. apply Hall.
    unfold zvector_entry. apply nth_In.
    rewrite length_to_list. exact Hcoordinate.
  - intros Hall item Hin. apply Z.geb_le.
    apply In_nth_error in Hin as [coordinate Hcoordinate].
    assert (Hlt : (coordinate < d)%nat).
    { assert (Hlt_list :
          (coordinate < length (Vector.to_list value))%nat).
      { apply nth_error_Some. rewrite Hcoordinate. discriminate. }
      rewrite length_to_list in Hlt_list. exact Hlt_list. }
    specialize (Hall coordinate Hlt). unfold zvector_entry in Hall.
    rewrite (@nth_error_nth Z (Vector.to_list value) coordinate item 0 Hcoordinate)
      in Hall. exact Hall.
Qed.

Lemma result_nonnegative_correct : forall d (action : Action d) code env children,
    List.Forall2 (block_denotes env code)
      (seq 0 (action_arity action)) children ->
    List.Forall (formula_semantics env)
      (List.map (fun result => Le (Num 0) result) (result_terms action)) <->
    zvec_nonnegative
      (zvec_add (action_offset action) (nvec_to_zvec (nvec_sum children))) = true.
Proof.
  intros d action code env children Hchildren.
  rewrite nonnegative_terms_correct, zvec_nonnegative_correct. split;
    intros H coordinate Hcoordinate.
  - rewrite <- result_terms_semantics with
      (code := code) (env := env) (children := children); try assumption.
    apply H. rewrite result_terms_length. exact Hcoordinate.
  - rewrite result_terms_length in Hcoordinate.
    rewrite result_terms_semantics with
      (code := code) (env := env) (children := children); try assumption.
    apply H. exact Hcoordinate.
Qed.

Lemma result_terms_match_decode : forall d (action : Action d) code env children
    output,
    List.Forall2 (block_denotes env code)
      (seq 0 (action_arity action)) children ->
    zvec_to_nvec
      (zvec_add (action_offset action) (nvec_to_zvec (nvec_sum children))) =
      Some output ->
    terms_match env (result_terms action) output.
Proof.
  intros d action code env children output Hchildren Hdecode.
  split; [apply result_terms_length|].
  intros coordinate Hcoordinate.
  rewrite result_terms_semantics with
    (code := code) (children := children); try assumption.
  rewrite zvector_entry_nth_order with (Hcoordinate := Hcoordinate).
  rewrite vector_entry_nth_order with (Hcoordinate := Hcoordinate).
  exact (zvec_to_nvec_sound d _ output Hdecode
    (Fin.of_nat_lt Hcoordinate)).
Qed.

Lemma forall2_block_denotes_values : forall d env (code : SemiCode d)
    blocks children,
    List.Forall2 (block_denotes env code) blocks children ->
    List.Forall (denote code) children.
Proof.
  intros d env code blocks children H.
  induction H; constructor; [exact (proj1 H)|exact IHForall2].
Qed.

Lemma environment_children_nonnegative : forall d (children : list (NVec d))
    index,
    (index < length children * d)%nat ->
    0 <= children_environment children index.
Proof.
  intros d children; induction children as [|child children IH]; intros index Hindex;
    simpl in *; [lia|].
  destruct (Nat.ltb_spec index d).
  - apply Nat2Z.is_nonneg.
  - apply IH. nia.
Qed.

Theorem action_counterexample_correct : forall d (action : Action d)
    (code : SemiCode d),
    formula_semantics empty_environment (action_counterexample action code) <->
    exists children output,
      length children = action_arity action /\
      List.Forall (denote code) children /\
      apply_action action children = Some output /\
      ~ denote code output.
Proof.
  intros d action code. unfold action_counterexample.
  rewrite exists_many_semantics. split.
  - intros [values [Hvalues Hbody]].
    apply formula_and_semantics in Hbody.
    apply Forall_app in Hbody as [Hvariables Hbody].
    apply Forall_app in Hbody as [Hchildren_forms Hbody].
    apply Forall_app in Hbody as [Hresult_nonnegative Hnot_list].
    inversion Hnot_list as [|? ? Hnot Hnil]; subst.
    apply children_membership_formulas_correct in Hchildren_forms.
    destruct Hchildren_forms as [children Hblocks].
    assert (Hlength : length children = action_arity action).
    { pose proof (Forall2_length Hblocks) as Hlen.
      rewrite seq_length in Hlen. symmetry. exact Hlen. }
    set (raw := zvec_add (action_offset action)
      (nvec_to_zvec (nvec_sum children))).
    assert (Hraw_nonnegative : zvec_nonnegative raw = true).
    { unfold raw. apply (proj1 (result_nonnegative_correct
        d action code (extend_many empty_environment values) children Hblocks)).
      exact Hresult_nonnegative. }
    set (output := Vector.map Z.to_nat raw).
    assert (Hdecode : zvec_to_nvec raw = Some output).
    { unfold zvec_to_nvec, output. rewrite Hraw_nonnegative. reflexivity. }
    exists children, output. repeat split.
    + exact Hlength.
    + eapply forall2_block_denotes_values; exact Hblocks.
    + unfold apply_action. rewrite Hlength, Nat.eqb_refl.
      unfold add_displacement, raw in Hdecode. exact Hdecode.
    + intro Houtput. apply Hnot.
      apply compile_membership_terms_correct.
      * apply result_terms_length.
      * exists output. split; [exact Houtput|].
        apply result_terms_match_decode with
          (code := code) (children := children); assumption.
  - intros [children [output [Hlength [Hchildren [Happly Hexcluded]]]]].
    assert (Hdecode : zvec_to_nvec
      (zvec_add (action_offset action) (nvec_to_zvec (nvec_sum children))) =
      Some output).
    { unfold apply_action in Happly. rewrite Hlength, Nat.eqb_refl in Happly.
      unfold add_displacement in Happly. exact Happly. }
    pose proof (children_blocks_from_values d code children Hchildren) as Hblocks.
    rewrite Hlength in Hblocks.
    exists (environment_values (children_environment children)
      (action_arity action * d)). split.
    + apply environment_values_length.
    + apply formula_and_semantics. apply Forall_app. split.
      * apply (proj2 (nonnegative_formulas_correct
          (action_arity action * d)
          (extend_many empty_environment
            (environment_values (children_environment children)
              (action_arity action * d))))).
        intros index Hindex. rewrite environment_values_lookup by exact Hindex.
        apply environment_children_nonnegative. rewrite Hlength. exact Hindex.
      * apply Forall_app. split.
        -- apply children_membership_formulas_correct. exists children. exact Hblocks.
        -- apply Forall_app. split.
           ++ apply (proj2 (result_nonnegative_correct d action code _ children Hblocks)).
              unfold zvec_to_nvec in Hdecode.
              destruct (zvec_nonnegative
                (zvec_add (action_offset action)
                  (nvec_to_zvec (nvec_sum children)))) eqn:Hnonnegative;
                [reflexivity|discriminate].
           ++ constructor.
              ** simpl. intro Hmember.
                 apply compile_membership_terms_correct in Hmember.
                 2: { apply result_terms_length. }
                 destruct Hmember as [candidate [Hcandidate Hcandidate_match]].
                 assert (Houtput_match : terms_match
                   (extend_many empty_environment
                     (environment_values (children_environment children)
                       (action_arity action * d)))
                   (result_terms action) output).
                 { apply result_terms_match_decode with
                     (code := code) (children := children); assumption. }
                 apply Hexcluded.
                 assert (candidate = output).
                 { apply nvec_ext_entry. intros coordinate Hcoordinate.
                   destruct Hcandidate_match as [_ Hcandidate_at].
                   destruct Houtput_match as [_ Houtput_at].
                   specialize (Hcandidate_at coordinate Hcoordinate).
                   specialize (Houtput_at coordinate Hcoordinate). lia. }
                 subst. exact Hcandidate.
              ** constructor.
Qed.

Theorem check_action_closed_correct : forall d (action : Action d) code,
    check_action_closed action code = true <->
    forall children output,
      length children = action_arity action ->
      List.Forall (denote code) children ->
      apply_action action children = Some output ->
      denote code output.
Proof.
  intros d action code. unfold check_action_closed. rewrite negb_true_iff.
  destruct (decide_closed_formula (action_counterexample action code)) eqn:Hcheck.
  - split; [discriminate|]. intros Hclosed.
    exfalso. apply (proj1 (decide_closed_formula_correct _
      (action_counterexample_closed d action code))) in Hcheck.
    apply action_counterexample_correct in Hcheck.
    destruct Hcheck as [children [output [Hlength [Hchildren [Happly Hnot]]]]].
    apply Hnot. eapply Hclosed; eauto.
  - split.
    + intros _ children output Hlength Hchildren Happly.
      destruct (classic (denote code output)) as [Hdenote|Hnot]; [exact Hdenote|].
      exfalso.
      assert (Hcounter : formula_semantics empty_environment
        (action_counterexample action code)).
      { apply action_counterexample_correct.
        exists children, output. repeat split; assumption. }
      apply (proj2 (decide_closed_formula_correct _
        (action_counterexample_closed d action code))) in Hcounter.
      congruence.
    + intros. reflexivity.
Qed.

Lemma apply_action_length : forall d (action : Action d) children output,
    apply_action action children = Some output ->
    length children = action_arity action.
Proof.
  intros d action children output Happly. unfold apply_action in Happly.
  destruct (Nat.eqb (length children) (action_arity action)) eqn:Hlength;
    [apply Nat.eqb_eq; exact Hlength|discriminate].
Qed.

Theorem check_actions_correct : forall d (S : IBVAS d) code,
    check_actions S code = true <-> Closed S (denote code).
Proof.
  intros d S code. unfold check_actions, Closed. rewrite forallb_forall. split.
  - intros Hall action children output Haction Hchildren Happly.
    pose proof (proj1 (check_action_closed_correct d action code)
      (Hall action Haction)) as Hclosed.
    eapply Hclosed.
    + eapply apply_action_length; eauto.
    + exact Hchildren.
    + exact Happly.
  - intros Hclosed action Haction.
    apply (proj2 (check_action_closed_correct d action code)).
    intros children output Hlength Hchildren Happly.
    eapply Hclosed; eauto.
Qed.

Theorem check_invariantP_correct : forall d (S : IBVAS d) code target,
    check_invariantP S code target = true <->
    invariant_obligation S code target.
Proof.
  intros d S code target. unfold check_invariantP, invariant_obligation.
  repeat rewrite Bool.andb_true_iff.
  rewrite check_initials_correct, check_actions_correct,
    check_target_excluded_correct. tauto.
Qed.

Lemma invariant_contains_reachable : forall d (S : IBVAS d) P,
    InitialIncluded S P -> Closed S P ->
    forall value, Reach S value -> P value.
Proof.
  intros d S P Hinitial Hclosed.
  apply (Reach_ind' d S
    (fun value _ => P value)
    (fun values _ => List.Forall P values)).
  - intros index value Hlookup. apply Hinitial.
    eapply nth_error_In; eauto.
  - intros index action children value Hlookup Hreaches Hchildren Happly.
    eapply Hclosed; eauto. eapply nth_error_In; eauto.
  - constructor.
  - intros value values Hreach Hvalue Hreaches Hvalues.
    constructor; assumption.
Qed.

Theorem check_invariant_sound : forall d (S : IBVAS d) code target,
    check_invariantP S code target = true ->
    ~ Reach S target.
Proof.
  intros d S code target Hcheck Hreach.
  apply check_invariantP_correct in Hcheck.
  destruct Hcheck as [Hinitial [Hclosed Hexcluded]].
  apply Hexcluded. eapply invariant_contains_reachable; eauto.
Qed.
