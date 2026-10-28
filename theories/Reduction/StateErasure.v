From Coq Require Import List Vector VectorSpec ZArith Lia
  Sorting.Permutation.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import System Runs RunOrder.
From Mell.BVASS Require Import Stateful.

Import ListNotations.

Fixpoint vector_of_function {A} (n : nat) : (Fin.t n -> A) -> Vector.t A n :=
  match n as count return (Fin.t count -> A) -> Vector.t A count with
  | 0 => fun _ => Vector.nil A
  | S count => fun f => Vector.cons A (f Fin.F1) count
      (vector_of_function count (fun index => f (Fin.FS index)))
  end.

Lemma nth_vector_of_function : forall A n (f : Fin.t n -> A) index,
    Vector.nth (vector_of_function n f) index = f index.
Proof.
  intros A n. induction n as [|n IH]; intros f index.
  - inversion index.
  - refine (Fin.caseS' index
      (fun i => Vector.nth (vector_of_function (S n) f) i = f i)
      eq_refl _).
    intro tail_index. cbn. apply IH.
Qed.

Definition one_hot_nat (n index : nat) : NVec n :=
  vector_of_function n (fun position =>
    if Nat.eqb (proj1_sig (Fin.to_nat position)) index then 1 else 0).

Definition one_hot_z (n index : nat) : ZVec n :=
  vector_of_function n (fun position =>
    if Nat.eqb (proj1_sig (Fin.to_nat position)) index then 1%Z else 0%Z).

Definition one_hot_state {q} (state : Fin.t q) : NVec q :=
  vector_of_function q
    (fun position => if Fin.eq_dec position state then 1 else 0).

Definition state_debit {q} (states : list (Fin.t q)) : ZVec q :=
  vector_of_function q (fun state =>
    (- Z.of_nat (List.count_occ Fin.eq_dec states state))%Z).

Definition state_credit {q} (state : Fin.t q) : ZVec q :=
  vector_of_function q
    (fun position => if Fin.eq_dec position state then 1%Z else 0%Z).

Definition gate_debit (count index : nat) : ZVec count :=
  Vector.map Z.opp (one_hot_z count index).

Lemma nvec_add_append : forall n m
    (left1 left2 : NVec n) (right1 right2 : NVec m),
    nvec_add (Vector.append left1 right1) (Vector.append left2 right2) =
    Vector.append (nvec_add left1 left2) (nvec_add right1 right2).
Proof.
  intros n m left1. induction left1 as [|x n left1 IH];
    intros left2 right1 right2.
  - refine (Vector.case0 (fun left2 =>
      nvec_add (Vector.append (Vector.nil nat) right1)
        (Vector.append left2 right2) =
      Vector.append (nvec_add (Vector.nil nat) left2)
        (nvec_add right1 right2)) _ left2).
    reflexivity.
  - refine (Vector.caseS' left2 (fun left2 =>
      nvec_add (Vector.append (@Vector.cons nat x n left1) right1)
        (Vector.append left2 right2) =
      Vector.append (nvec_add (@Vector.cons nat x n left1) left2)
        (nvec_add right1 right2)) _).
    intros y tail. cbn. f_equal. apply IH.
Qed.

Lemma zvec_add_append : forall n m
    (left1 left2 : ZVec n) (right1 right2 : ZVec m),
    zvec_add (Vector.append left1 right1) (Vector.append left2 right2) =
    Vector.append (zvec_add left1 left2) (zvec_add right1 right2).
Proof.
  intros n m left1. induction left1 as [|x n left1 IH];
    intros left2 right1 right2.
  - refine (Vector.case0 (fun left2 =>
      zvec_add (Vector.append (Vector.nil Z) right1)
        (Vector.append left2 right2) =
      Vector.append (zvec_add (Vector.nil Z) left2)
        (zvec_add right1 right2)) _ left2).
    reflexivity.
  - refine (Vector.caseS' left2 (fun left2 =>
      zvec_add (Vector.append (@Vector.cons Z x n left1) right1)
        (Vector.append left2 right2) =
      Vector.append (zvec_add (@Vector.cons Z x n left1) left2)
        (zvec_add right1 right2)) _).
    intros y tail. cbn. f_equal. apply IH.
Qed.

Lemma nvec_to_zvec_append : forall n m (left : NVec n) (right : NVec m),
    nvec_to_zvec (Vector.append left right) =
    Vector.append (nvec_to_zvec left) (nvec_to_zvec right).
Proof. intros. unfold nvec_to_zvec. apply map_append. Qed.

Lemma nvec_zero_add : forall n (value : NVec n),
    nvec_add (nvec_zero n) value = value.
Proof.
  intros n value. apply (proj1 (Vector.eq_nth_iff nat n _ _)).
  intros index index' Heq; subst index'. unfold nvec_add, nvec_zero.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (const_nth nat 0 n index). lia.
Qed.

Lemma nvec_add_zero : forall n (value : NVec n),
    nvec_add value (nvec_zero n) = value.
Proof.
  intros n value. apply (proj1 (Vector.eq_nth_iff nat n _ _)).
  intros index index' Heq; subst index'. unfold nvec_add, nvec_zero.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl),
    (const_nth nat 0 n index). lia.
Qed.

Lemma nvec_add_assoc_local : forall n (x y z : NVec n),
    nvec_add (nvec_add x y) z = nvec_add x (nvec_add y z).
Proof.
  intros n x y z. apply (proj1 (Vector.eq_nth_iff nat n _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Fixpoint nvec_rsum_local {n} (values : list (NVec n)) : NVec n :=
  match values with
  | [] => nvec_zero n
  | value :: tail => nvec_add value (nvec_rsum_local tail)
  end.

Lemma fold_left_nvec_add_local : forall n (values : list (NVec n)) acc,
    List.fold_left nvec_add values acc = nvec_add acc (nvec_rsum_local values).
Proof.
  intros n values. induction values as [|value values IH]; intro acc; cbn.
  - symmetry. apply nvec_add_zero.
  - rewrite IH, nvec_add_assoc_local. reflexivity.
Qed.

Lemma nvec_sum_local : forall n (values : list (NVec n)),
    nvec_sum values = nvec_rsum_local values.
Proof.
  intros n values. unfold nvec_sum. rewrite fold_left_nvec_add_local.
  apply nvec_zero_add.
Qed.

Definition state_count {q} (states : list (Fin.t q)) : NVec q :=
  vector_of_function q (fun state => List.count_occ Fin.eq_dec states state).

Lemma state_count_cons : forall q (state : Fin.t q) states,
    state_count (state :: states) =
    nvec_add (one_hot_state state) (state_count states).
Proof.
  intros q state states. apply (proj1 (Vector.eq_nth_iff nat q _ _)).
  intros index index' Heq; subst index'.
  unfold state_count, one_hot_state, nvec_add.
  rewrite (nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  repeat rewrite nth_vector_of_function. cbn.
  destruct (Fin.eq_dec index state), (Fin.eq_dec state index); subst;
    try congruence; cbn; lia.
Qed.

Lemma state_count_permutation : forall q (left right : list (Fin.t q)),
    Permutation left right -> state_count left = state_count right.
Proof.
  intros q left right Hperm. apply (proj1 (Vector.eq_nth_iff nat q _ _)).
  intros index index' Heq; subst index'. unfold state_count.
  repeat rewrite nth_vector_of_function.
  exact ((proj1 (Permutation_count_occ Fin.eq_dec left right)) Hperm index).
Qed.

Lemma state_count_nil : forall q, @state_count q [] = nvec_zero q.
Proof.
  intro q. apply (proj1 (Vector.eq_nth_iff nat q _ _)).
  intros index index' Heq; subst index'. unfold state_count, nvec_zero.
  rewrite nth_vector_of_function, (const_nth nat 0 q index). reflexivity.
Qed.

Lemma nvec_zero_append : forall n m,
    nvec_zero (n + m) = Vector.append (nvec_zero n) (nvec_zero m).
Proof.
  intros n m. induction n; cbn; [reflexivity|]. f_equal. exact IHn.
Qed.

Definition encode_state_config {d q} (S : SBVAS d q)
    (state : Fin.t q) (counters : NVec d) :
    NVec (d + q + length (stateful_rules S)) :=
  Vector.append (Vector.append counters
    (one_hot_state state))
    (nvec_zero (length (stateful_rules S))).

Definition encode_gate_config {d q} (S : SBVAS d q)
    (index : nat) (counters : NVec d) :
    NVec (d + q + length (stateful_rules S)) :=
  Vector.append (Vector.append counters (nvec_zero q))
    (one_hot_nat (length (stateful_rules S)) index).

Definition erase_front_action {d q} (S : SBVAS d q)
    (index : nat) (rule : SRule d q) :
    Action (d + q + length (stateful_rules S)).
Proof.
  refine {| action_arity := length (input_states rule);
            action_offset :=
              Vector.append (Vector.append (rule_delta rule)
                (state_debit (input_states rule)))
                (one_hot_z (length (stateful_rules S)) index) |}.
  destruct (input_states rule) eqn:Hinputs.
  - exfalso. apply (input_nonempty rule). exact Hinputs.
  - cbn. lia.
Defined.

Definition erase_back_action {d q} (S : SBVAS d q)
    (index : nat) (rule : SRule d q) :
    Action (d + q + length (stateful_rules S)) :=
  {| action_arity := 1;
     action_arity_positive := Nat.lt_0_succ 0;
     action_offset :=
       Vector.append (Vector.append (zvec_zero d)
         (state_credit (output_state rule)))
         (gate_debit (length (stateful_rules S)) index) |}.

Fixpoint erase_rule_actions {d q} (S : SBVAS d q)
    (index : nat) (rules : list (SRule d q)) :
    list (Action (d + q + length (stateful_rules S))) :=
  match rules with
  | [] => []
  | rule :: tail =>
      erase_front_action S index rule :: erase_back_action S index rule ::
      erase_rule_actions S (Nat.succ index) tail
  end.

Definition erase_states {d q} (S : SBVAS d q) :
    IBVAS (d + q + length (stateful_rules S)) :=
  {| initial_vectors := List.map (fun config =>
       encode_state_config S (fst config) (snd config)) (initial_configs S);
     system_actions := erase_rule_actions S 0 (stateful_rules S) |}.

Lemma sum_encoded_configs : forall d q (S : SBVAS d q)
    (configs : list (SConfig d q)),
    nvec_sum (List.map (fun config =>
      encode_state_config S (fst config) (snd config)) configs) =
    Vector.append
      (Vector.append (nvec_sum (List.map snd configs))
        (state_count (List.map fst configs)))
      (nvec_zero (length (stateful_rules S))).
Proof.
  intros d q S configs. repeat rewrite nvec_sum_local.
  induction configs as [|[state counters] configs IH]; cbn.
  - rewrite state_count_nil. repeat rewrite <- nvec_zero_append. reflexivity.
  - rewrite IH. unfold encode_state_config.
    rewrite nvec_add_append, nvec_add_append, state_count_cons,
      nvec_zero_add. reflexivity.
Qed.

Lemma apply_action_of_exact : forall n (action : Action n) children target,
    length children = action_arity action ->
    zvec_add (action_offset action) (nvec_to_zvec (nvec_sum children)) =
      nvec_to_zvec target ->
    apply_action action children = Some target.
Proof.
  intros n action children target Hlength Hexact.
  unfold apply_action. apply Nat.eqb_eq in Hlength. rewrite Hlength.
  unfold add_displacement. rewrite Hexact. apply zvec_to_nvec_of_nvec.
Qed.

Lemma apply_action_length : forall n (action : Action n) children target,
    apply_action action children = Some target ->
    List.length children = action_arity action.
Proof.
  intros n action children target Happly. unfold apply_action in Happly.
  destruct (Nat.eqb (List.length children) (action_arity action)) eqn:Harity;
    [now apply Nat.eqb_eq|discriminate].
Qed.

Lemma state_debit_cancels : forall q states,
    zvec_add (state_debit states) (nvec_to_zvec (state_count states)) =
    zvec_zero q.
Proof.
  intros q states. apply (proj1 (Vector.eq_nth_iff Z q _ _)).
  intros index index' Heq; subst index'.
  unfold state_debit, state_count, zvec_add, nvec_to_zvec, zvec_zero.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (nth_map Z.of_nat _ index index eq_refl),
    (const_nth Z 0%Z q index).
  repeat rewrite nth_vector_of_function. lia.
Qed.

Lemma add_displacement_exact : forall d (offset : ZVec d) children result,
    add_displacement offset children = Some result ->
    zvec_add offset (nvec_to_zvec (nvec_sum children)) =
      nvec_to_zvec result.
Proof.
  intros d offset children result H.
  apply (proj1 (Vector.eq_nth_iff Z d _ _)).
  intros index index' Heq; subst index'.
  unfold nvec_to_zvec.
  rewrite (nth_map Z.of_nat result index index eq_refl).
  eapply zvec_to_nvec_sound; exact H.
Qed.

Lemma zvec_zero_add : forall n (value : ZVec n),
    zvec_add (zvec_zero n) value = value.
Proof.
  intros n value. apply (proj1 (Vector.eq_nth_iff Z n _ _)).
  intros index index' Heq; subst index'. unfold zvec_add, zvec_zero.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (const_nth Z 0%Z n index). lia.
Qed.

Lemma zvec_add_zero : forall n (value : ZVec n),
    zvec_add value (zvec_zero n) = value.
Proof.
  intros n value. apply (proj1 (Vector.eq_nth_iff Z n _ _)).
  intros index index' Heq; subst index'. unfold zvec_add, zvec_zero.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (const_nth Z 0%Z n index). lia.
Qed.

Lemma nvec_to_zvec_zero : forall n,
    nvec_to_zvec (nvec_zero n) = zvec_zero n.
Proof.
  intro n. apply (proj1 (Vector.eq_nth_iff Z n _ _)).
  intros index index' Heq; subst index'.
  unfold nvec_to_zvec, nvec_zero, zvec_zero.
  rewrite (nth_map Z.of_nat _ index index eq_refl).
  repeat rewrite (const_nth _ _ n index). reflexivity.
Qed.

Lemma one_hot_z_of_nat : forall n index,
    nvec_to_zvec (one_hot_nat n index) = one_hot_z n index.
Proof.
  intros n index. apply (proj1 (Vector.eq_nth_iff Z n _ _)).
  intros position position' Heq; subst position'.
  unfold nvec_to_zvec, one_hot_nat, one_hot_z.
  rewrite (nth_map Z.of_nat _ position position eq_refl).
  repeat rewrite nth_vector_of_function.
  destruct (Nat.eqb _ index); reflexivity.
Qed.

Lemma state_credit_of_nat : forall q (state : Fin.t q),
    nvec_to_zvec (one_hot_state state) = state_credit state.
Proof.
  intros q state. apply (proj1 (Vector.eq_nth_iff Z q _ _)).
  intros position position' Heq; subst position'.
  unfold nvec_to_zvec, one_hot_state, state_credit.
  rewrite (nth_map Z.of_nat _ position position eq_refl).
  repeat rewrite nth_vector_of_function.
  destruct (Fin.eq_dec position state); reflexivity.
Qed.

Lemma gate_debit_cancels : forall count index,
    zvec_add (gate_debit count index)
      (nvec_to_zvec (one_hot_nat count index)) = zvec_zero count.
Proof.
  intros count index. rewrite one_hot_z_of_nat.
  apply (proj1 (Vector.eq_nth_iff Z count _ _)).
  intros position position' Heq; subst position'.
  unfold gate_debit, zvec_add, zvec_zero.
  rewrite (nth_map2 Z.add _ _ position position position eq_refl eq_refl),
    (nth_map Z.opp _ position position eq_refl),
    (const_nth Z 0%Z count position). lia.
Qed.

Lemma erase_front_apply : forall d q (S : SBVAS d q) index rule configs result,
    Permutation (List.map fst configs) (input_states rule) ->
    add_displacement (rule_delta rule) (List.map snd configs) = Some result ->
    apply_action (erase_front_action S index rule)
      (List.map (fun config =>
        encode_state_config S (fst config) (snd config)) configs) =
      Some (encode_gate_config S index result).
Proof.
  intros d q S index rule configs result Hstates Happly.
  apply apply_action_of_exact.
  - rewrite map_length. apply Permutation_length in Hstates.
    rewrite map_length in Hstates. exact Hstates.
  - cbn [erase_front_action action_offset].
    rewrite sum_encoded_configs, nvec_to_zvec_append,
      nvec_to_zvec_append, zvec_add_append, zvec_add_append.
    rewrite (state_count_permutation q _ _ Hstates), state_debit_cancels.
    rewrite (add_displacement_exact d _ _ _ Happly).
    unfold encode_gate_config. repeat rewrite nvec_to_zvec_append.
    rewrite one_hot_z_of_nat. repeat rewrite nvec_to_zvec_zero.
    rewrite zvec_add_zero.
    reflexivity.
Qed.

Lemma erase_back_apply : forall d q (S : SBVAS d q) index rule counters,
    apply_action (erase_back_action S index rule)
      [encode_gate_config S index counters] =
    Some (encode_state_config S (output_state rule) counters).
Proof.
  intros d q S index rule counters. apply apply_action_of_exact; [reflexivity|].
  cbn [erase_back_action action_offset]. rewrite nvec_sum_local; cbn.
  rewrite nvec_add_zero.
  unfold encode_gate_config, encode_state_config.
  repeat rewrite nvec_to_zvec_append.
  repeat rewrite zvec_add_append.
  repeat rewrite nvec_to_zvec_zero.
  rewrite state_credit_of_nat, zvec_zero_add, zvec_add_zero,
    gate_debit_cancels.
  reflexivity.
Qed.

Lemma erase_rule_actions_nth : forall d q (S : SBVAS d q) rules start
    position rule,
    nth_error rules position = Some rule ->
    List.In (erase_front_action S (start + position) rule)
      (erase_rule_actions S start rules) /\
    List.In (erase_back_action S (start + position) rule)
      (erase_rule_actions S start rules).
Proof.
  intros d q S rules. induction rules as [|head tail IH];
    intros start position rule Hnth.
  - destruct position; discriminate.
  - destruct position as [|position]; cbn in Hnth.
    + inversion Hnth; subst. cbn. replace (start + 0) with start by lia.
      split; auto.
    + cbn. specialize (IH (Nat.succ start) position rule Hnth).
      rewrite Nat.add_succ_r. cbn. destruct IH as [IHfront IHback].
      split; right; right; assumption.
Qed.

Lemma erase_rule_actions_in : forall d q (S : SBVAS d q) action rules start,
    List.In action (erase_rule_actions S start rules) ->
    exists position rule,
      nth_error rules position = Some rule /\
      (action = erase_front_action S (start + position) rule \/
       action = erase_back_action S (start + position) rule).
Proof.
  intros d q S action rules. induction rules as [|head tail IH];
    intros start Hin; cbn in Hin.
  - contradiction.
  - destruct Hin as [<-|[<-|Hin]].
    + exists 0, head. cbn. replace (start + 0) with start by lia. auto.
    + exists 0, head. cbn. replace (start + 0) with start by lia. auto.
    + destruct (IH (Nat.succ start) Hin) as
        [position [rule [Hnth Hshape]]].
      exists (Nat.succ position), rule. cbn. split; [exact Hnth|].
      rewrite Nat.add_succ_r. cbn. exact Hshape.
Qed.

Lemma sreach_erased_mut : forall d q (S : SBVAS d q),
  (forall state counters, SReach S state counters ->
    Reach (erase_states S) (encode_state_config S state counters)) /\
  (forall configs, SReachChildren S configs ->
    ReachChildren (erase_states S)
      (List.map (fun config =>
        encode_state_config S (fst config) (snd config)) configs)).
Proof.
  intros d q S. apply SReach_mutind.
  - intros state counters Hinitial.
    assert (Hin : List.In (encode_state_config S state counters)
        (initial_vectors (erase_states S))).
    { cbn. apply in_map_iff. exists (state, counters).
      split; [reflexivity|exact Hinitial]. }
    apply in_split in Hin. destruct Hin as [before [after Heq]].
    eapply reach_initial with (index := length before).
    rewrite Heq, nth_error_app2; [|lia].
    replace (length before - length before) with 0 by lia. reflexivity.
  - intros rule configs result Hrule Hchildren IHchildren Hstates Happly.
    apply In_nth_error in Hrule. destruct Hrule as [position Hposition].
    pose proof (erase_rule_actions_nth d q S (stateful_rules S) 0
      position rule Hposition) as [Hfront Hback].
    apply In_nth_error in Hfront. destruct Hfront as [front_index Hfront].
    apply In_nth_error in Hback. destruct Hback as [back_index Hback].
    eapply reach_action with (index := back_index)
      (action := erase_back_action S position rule)
      (children := [encode_gate_config S position result]).
    + exact Hback.
    + constructor.
      * eapply reach_action with (index := front_index)
          (action := erase_front_action S position rule)
          (children := List.map (fun config =>
            encode_state_config S (fst config) (snd config)) configs).
        -- exact Hfront.
        -- exact IHchildren.
        -- now apply erase_front_apply.
      * constructor.
    + apply erase_back_apply.
  - constructor.
  - intros state counters configs Hreach IHreach Hchildren IHchildren.
    cbn. constructor; assumption.
Qed.

Theorem sreach_erased : forall d q (S : SBVAS d q) state counters,
    SReach S state counters ->
    Reach (erase_states S) (encode_state_config S state counters).
Proof. intros; eapply (proj1 (sreach_erased_mut d q S)); eauto. Qed.

Fixpoint nvec_total {n} (value : NVec n) : nat :=
  match value with
  | Vector.nil _ => 0
  | Vector.cons _ head _ tail => head + nvec_total tail
  end.

Lemma nvec_total_zero : forall n, nvec_total (nvec_zero n) = 0.
Proof. intro n. induction n; cbn; auto. Qed.

Lemma nvec_total_add : forall n (left right : NVec n),
    nvec_total (nvec_add left right) = nvec_total left + nvec_total right.
Proof.
  intros n left. induction left as [|head n tail IH]; intros right.
  - refine (Vector.case0 (fun right =>
      nvec_total (nvec_add (Vector.nil nat) right) =
      nvec_total (Vector.nil nat) + nvec_total right) _ right).
    reflexivity.
  - refine (Vector.caseS' right (fun right =>
      nvec_total (nvec_add (@Vector.cons nat head n tail) right) =
      nvec_total (@Vector.cons nat head n tail) + nvec_total right) _).
    intros other rest. cbn. rewrite IH. lia.
Qed.

Lemma nvec_total_vector_zero : forall n,
    nvec_total (vector_of_function n (fun _ => 0)) = 0.
Proof. intro n. induction n; cbn; auto. Qed.

Lemma nvec_total_no_F1 : forall n,
    nvec_total (vector_of_function n
      (fun position => if Fin.eq_dec (Fin.FS position) Fin.F1 then 1 else 0)) = 0.
Proof.
  intro n. induction n; cbn; auto.
Qed.

Lemma one_hot_state_total : forall q (state : Fin.t q),
    nvec_total (one_hot_state state) = 1.
Proof.
  intros q state. induction state as [q|q state IH].
  - cbn [one_hot_state vector_of_function].
    destruct (Fin.eq_dec Fin.F1 Fin.F1); [|contradiction].
    cbn. rewrite nvec_total_vector_zero. reflexivity.
  - cbn [one_hot_state vector_of_function] in IH |- *.
    destruct (Fin.eq_dec Fin.F1 (Fin.FS state)) as [Heq|Hneq].
    + discriminate Heq.
    + cbn.
      assert (Htail : vector_of_function q
          (fun position : Fin.t q =>
            if Fin.eq_dec (Fin.FS position) (Fin.FS state) then 1 else 0) =
          vector_of_function q
            (fun position => if Fin.eq_dec position state then 1 else 0)).
      { apply (proj1 (Vector.eq_nth_iff nat q _ _)).
        intros index index' Heq'; subst index'. repeat rewrite nth_vector_of_function.
        destruct (Fin.eq_dec (Fin.FS index) (Fin.FS state)) as [Hfs|Hnfs];
          destruct (Fin.eq_dec index state) as [Hi|Hni].
        - reflexivity.
        - exfalso. apply Hni. now apply Fin.FS_inj in Hfs.
        - exfalso. apply Hnfs. now subst index.
        - reflexivity. }
      rewrite Htail. exact IH.
Qed.

Lemma state_count_total : forall q (states : list (Fin.t q)),
    nvec_total (state_count states) = List.length states.
Proof.
  intros q states. induction states as [|state states IH].
  - rewrite state_count_nil, nvec_total_zero. reflexivity.
  - rewrite state_count_cons, nvec_total_add, one_hot_state_total, IH.
    cbn. lia.
Qed.

Inductive ErasedTag (q : nat) :=
| normal_tag : Fin.t q -> ErasedTag q
| gate_tag : nat -> ErasedTag q.

Arguments normal_tag {q} _.
Arguments gate_tag {q} _.

Definition TaggedConfig (d q : nat) := (ErasedTag q * NVec d)%type.

Definition encode_tagged {d q} (S : SBVAS d q) (item : TaggedConfig d q) :=
  match fst item with
  | normal_tag state => encode_state_config S state (snd item)
  | gate_tag index => encode_gate_config S index (snd item)
  end.

Lemma map_encode_tagged_normal : forall d q (S : SBVAS d q)
    (configs : list (SConfig d q)),
    List.map (encode_tagged S)
      (List.map (fun config => (normal_tag (fst config), snd config)) configs) =
    List.map (fun config =>
      encode_state_config S (fst config) (snd config)) configs.
Proof.
  intros d q S configs. induction configs as [|[state counters] configs IH];
    cbn; [reflexivity|]. f_equal. exact IH.
Qed.

Fixpoint tagged_states {d q} (items : list (TaggedConfig d q)) : list (Fin.t q) :=
  match items with
  | [] => []
  | (normal_tag state, _) :: tail => state :: tagged_states tail
  | (gate_tag _, _) :: tail => tagged_states tail
  end.

Fixpoint tagged_counters {d q} (items : list (TaggedConfig d q)) : list (NVec d) :=
  match items with
  | [] => []
  | (_, counters) :: tail => counters :: tagged_counters tail
  end.

Fixpoint tagged_gates {d q} (S : SBVAS d q)
    (items : list (TaggedConfig d q)) : NVec (length (stateful_rules S)) :=
  match items with
  | [] => nvec_zero _
  | (normal_tag _, _) :: tail => tagged_gates S tail
  | (gate_tag index, _) :: tail =>
      nvec_add (one_hot_nat (length (stateful_rules S)) index)
        (tagged_gates S tail)
  end.

Lemma sum_encoded_tagged : forall d q (S : SBVAS d q) items,
    nvec_sum (List.map (encode_tagged S) items) =
    Vector.append
      (Vector.append (nvec_sum (tagged_counters items))
        (state_count (tagged_states items)))
      (tagged_gates S items).
Proof.
  intros d q S items. repeat rewrite nvec_sum_local.
  induction items as [|[tag counters] items IH]; cbn.
  - rewrite state_count_nil. repeat rewrite <- nvec_zero_append. reflexivity.
  - destruct tag as [state|index]; cbn.
    + rewrite IH. unfold encode_tagged, encode_state_config.
      rewrite nvec_add_append, nvec_add_append, state_count_cons,
        nvec_zero_add. reflexivity.
    + rewrite IH. unfold encode_tagged, encode_gate_config.
      rewrite nvec_add_append, nvec_add_append, nvec_zero_add.
      reflexivity.
Qed.

Lemma nvec_total_mono : forall n (left right : NVec n),
    (forall index, Vector.nth left index <= Vector.nth right index) ->
    nvec_total left <= nvec_total right.
Proof.
  intros n left. induction left as [|head n tail IH]; intros right.
  - refine (Vector.case0 (fun right =>
      (forall index, Vector.nth (Vector.nil nat) index <=
        Vector.nth right index) ->
      nvec_total (Vector.nil nat) <= nvec_total right) _ right).
    intro Hle. cbn. lia.
  - refine (Vector.caseS' right (fun right =>
      (forall index, Vector.nth (@Vector.cons nat head n tail) index <=
        Vector.nth right index) ->
      nvec_total (@Vector.cons nat head n tail) <= nvec_total right) _).
    intros h rest Hle. cbn.
    assert (Hhead : head <= h).
    { exact (Hle Fin.F1). }
    assert (Htail : nvec_total tail <= nvec_total rest).
    { apply IH. intro index. exact (Hle (Fin.FS index)). }
    lia.
Qed.

Lemma state_debit_bound : forall (q : nat)
    (required observed : list (Fin.t q)) (output : NVec q),
    zvec_add (state_debit required) (nvec_to_zvec (state_count observed)) =
      nvec_to_zvec output ->
    List.length required <= List.length observed.
Proof.
  intros q required observed output Heq.
  rewrite <- (state_count_total q required), <- (state_count_total q observed).
  apply nvec_total_mono. intro index.
  pose proof (f_equal (fun value => Vector.nth value index) Heq) as Hindex.
  unfold state_debit, state_count, zvec_add, nvec_to_zvec in Hindex.
  rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
    (nth_map Z.of_nat _ index index eq_refl),
    (nth_map Z.of_nat output index index eq_refl) in Hindex.
  repeat rewrite nth_vector_of_function in Hindex.
  unfold state_count. repeat rewrite nth_vector_of_function. lia.
Qed.

Lemma tagged_states_length_le : forall d q (items : list (TaggedConfig d q)),
    List.length (tagged_states items) <= List.length items.
Proof.
  intros d q items. induction items as [|[tag counters] items IH]; cbn; [lia|].
  destruct tag; cbn; lia.
Qed.

Lemma tagged_all_normal : forall d q (items : list (TaggedConfig d q)),
    List.length (tagged_states items) = List.length items ->
    exists configs : list (SConfig d q),
      items = List.map (fun config => (normal_tag (fst config), snd config)) configs.
Proof.
  intros d q items. induction items as [|[tag counters] items IH]; intro Hlen.
  - exists []; reflexivity.
  - destruct tag as [state|index]; cbn in Hlen.
    + destruct (IH ltac:(lia)) as [configs ->].
      exists ((state, counters) :: configs). reflexivity.
    + pose proof (tagged_states_length_le d q items). cbn in Hlen. lia.
Qed.

Lemma vector_three_parts : forall A d q g (value : Vector.t A (d + q + g)),
    exists counters states gates,
      value = Vector.append (Vector.append counters states) gates.
Proof.
  intros A d q g value.
  destruct (Vector.splitat (d + q) value) as [prefix gates] eqn:Houter.
  destruct (Vector.splitat d prefix) as [counters states] eqn:Hinner.
  exists counters, states, gates.
  apply Vector.append_splitat in Houter.
  apply Vector.append_splitat in Hinner. subst prefix value. reflexivity.
Qed.

Lemma erase_front_state_equation : forall d q (S : SBVAS d q)
    index rule items value,
    apply_action (erase_front_action S index rule)
      (List.map (encode_tagged S) items) = Some value ->
    exists output_states : NVec q,
      zvec_add (state_debit (input_states rule))
        (nvec_to_zvec (state_count (tagged_states items))) =
      nvec_to_zvec output_states.
Proof.
  intros d q S index rule items value Happly.
  destruct (vector_three_parts nat d q (length (stateful_rules S)) value)
    as [out_counters [out_states [out_gates Hvalue]]].
  exists out_states.
  pose proof (add_displacement_exact _ _ _ _
    ltac:(unfold apply_action in Happly;
      destruct (Nat.eqb (List.length (List.map (encode_tagged S) items))
        (action_arity (erase_front_action S index rule)));
      [exact Happly|discriminate])) as Hexact.
  cbn [erase_front_action action_offset] in Hexact.
  rewrite sum_encoded_tagged in Hexact.
  repeat rewrite nvec_to_zvec_append in Hexact.
  repeat rewrite zvec_add_append in Hexact.
  rewrite Hvalue in Hexact. repeat rewrite nvec_to_zvec_append in Hexact.
  apply Vector.append_inj in Hexact as [Hprefix Hgates].
  apply Vector.append_inj in Hprefix as [Hcounters Hstates].
  exact Hstates.
Qed.

Lemma erase_front_items_normal : forall d q (S : SBVAS d q)
    index rule items value,
    apply_action (erase_front_action S index rule)
      (List.map (encode_tagged S) items) = Some value ->
    exists configs : list (SConfig d q),
      items = List.map (fun config => (normal_tag (fst config), snd config)) configs.
Proof.
  intros d q S index rule items value Happly.
  assert (Hlength : List.length items = List.length (input_states rule)).
  { unfold apply_action in Happly.
    destruct (Nat.eqb (List.length (List.map (encode_tagged S) items))
      (action_arity (erase_front_action S index rule))) eqn:Harity;
      [|discriminate].
    apply Nat.eqb_eq in Harity. rewrite map_length in Harity.
    exact Harity. }
  destruct (erase_front_state_equation d q S index rule items value Happly)
    as [output_states Hstates].
  pose proof (state_debit_bound q (input_states rule)
    (tagged_states items) output_states Hstates) as Hrequired.
  pose proof (tagged_states_length_le d q items) as Htagged.
  apply tagged_all_normal. lia.
Qed.

Lemma nvec_le_total_eq : forall n (left right : NVec n),
    (forall index, Vector.nth left index <= Vector.nth right index) ->
    nvec_total left = nvec_total right -> left = right.
Proof.
  intros n left. induction left as [|head n tail IH]; intros right.
  - refine (Vector.case0 (fun right =>
      (forall index, Vector.nth (Vector.nil nat) index <=
        Vector.nth right index) ->
      nvec_total (Vector.nil nat) = nvec_total right ->
      Vector.nil nat = right) _ right).
    intros Hle Htotal. reflexivity.
  - refine (Vector.caseS' right (fun right =>
      (forall index, Vector.nth (@Vector.cons nat head n tail) index <=
        Vector.nth right index) ->
      nvec_total (@Vector.cons nat head n tail) = nvec_total right ->
      @Vector.cons nat head n tail = right) _).
    intros h rest Hle Htotal. cbn in Htotal.
    assert (Hhead : head <= h) by exact (Hle Fin.F1).
    assert (Htail : nvec_total tail <= nvec_total rest).
    { apply nvec_total_mono. intro index. exact (Hle (Fin.FS index)). }
    assert (Hhead_eq : head = h) by lia. subst h. f_equal.
    apply IH.
    + intro index. exact (Hle (Fin.FS index)).
    + lia.
Qed.

Lemma state_debit_exact : forall q
    (required observed : list (Fin.t q)) output,
    List.length required = List.length observed ->
    zvec_add (state_debit required) (nvec_to_zvec (state_count observed)) =
      nvec_to_zvec output ->
    Permutation observed required /\ output = nvec_zero q.
Proof.
  intros q required observed output Hlength Heq.
  assert (Hle : forall index,
      Vector.nth (state_count required) index <=
      Vector.nth (state_count observed) index).
  { intro index.
    pose proof (f_equal (fun value => Vector.nth value index) Heq) as Hindex.
    unfold state_debit, state_count, zvec_add, nvec_to_zvec in Hindex |- *.
    rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
      (nth_map Z.of_nat _ index index eq_refl),
      (nth_map Z.of_nat output index index eq_refl) in Hindex.
    repeat rewrite nth_vector_of_function in Hindex |- *. lia. }
  assert (Hcounts : state_count required = state_count observed).
  { apply nvec_le_total_eq; [exact Hle|].
    repeat rewrite state_count_total. exact Hlength. }
  split.
  - apply (proj2 (Permutation_count_occ Fin.eq_dec observed required)).
    intro state. pose proof (f_equal (fun value => Vector.nth value state)
      Hcounts) as Hstate.
    unfold state_count in Hstate. repeat rewrite nth_vector_of_function in Hstate.
    symmetry. exact Hstate.
  - apply (proj1 (Vector.eq_nth_iff nat q _ _)).
    intros index index' Hindex; subst index'. unfold nvec_zero.
    rewrite (const_nth nat 0 q index).
    pose proof (f_equal (fun value => Vector.nth value index) Heq) as Hcoord.
    unfold state_debit, state_count, zvec_add, nvec_to_zvec in Hcoord.
    rewrite (nth_map2 Z.add _ _ index index index eq_refl eq_refl),
      (nth_map Z.of_nat _ index index eq_refl),
      (nth_map Z.of_nat output index index eq_refl) in Hcoord.
    repeat rewrite nth_vector_of_function in Hcoord.
    pose proof (f_equal (fun value => Vector.nth value index) Hcounts) as Hcount.
    unfold state_count in Hcount. repeat rewrite nth_vector_of_function in Hcount.
    lia.
Qed.

Lemma nvec_to_zvec_inj : forall n (left right : NVec n),
    nvec_to_zvec left = nvec_to_zvec right -> left = right.
Proof.
  intros n left right Heq. apply (proj1 (Vector.eq_nth_iff nat n _ _)).
  intros index index' Hindex; subst index'.
  pose proof (f_equal (fun value => Vector.nth value index) Heq) as Hcoord.
  unfold nvec_to_zvec in Hcoord. repeat rewrite
    (nth_map Z.of_nat _ index index eq_refl) in Hcoord. lia.
Qed.

Lemma erase_front_inverse : forall d q (S : SBVAS d q)
    index rule configs value,
    apply_action (erase_front_action S index rule)
      (List.map (fun config =>
        encode_state_config S (fst config) (snd config)) configs) = Some value ->
    exists result,
      Permutation (List.map fst configs) (input_states rule) /\
      add_displacement (rule_delta rule) (List.map snd configs) = Some result /\
      value = encode_gate_config S index result.
Proof.
  intros d q S index rule configs value Happly.
  assert (Hlength : List.length configs = List.length (input_states rule)).
  { pose proof (apply_action_length _ _ _ _ Happly) as Harity.
    rewrite map_length in Harity. exact Harity. }
  destruct (vector_three_parts nat d q (length (stateful_rules S)) value)
    as [out_counters [out_states [out_gates Hvalue]]].
  assert (Hdisp : add_displacement (action_offset (erase_front_action S index rule))
      (List.map (fun config : SConfig d q =>
        encode_state_config S (fst config) (snd config)) configs) = Some value).
  { unfold apply_action in Happly.
    destruct (Nat.eqb _ _) eqn:Harity; [exact Happly|discriminate]. }
  pose proof (add_displacement_exact _ _ _ _ Hdisp) as Hexact.
  cbn [erase_front_action action_offset] in Hexact.
  rewrite sum_encoded_configs in Hexact.
  repeat rewrite nvec_to_zvec_append in Hexact.
  repeat rewrite zvec_add_append in Hexact.
  rewrite Hvalue in Hexact. repeat rewrite nvec_to_zvec_append in Hexact.
  apply Vector.append_inj in Hexact as [Hprefix Hgate].
  apply Vector.append_inj in Hprefix as [Hcounter Hstate].
  destruct (state_debit_exact q (input_states rule) (List.map fst configs)
    out_states ltac:(rewrite map_length; symmetry; exact Hlength) Hstate)
    as [Hstates Hout_states].
  assert (Hcounter_apply :
      add_displacement (rule_delta rule) (List.map snd configs) =
        Some out_counters).
  { unfold add_displacement. rewrite Hcounter. apply zvec_to_nvec_of_nvec. }
  assert (Hout_gates : out_gates =
      one_hot_nat (length (stateful_rules S)) index).
  { rewrite nvec_to_zvec_zero, zvec_add_zero in Hgate.
    apply nvec_to_zvec_inj. rewrite one_hot_z_of_nat.
    symmetry. exact Hgate. }
  exists out_counters. split; [exact Hstates|]. split; [exact Hcounter_apply|].
  rewrite Hvalue, Hout_states, Hout_gates. reflexivity.
Qed.

Lemma erase_back_inverse_tagged : forall d q (S : SBVAS d q)
    index rule item value,
    index < length (stateful_rules S) ->
    apply_action (erase_back_action S index rule)
      [encode_tagged S item] = Some value ->
    exists counters,
      item = (gate_tag index, counters) /\
      value = encode_state_config S (output_state rule) counters.
Proof.
  intros d q S index rule [tag counters] value Hindex Happly.
  destruct (vector_three_parts nat d q (length (stateful_rules S)) value)
    as [out_counters [out_states [out_gates Hvalue]]].
  assert (Hdisp : add_displacement (action_offset (erase_back_action S index rule))
      [encode_tagged S (tag, counters)] = Some value).
  { unfold apply_action in Happly. cbn in Happly. exact Happly. }
  pose proof (add_displacement_exact _ _ _ _ Hdisp) as Hexact.
  cbn [erase_back_action action_offset]. rewrite nvec_sum_local in Hexact.
  cbn in Hexact. rewrite nvec_add_zero in Hexact.
  destruct tag as [state|gate].
  - change (encode_tagged S (normal_tag state, counters)) with
      (encode_state_config S state counters) in Hexact.
    unfold encode_state_config in Hexact.
    repeat rewrite nvec_to_zvec_append in Hexact.
    repeat rewrite zvec_add_append in Hexact.
    rewrite Hvalue in Hexact. repeat rewrite nvec_to_zvec_append in Hexact.
    apply Vector.append_inj in Hexact as [Hprefix Hgate].
    pose (position := Fin.of_nat_lt Hindex).
    pose proof (f_equal (fun vector => Vector.nth vector position) Hgate) as Hcoord.
    unfold gate_debit, zvec_add, nvec_to_zvec, nvec_zero in Hcoord.
    rewrite (nth_map2 Z.add _ _ position position position eq_refl eq_refl),
      (nth_map Z.opp _ position position eq_refl),
      (nth_map Z.of_nat _ position position eq_refl),
      (const_nth nat 0 _ position),
      (nth_map Z.of_nat out_gates position position eq_refl) in Hcoord.
    unfold one_hot_z in Hcoord. try rewrite nth_vector_of_function in Hcoord.
    unfold position in Hcoord. rewrite Fin.to_nat_of_nat in Hcoord. cbn in Hcoord.
    rewrite Nat.eqb_refl in Hcoord. lia.
  - change (encode_tagged S (gate_tag gate, counters)) with
      (encode_gate_config S gate counters) in Hexact.
    unfold encode_gate_config in Hexact.
    repeat rewrite nvec_to_zvec_append in Hexact.
    repeat rewrite zvec_add_append in Hexact.
    rewrite Hvalue in Hexact. repeat rewrite nvec_to_zvec_append in Hexact.
    apply Vector.append_inj in Hexact as [Hprefix Hgate].
    apply Vector.append_inj in Hprefix as [Hcounter Hstate].
    assert (Hgate_eq : gate = index).
    { pose (position := Fin.of_nat_lt Hindex).
      pose proof (f_equal (fun vector => Vector.nth vector position) Hgate) as Hcoord.
      unfold gate_debit, zvec_add, nvec_to_zvec in Hcoord.
      rewrite (nth_map2 Z.add _ _ position position position eq_refl eq_refl),
        (nth_map Z.opp _ position position eq_refl),
        (nth_map Z.of_nat _ position position eq_refl),
        (nth_map Z.of_nat out_gates position position eq_refl) in Hcoord.
      unfold one_hot_z, one_hot_nat in Hcoord.
      try repeat rewrite nth_vector_of_function in Hcoord.
      unfold position in Hcoord. repeat rewrite Fin.to_nat_of_nat in Hcoord. cbn in Hcoord.
      rewrite Nat.eqb_refl in Hcoord.
      destruct (Nat.eqb index gate) eqn:Heq; [now apply Nat.eqb_eq in Heq|lia]. }
    subst gate. exists counters. split; [reflexivity|].
    assert (Hout_counters : out_counters = counters).
    { rewrite zvec_zero_add in Hcounter. symmetry. now apply nvec_to_zvec_inj. }
    assert (Hout_states : out_states = one_hot_state (output_state rule)).
    { rewrite nvec_to_zvec_zero, zvec_add_zero in Hstate.
      apply nvec_to_zvec_inj. rewrite state_credit_of_nat.
      symmetry. exact Hstate. }
    assert (Hout_gates : out_gates = nvec_zero (length (stateful_rules S))).
    { rewrite gate_debit_cancels in Hgate.
      rewrite <- nvec_to_zvec_zero in Hgate.
      symmetry. now apply nvec_to_zvec_inj. }
    rewrite Hvalue, Hout_counters, Hout_states, Hout_gates. reflexivity.
Qed.

Inductive ErasedClass {d q} (S : SBVAS d q) :
    NVec (d + q + length (stateful_rules S)) -> Prop :=
| erased_normal : forall state counters,
    SReach S state counters ->
    ErasedClass S (encode_state_config S state counters)
| erased_gate : forall position rule configs result,
    nth_error (stateful_rules S) position = Some rule ->
    SReachChildren S configs ->
    Permutation (List.map fst configs) (input_states rule) ->
    add_displacement (rule_delta rule) (List.map snd configs) = Some result ->
    ErasedClass S (encode_gate_config S position result).

Inductive TaggedValid {d q} (S : SBVAS d q) : TaggedConfig d q -> Prop :=
| tagged_normal_valid : forall state counters,
    SReach S state counters -> TaggedValid S (normal_tag state, counters)
| tagged_gate_valid : forall position counters rule configs,
    nth_error (stateful_rules S) position = Some rule ->
    SReachChildren S configs ->
    Permutation (List.map fst configs) (input_states rule) ->
    add_displacement (rule_delta rule) (List.map snd configs) = Some counters ->
    TaggedValid S (gate_tag position, counters).

Lemma erased_class_tagged : forall d q (S : SBVAS d q) value,
    ErasedClass S value ->
    exists item, value = encode_tagged S item /\ TaggedValid S item.
Proof.
  intros d q S value Hclass. destruct Hclass.
  - exists (normal_tag state, counters). split; [reflexivity|constructor; assumption].
  - exists (gate_tag position, result). split; [reflexivity|].
    econstructor; eauto.
Qed.

Lemma erased_classes_tagged : forall d q (S : SBVAS d q) values,
    List.Forall (ErasedClass S) values ->
    exists items,
      values = List.map (encode_tagged S) items /\
      List.Forall (TaggedValid S) items.
Proof.
  intros d q S values Hvalues. induction Hvalues.
  - exists []. split; constructor.
  - destruct (erased_class_tagged d q S x H) as [item [Hitem Hvalid]].
    destruct IHHvalues as [items [Hitems Hvalids]].
    exists (item :: items). cbn. subst x l. split; [reflexivity|constructor; assumption].
Qed.

Lemma tagged_normal_inv : forall d q (S : SBVAS d q) state counters,
    TaggedValid S (normal_tag state, counters) -> SReach S state counters.
Proof. intros d q S state counters H. inversion H; subst; assumption. Qed.

Lemma tagged_gate_inv : forall d q (S : SBVAS d q) position counters,
    TaggedValid S (gate_tag position, counters) ->
    exists rule configs,
      nth_error (stateful_rules S) position = Some rule /\
      SReachChildren S configs /\
      Permutation (List.map fst configs) (input_states rule) /\
      add_displacement (rule_delta rule) (List.map snd configs) = Some counters.
Proof.
  intros d q S position counters H. inversion H; subst.
  eexists _, _. repeat split; eauto.
Qed.

Lemma tagged_normals_reachable : forall d q (S : SBVAS d q) configs,
    List.Forall (TaggedValid S)
      (List.map (fun config => (normal_tag (fst config), snd config)) configs) ->
    SReachChildren S configs.
Proof.
  intros d q S configs. induction configs as [|[state counters] configs IH];
    intro Hvalid; cbn in Hvalid |- *.
  - constructor.
  - inversion Hvalid; subst.
    constructor.
    + match goal with
      | Hhead : TaggedValid S (normal_tag state, counters) |- _ =>
          exact (tagged_normal_inv d q S state counters Hhead)
      end.
    + apply IH. match goal with
      | Htail : List.Forall (TaggedValid S)
          (List.map _ configs) |- _ => exact Htail
      end.
Qed.

Lemma nth_error_lt : forall A (values : list A) position value,
    nth_error values position = Some value -> position < List.length values.
Proof.
  intros A values position value Hnth. apply nth_error_Some.
  rewrite Hnth. discriminate.
Qed.

Lemma erased_reach_class_mut : forall d q (S : SBVAS d q),
  (forall value, Reach (erase_states S) value -> ErasedClass S value) /\
  (forall values, ReachChildren (erase_states S) values ->
    List.Forall (ErasedClass S) values).
Proof.
  intros d q S. apply Reach_mutind.
  - intros initial_index value Hinitial.
    cbn in Hinitial.
    apply nth_error_In in Hinitial. apply in_map_iff in Hinitial.
    destruct Hinitial as [[state counters] [<- Hin]].
    constructor. now apply sreach_initial.
  - intros action_index action children value Haction Hchildren IHchildren Happly.
    apply nth_error_In in Haction. cbn in Haction.
    destruct (erase_rule_actions_in d q S action (stateful_rules S) 0 Haction)
      as [position [rule [Hrule [Hfront|Hback]]]].
    + rewrite Nat.add_0_l in Hfront. subst action.
      destruct (erased_classes_tagged d q S children IHchildren)
        as [items [Hitems Hvalids]]. subst children.
      destruct (erase_front_items_normal d q S position rule items value Happly)
        as [configs Hconfigs]. subst items.
      assert (Hreachable : SReachChildren S configs).
      { apply tagged_normals_reachable. exact Hvalids. }
      rewrite map_encode_tagged_normal in Happly.
      destruct (erase_front_inverse d q S position rule configs value Happly)
        as [result [Hstates [Horiginal Hvalue]]]. subst value.
      econstructor; eauto.
    + rewrite Nat.add_0_l in Hback. subst action.
      destruct (erased_classes_tagged d q S children IHchildren)
        as [items [Hitems Hvalids]]. subst children.
      pose proof (apply_action_length _ _ _ _ Happly) as Hlength.
      cbn in Hlength. destruct items as [|item items]; cbn in Hlength; [discriminate|].
      destruct items; cbn in Hlength; [|discriminate].
      pose proof (Forall_inv Hvalids) as Hitemvalid.
      destruct (erase_back_inverse_tagged d q S position rule item value
        (nth_error_lt _ _ _ _ Hrule) Happly) as
        [counters [Hitem Hvalue]].
      subst item value.
      destruct (tagged_gate_inv d q S position counters Hitemvalid) as
        [pending_rule [configs [Hpending [Hreachable [Hstates Horiginal]]]]].
      rewrite Hrule in Hpending. inversion Hpending; subst pending_rule.
      constructor. eapply sreach_rule with
        (rule := rule) (child_configs := configs).
      * exact (nth_error_In _ _ Hrule).
      * exact Hreachable.
      * exact Hstates.
      * exact Horiginal.
  - constructor.
  - intros child children Hchild IHchild Hchildren IHchildren.
    constructor; assumption.
Qed.

Lemma one_hot_state_inj : forall q (left right : Fin.t q),
    one_hot_state left = one_hot_state right -> left = right.
Proof.
  intros q left right Heq.
  destruct (Fin.eq_dec left right) as [->|Hneq]; [reflexivity|].
  exfalso. pose proof (f_equal (fun value => Vector.nth value left) Heq) as Hcoord.
  unfold one_hot_state in Hcoord. repeat rewrite nth_vector_of_function in Hcoord.
  destruct (Fin.eq_dec left left); [|contradiction].
  destruct (Fin.eq_dec left right); [contradiction|]. discriminate.
Qed.

Lemma encode_state_config_inj : forall d q (S : SBVAS d q)
    left_state left_counters right_state right_counters,
    encode_state_config S left_state left_counters =
      encode_state_config S right_state right_counters ->
    left_state = right_state /\ left_counters = right_counters.
Proof.
  intros d q S left_state left_counters right_state right_counters Heq.
  unfold encode_state_config in Heq.
  apply Vector.append_inj in Heq as [Hprefix Hgates].
  apply Vector.append_inj in Hprefix as [Hcounters Hstates].
  split; [now apply one_hot_state_inj in Hstates|exact Hcounters].
Qed.

Lemma encode_gate_state_distinct : forall d q (S : SBVAS d q)
    index gate_counters state state_counters,
    encode_gate_config S index gate_counters <>
      encode_state_config S state state_counters.
Proof.
  intros d q S index gate_counters state state_counters Heq.
  unfold encode_gate_config, encode_state_config in Heq.
  apply Vector.append_inj in Heq as [Hprefix Hgates].
  apply Vector.append_inj in Hprefix as [Hcounters Hstates].
  pose proof (f_equal nvec_total Hstates) as Htotal.
  rewrite nvec_total_zero, one_hot_state_total in Htotal. discriminate.
Qed.

Theorem erased_reach_sreach : forall d q (S : SBVAS d q) state counters,
    Reach (erase_states S) (encode_state_config S state counters) ->
    SReach S state counters.
Proof.
  intros d q S state counters Hreach.
  remember (encode_state_config S state counters) as target eqn:Htarget.
  assert (Htarget_reach : Reach (erase_states S) target) by now subst target.
  clear Hreach.
  pose proof (proj1 (erased_reach_class_mut d q S) target Htarget_reach)
    as Hclass.
  destruct Hclass.
  - destruct (encode_state_config_inj d q S state0 counters0 state counters
      Htarget) as [Hstate Hcounters]. subst. exact H.
  - exfalso. eapply encode_gate_state_distinct. exact Htarget.
Qed.

Theorem erase_states_correct : forall d q (S : SBVAS d q)
    (state : Fin.t q) counters,
    SReach S state counters <->
    Reach (erase_states S) (encode_state_config S state counters).
Proof.
  intros d q S state counters. split.
  - apply sreach_erased.
  - apply erased_reach_sreach.
Qed.

Lemma encode_initial_in : forall d q (S : SBVAS d q) state counters,
    List.In (state, counters) (initial_configs S) ->
    List.In (encode_state_config S state counters)
      (initial_vectors (erase_states S)).
Proof.
  intros d q S state counters H.
  apply in_map_iff. exists (state, counters). split; [reflexivity|exact H].
Qed.
