From Coq Require Import List ZArith Lia Sorting.Permutation.
Require Import Yalla.OLlibs.PermutationPropify.
From Mell.Core Require Import Vector.
From Mell.BVAS Require Import RunOrder.
From Mell.Logic Require Import Syntax YallaBridge.
From Mell.Reduction Require Import ILZ MELLToABVASS.

Import ListNotations.
Module IF := Yalla.iformulas.

Definition context_guarded_bodies (context : list IF.iformula) : list IF.iformula :=
  List.flat_map (fun formula =>
    match formula with IF.ioc A => [A] | _ => [] end) context.

Definition ILZMachineCompleteAt (goal : ILZGoal)
    (context : list IF.iformula) (conclusion : IF.iformula) : Prop :=
  forall support,
    List.In support (ilz_supports goal) ->
    List.incl (context_guarded_bodies context) support ->
    FullZeroReach (compile_ilz_machine goal)
      (ilz_machine_sequent support conclusion)
      (encode_counter_context (ilz_subformulas goal)
        (linear_context context)).

Lemma context_guarded_bodies_in : forall context A,
  List.In A (context_guarded_bodies context) <->
  List.In (IF.ioc A) context.
Proof.
  intros context A. unfold context_guarded_bodies.
  apply guarded_body_in.
Qed.

Lemma context_guarded_bodies_app : forall left right,
  context_guarded_bodies (left ++ right) =
  context_guarded_bodies left ++ context_guarded_bodies right.
Proof.
  intros left right. unfold context_guarded_bodies.
  apply List.flat_map_app.
Qed.

Lemma linear_context_app : forall left right,
  linear_context (left ++ right) = linear_context left ++ linear_context right.
Proof.
  induction left as [|head tail IH]; intro right; cbn; [reflexivity|].
  destruct head; cbn; now rewrite IH.
Qed.

Definition linear_formula_list (formula : IF.iformula) : list IF.iformula :=
  match formula with IF.ioc _ => [] | _ => [formula] end.

Lemma linear_context_flat_map : forall context,
  linear_context context = List.flat_map linear_formula_list context.
Proof.
  induction context as [|head tail IH]; cbn; [reflexivity|].
  destruct head; cbn; now rewrite IH.
Qed.

Lemma linear_context_permutation : forall left right,
  Permutation left right ->
  Permutation (linear_context left) (linear_context right).
Proof.
  intros left right Hperm. rewrite !linear_context_flat_map.
  now apply Permutation_flat_map.
Qed.

Lemma context_guarded_bodies_permutation : forall left right,
  Permutation left right ->
  Permutation (context_guarded_bodies left) (context_guarded_bodies right).
Proof.
  intros left right Hperm. unfold context_guarded_bodies.
  now apply Permutation_flat_map.
Qed.

Lemma forall_permutation : forall (P : IF.iformula -> Prop) left right,
  Permutation left right -> List.Forall P left -> List.Forall P right.
Proof.
  intros P left right Hperm Hforall. apply List.Forall_forall.
  intros A HA. apply (proj1 (List.Forall_forall _ _) Hforall).
  eapply Permutation_in; [exact (Permutation_sym Hperm)|exact HA].
Qed.

Lemma ilz_machine_complete_at_permutation : forall goal left right conclusion,
  Permutation left right ->
  ILZMachineCompleteAt goal left conclusion ->
  ILZMachineCompleteAt goal right conclusion.
Proof.
  intros goal left right conclusion Hperm Hcomplete.
  unfold ILZMachineCompleteAt in *. intros support Hsupport Hguard.
  pose proof (context_guarded_bodies_permutation _ _ Hperm) as Hguarded.
  pose proof (linear_context_permutation _ _ Hperm) as Hlinear.
  rewrite <- (encode_counter_context_permutation _ _ _ Hlinear).
  apply Hcomplete; [exact Hsupport|].
  intros body Hbody. apply Hguard.
  eapply Permutation_in; [exact Hguarded|exact Hbody].
Qed.

Lemma encode_counter_context_nil : forall subformulas,
  encode_counter_context subformulas [] = nvec_zero (length subformulas).
Proof.
  induction subformulas as [|formula tail IH]; cbn; [reflexivity|].
  f_equal. exact IH.
Qed.

Lemma support_union_absorbed : forall left right,
  List.incl left right -> support_union left right = right.
Proof.
  unfold support_union. induction left as [|head tail IH];
    intros right Hincl; cbn; [reflexivity|].
  rewrite IH by (intros A HA; apply Hincl; now right).
  unfold add_support.
  destruct (in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec
    head right); [reflexivity|].
  exfalso. apply n, Hincl. now left.
Qed.

Lemma support_union_id : forall support,
  support_union support support = support.
Proof.
  intro support. apply support_union_absorbed. apply List.incl_refl.
Qed.

Lemma nvec_add_comm_reduction : forall d (left right : NVec d),
  nvec_add left right = nvec_add right left.
Proof.
  intros d left right. apply (proj1 (Vector.eq_nth_iff nat d _ _)).
  intros index index' Heq; subst index'. unfold nvec_add.
  repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl).
  lia.
Qed.

Lemma encode_counter_context_middle : forall subformulas before formula after,
  encode_counter_context subformulas (before ++ formula :: after) =
  nvec_add (encode_counter_context subformulas [formula])
    (encode_counter_context subformulas (before ++ after)).
Proof.
  intros subformulas before formula after.
  rewrite !encode_counter_context_app, encode_counter_context_cons.
  rewrite <- nvec_add_assoc.
  rewrite (nvec_add_comm_reduction _
    (encode_counter_context subformulas before)
    (encode_counter_context subformulas [formula])).
  apply nvec_add_assoc.
Qed.

Lemma formula_remove_middle_application : forall subformulas before formula after,
  add_displacement (formula_remove subformulas formula)
    [encode_counter_context subformulas (before ++ formula :: after)] =
  Some (encode_counter_context subformulas (before ++ after)).
Proof.
  intros. rewrite encode_counter_context_middle.
  apply formula_remove_application.
Qed.

Lemma formula_replace_two_application_from_balance : forall subformulas old first second
    source target,
  nvec_add (encode_counter_context subformulas [old]) target =
  nvec_add (encode_counter_context subformulas [first])
    (nvec_add (encode_counter_context subformulas [second]) source) ->
  add_displacement
    (zvec_add (formula_remove subformulas old)
      (zvec_add (formula_add subformulas first)
        (formula_add subformulas second))) [source] = Some target.
Proof.
  intros subformulas old first second source target Hbalance.
  apply add_displacement_of_exact_reduction.
  rewrite nvec_sum_singleton_reduction, !formula_remove_encode_singleton,
    !formula_add_encode_singleton.
  apply (proj1 (Vector.eq_nth_iff Z _ _ _)).
  intros index index' Heq; subst index'.
  apply (f_equal (fun value => Vector.nth value index)) in Hbalance.
  unfold zvec_add, nvec_add, nvec_to_zvec in *.
  repeat rewrite (Vector.nth_map2 Z.add _ _ index index index eq_refl eq_refl).
  rewrite (Vector.nth_map Z.opp _ index index eq_refl).
  repeat rewrite (Vector.nth_map Z.of_nat _ index index eq_refl).
  repeat rewrite (Vector.nth_map2 Nat.add _ _ index index index eq_refl eq_refl)
    in Hbalance.
  lia.
Qed.

Lemma formula_replace_two_middle_application : forall subformulas before old first second after,
  add_displacement
    (zvec_add (formula_remove subformulas old)
      (zvec_add (formula_add subformulas first)
        (formula_add subformulas second)))
    [encode_counter_context subformulas (before ++ old :: after)] =
  Some (encode_counter_context subformulas (before ++ first :: second :: after)).
Proof.
  intros. apply formula_replace_two_application_from_balance.
  repeat rewrite encode_counter_context_middle.
  rewrite <- !nvec_add_assoc. f_equal.
  rewrite (nvec_add_comm_reduction _
    (encode_counter_context subformulas [old])
    (encode_counter_context subformulas [first])).
  rewrite !nvec_add_assoc.
  rewrite (nvec_add_comm_reduction _
    (encode_counter_context subformulas [old])
    (encode_counter_context subformulas [second])). reflexivity.
Qed.

Lemma initial_variable_reach : forall goal support atom,
  List.In support (ilz_supports goal) ->
  List.In (IF.ivar atom) (ilz_subformulas goal) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support (IF.ivar atom))
    (encode_counter_context (ilz_subformulas goal) [IF.ivar atom]).
Proof.
  intros goal support atom Hsupport Hformula.
  refine (@full_zero_reach_unary
    (length (ilz_subformulas goal)) ILZMachineState
    (compile_ilz_machine goal)
    (@mk_unary (length (ilz_subformulas goal))
      (ilz_machine_sequent support (IF.ivar atom))
      (formula_remove (ilz_subformulas goal) (IF.ivar atom))
      ilz_machine_leaf)
    (encode_counter_context (ilz_subformulas goal) [IF.ivar atom])
    (nvec_zero (length (ilz_subformulas goal))) _ _ _).
  - cbn [compile_ilz_machine].
    apply List.in_or_app. left.
    unfold ilz_initial_rules.
    apply List.in_flat_map. exists support. split; [exact Hsupport|].
    apply List.in_flat_map. exists (IF.ivar atom). split; [exact Hformula|].
    cbn. now left.
  - change (add_displacement
      (formula_remove (ilz_subformulas goal) (IF.ivar atom))
      [encode_counter_context (ilz_subformulas goal) [IF.ivar atom]] =
      Some (nvec_zero (length (ilz_subformulas goal)))).
    replace (encode_counter_context (ilz_subformulas goal) [IF.ivar atom])
      with (nvec_add
        (encode_counter_context (ilz_subformulas goal) [IF.ivar atom])
        (nvec_zero (length (ilz_subformulas goal)))).
    + apply formula_remove_application.
    + apply nvec_add_zero_right.
  - apply full_zero_reach_leaf. cbn. now left.
Qed.

Lemma initial_one_reach : forall goal support,
  List.In support (ilz_supports goal) ->
  List.In IF.ione (ilz_subformulas goal) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support IF.ione)
    (nvec_zero (length (ilz_subformulas goal))).
Proof.
  intros goal support Hsupport Hformula.
  refine (@full_zero_reach_unary
    (length (ilz_subformulas goal)) ILZMachineState
    (compile_ilz_machine goal)
    (@mk_unary (length (ilz_subformulas goal))
      (ilz_machine_sequent support IF.ione)
      (zvec_zero (length (ilz_subformulas goal))) ilz_machine_leaf)
    (nvec_zero (length (ilz_subformulas goal)))
    (nvec_zero (length (ilz_subformulas goal))) _ _ _).
  - cbn [compile_ilz_machine].
    apply List.in_or_app. left.
    unfold ilz_initial_rules.
    apply List.in_flat_map. exists support. split; [exact Hsupport|].
    apply List.in_flat_map. exists IF.ione. split; [exact Hformula|].
    cbn. now left.
  - apply zero_displacement_application.
  - apply full_zero_reach_leaf. cbn. now left.
Qed.

Lemma initial_ioc_reach : forall goal support A,
  List.In support (ilz_supports goal) ->
  List.In (IF.ioc A) (ilz_subformulas goal) ->
  List.In A support ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support (IF.ioc A))
    (nvec_zero (length (ilz_subformulas goal))).
Proof.
  intros goal support A Hsupport Hformula HA.
  refine (@full_zero_reach_unary
    (length (ilz_subformulas goal)) ILZMachineState
    (compile_ilz_machine goal)
    (@mk_unary (length (ilz_subformulas goal))
      (ilz_machine_sequent support (IF.ioc A))
      (zvec_zero (length (ilz_subformulas goal))) ilz_machine_leaf)
    (nvec_zero (length (ilz_subformulas goal)))
    (nvec_zero (length (ilz_subformulas goal))) _ _ _).
  - cbn [compile_ilz_machine].
    apply List.in_or_app. left.
    unfold ilz_initial_rules.
    apply List.in_flat_map. exists support. split; [exact Hsupport|].
    apply List.in_flat_map. exists (IF.ioc A). split; [exact Hformula|].
    cbn. destruct (in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec
      A support); [now left|contradiction].
  - apply zero_displacement_application.
  - apply full_zero_reach_leaf. cbn. now left.
Qed.

Lemma tensor_right_reach : forall goal support left right A B,
  List.In support (ilz_supports goal) ->
  List.In (IF.itens A B) (ilz_subformulas goal) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support A)
    (encode_counter_context (ilz_subformulas goal) (linear_context left)) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support B)
    (encode_counter_context (ilz_subformulas goal) (linear_context right)) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support (IF.itens A B))
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (left ++ right))).
Proof.
  intros goal support left right A B Hsupport Hformula Hleft Hright.
  refine (@full_zero_reach_split
    (length (ilz_subformulas goal)) ILZMachineState
    (compile_ilz_machine goal)
    (mk_split
      (ilz_machine_sequent support (IF.itens A B))
      (ilz_machine_sequent support A)
      (ilz_machine_sequent support B))
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (left ++ right)))
    (encode_counter_context (ilz_subformulas goal) (linear_context left))
    (encode_counter_context (ilz_subformulas goal) (linear_context right))
    _ _ Hleft Hright).
  - cbn [compile_ilz_machine]. unfold ilz_split_rules.
    apply List.in_or_app. left.
    apply List.in_flat_map. exists support. split; [exact Hsupport|].
    apply List.in_flat_map. exists support. split; [exact Hsupport|].
    apply List.in_flat_map. exists (IF.itens A B). split; [exact Hformula|].
    fold (support_union support support). rewrite support_union_id. cbn. now left.
  - rewrite linear_context_app, encode_counter_context_app. reflexivity.
Qed.

Lemma one_left_reach : forall goal support before after conclusion,
  List.In support (ilz_supports goal) ->
  List.In IF.ione (ilz_subformulas goal) ->
  List.In conclusion (ilz_subformulas goal) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support conclusion)
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (before ++ after))) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support conclusion)
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (before ++ IF.ione :: after))).
Proof.
  intros goal support before after conclusion Hsupport Hone Hconclusion Hreach.
  rewrite !linear_context_app in Hreach |- *. cbn in Hreach |- *.
  refine (@full_zero_reach_unary
    (length (ilz_subformulas goal)) ILZMachineState
    (compile_ilz_machine goal)
    (@mk_unary (length (ilz_subformulas goal))
      (ilz_machine_sequent support conclusion)
      (formula_remove (ilz_subformulas goal) IF.ione)
      (ilz_machine_sequent support conclusion))
    (encode_counter_context (ilz_subformulas goal)
      (linear_context before ++ IF.ione :: linear_context after))
    (encode_counter_context (ilz_subformulas goal)
      (linear_context before ++ linear_context after)) _ _ Hreach).
  - cbn [compile_ilz_machine].
    apply List.in_or_app. right. apply List.in_or_app. right.
    apply List.in_or_app. left. unfold ilz_logical_unary_rules.
    apply List.in_flat_map.
    exists (ilz_machine_sequent support conclusion). split.
    + apply ilz_sequent_state_in; assumption.
    + apply List.in_flat_map. exists IF.ione. split; [exact Hone|].
      cbn. now left.
  - apply formula_remove_middle_application.
Qed.

Lemma store_context_reach_frame : forall goal context support frame conclusion,
  List.In support (ilz_supports goal) ->
  List.In conclusion (ilz_subformulas goal) ->
  List.Forall (fun A => List.In A (ilz_subformulas goal)) context ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent (store_context_support support context) conclusion)
    (encode_counter_context (ilz_subformulas goal)
      (frame ++ linear_context context)) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support conclusion)
    (encode_counter_context (ilz_subformulas goal) (frame ++ context)).
Proof.
  intros goal context; induction context as [|head tail IH];
    intros support frame conclusion Hsupport Hconclusion Hall Hreach.
  - cbn in *. exact Hreach.
  - inversion Hall as [|? ? Hhead Htail]; subst.
    assert (Hlinear_step : forall formula,
      FullZeroReach (compile_ilz_machine goal)
        (ilz_machine_sequent (store_context_support support tail) conclusion)
        (encode_counter_context (ilz_subformulas goal)
          (frame ++ formula :: linear_context tail)) ->
      FullZeroReach (compile_ilz_machine goal)
        (ilz_machine_sequent support conclusion)
        (encode_counter_context (ilz_subformulas goal)
          (frame ++ formula :: tail))).
    { intros formula Hlinear.
      replace (frame ++ formula :: tail) with ((frame ++ [formula]) ++ tail)
        by now rewrite <- List.app_assoc.
      replace (frame ++ formula :: linear_context tail)
        with ((frame ++ [formula]) ++ linear_context tail) in Hlinear
        by now rewrite <- List.app_assoc.
      exact (IH support (frame ++ [formula]) conclusion Hsupport Hconclusion
        Htail Hlinear). }
    destruct head as
      [atom | | tens_left tens_right | lpam_left lpam_right | gen_body
       | lmap_left lmap_right | neg_body | | with_left with_right | | plus_left plus_right
       | ioc_body]; cbn in Hreach |- *; try (now apply Hlinear_step).
    cbn in Hreach |- *.
    assert (Hadded : List.In (add_support ioc_body support) (ilz_supports goal)).
    { change (List.In (store_context_support support [IF.ioc ioc_body])
        (ilz_supports goal)).
      apply store_context_support_in; [exact Hsupport|].
      constructor; [exact Hhead|constructor]. }
    specialize (IH (add_support ioc_body support) frame conclusion Hadded Hconclusion
      Htail Hreach).
    refine (@full_zero_reach_unary
      (length (ilz_subformulas goal)) ILZMachineState
      (compile_ilz_machine goal)
      (@mk_unary (length (ilz_subformulas goal))
        (ilz_machine_sequent support conclusion)
        (formula_remove (ilz_subformulas goal) (IF.ioc ioc_body))
        (ilz_machine_sequent (add_support ioc_body support) conclusion))
      (encode_counter_context (ilz_subformulas goal)
        (frame ++ IF.ioc ioc_body :: tail))
      (encode_counter_context (ilz_subformulas goal) (frame ++ tail))
      _ _ IH).
    + apply ilz_store_move_rule_in; assumption.
    + apply formula_remove_middle_application.
Qed.

Lemma store_context_support_absorbed : forall support context,
  List.incl (context_guarded_bodies context) support ->
  store_context_support support context = support.
Proof.
  intros support context; revert support.
  induction context as [|head tail IH]; intros support Hincl; cbn; [reflexivity|].
  destruct head as
    [atom | | tens_left tens_right | lpam_left lpam_right | gen_body
     | lmap_left lmap_right | neg_body | | with_left with_right | | plus_left plus_right
     | ioc_body]; cbn in *; try (apply IH; intros A HA; apply Hincl; exact HA).
  unfold add_support.
  destruct (in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec
    ioc_body support) as [Hin | Hnotin].
  - apply IH. intros A HA. apply Hincl. now right.
  - exfalso. apply Hnotin, Hincl. now left.
Qed.

Lemma context_guarded_bodies_in_store : forall support context,
  List.incl (context_guarded_bodies context)
    (store_context_support support context).
Proof.
  assert (Hsupport : forall support context,
    List.incl support (store_context_support support context)).
  { intros initial context'; revert initial.
    induction context' as [|head' tail' IH']; intros initial A HA; cbn.
    - exact HA.
    - destruct head' as
        [atom | | tens_left tens_right | lpam_left lpam_right | gen_body
         | lmap_left lmap_right | neg_body | | with_left with_right | | plus_left plus_right
         | ioc_body]; cbn; try (now apply IH').
      apply IH'. apply add_support_in. now right. }
  intros support context; revert support.
  induction context as [|head tail IH]; intros support A HA; cbn in HA |- *.
  - contradiction.
  - destruct head as
      [atom | | tens_left tens_right | lpam_left lpam_right | gen_body
       | lmap_left lmap_right | neg_body | | with_left with_right | | plus_left plus_right
       | ioc_body]; cbn in HA |- *; try (eapply IH; exact HA).
    destruct HA as [<- | HA].
    + apply Hsupport. apply add_support_in. now left.
    + eapply IH; exact HA.
Qed.

Lemma store_context_reach : forall goal context support conclusion,
  List.In support (ilz_supports goal) ->
  List.In conclusion (ilz_subformulas goal) ->
  List.Forall (fun A => List.In A (ilz_subformulas goal)) context ->
  List.incl (context_guarded_bodies context) support ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support conclusion)
    (encode_counter_context (ilz_subformulas goal) (linear_context context)) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support conclusion)
    (encode_counter_context (ilz_subformulas goal) context).
Proof.
  intros goal context support conclusion Hsupport Hconclusion Hall Hguard Hreach.
  eapply store_context_reach_frame with (frame := []); eauto.
  cbn. rewrite store_context_support_absorbed by exact Hguard. exact Hreach.
Qed.

Inductive MELLILZFormula : IF.iformula -> Prop :=
| mell_ilz_var : forall atom, MELLILZFormula (IF.ivar atom)
| mell_ilz_one : MELLILZFormula IF.ione
| mell_ilz_tens : forall A B,
    MELLILZFormula A -> MELLILZFormula B -> MELLILZFormula (IF.itens A B)
| mell_ilz_lmap : forall A B,
    MELLILZFormula A -> MELLILZFormula B -> MELLILZFormula (IF.ilmap A B)
| mell_ilz_ioc : forall A,
    MELLILZFormula A -> MELLILZFormula (IF.ioc A).

Lemma context_guarded_bodies_incl_app_left : forall left right support,
  List.incl (context_guarded_bodies (left ++ right)) support ->
  List.incl (context_guarded_bodies left) support.
Proof.
  intros left right support H A HA. apply H.
  rewrite context_guarded_bodies_app, List.in_app_iff. now left.
Qed.

Lemma context_guarded_bodies_incl_app_right : forall left right support,
  List.incl (context_guarded_bodies (left ++ right)) support ->
  List.incl (context_guarded_bodies right) support.
Proof.
  intros left right support H A HA. apply H.
  rewrite context_guarded_bodies_app, List.in_app_iff. now right.
Qed.

Lemma tensor_left_reach : forall goal support before after conclusion A B,
  List.In support (ilz_supports goal) ->
  List.In (IF.itens A B) (ilz_subformulas goal) ->
  List.In conclusion (ilz_subformulas goal) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent (store_context_support support [A; B]) conclusion)
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (before ++ A :: B :: after))) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support conclusion)
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (before ++ IF.itens A B :: after))).
Proof.
  intros goal support before after conclusion A B Hsupport Htensor Hconclusion Hreach.
  assert (HA : List.In A (ilz_subformulas goal)).
  { eapply ilz_subformula_child; [exact Htensor|].
    apply IF.isub_tens_l. constructor. }
  assert (HB : List.In B (ilz_subformulas goal)).
  { eapply ilz_subformula_child; [exact Htensor|].
    apply IF.isub_tens_r. constructor. }
  assert (Hstored : List.In (store_context_support support [A; B])
      (ilz_supports goal)).
  { apply store_context_support_in; [exact Hsupport|].
    repeat constructor; assumption. }
  assert (Hlocal : FullZeroReach (compile_ilz_machine goal)
      (ilz_machine_sequent support conclusion)
      (encode_counter_context (ilz_subformulas goal)
        ((linear_context before ++ linear_context after) ++ [A; B]))).
  { eapply store_context_reach_frame with
      (context := [A; B])
      (frame := linear_context before ++ linear_context after).
    - exact Hsupport.
    - exact Hconclusion.
    - repeat constructor; assumption.
    - assert (Hperm : Permutation (before ++ A :: B :: after)
          ((before ++ after) ++ [A; B])).
      { repeat rewrite <- List.app_assoc. apply Permutation_app_head.
        change (Permutation (A :: B :: after) (after ++ [A; B])).
        change (Permutation ([A; B] ++ after) (after ++ [A; B])).
        apply Permutation_app_comm. }
      pose proof (encode_counter_context_permutation
        (ilz_subformulas goal) _ _
        (linear_context_permutation _ _ Hperm)) as Heq.
      rewrite <- !linear_context_app.
      rewrite <- Heq. exact Hreach. }
  assert (Htarget : FullZeroReach (compile_ilz_machine goal)
      (ilz_machine_sequent support conclusion)
      (encode_counter_context (ilz_subformulas goal)
        (linear_context before ++ A :: B :: linear_context after))).
  { rewrite (encode_counter_context_permutation
      (ilz_subformulas goal)
      (linear_context before ++ A :: B :: linear_context after)
      ((linear_context before ++ linear_context after) ++ [A; B])).
    - exact Hlocal.
    - repeat rewrite <- List.app_assoc. apply Permutation_app_head.
      change (Permutation (A :: B :: linear_context after)
        (linear_context after ++ [A; B])).
      change (Permutation ([A; B] ++ linear_context after)
        (linear_context after ++ [A; B])).
      apply Permutation_app_comm. }
  rewrite !linear_context_app. cbn [linear_context].
  refine (@full_zero_reach_unary
    (length (ilz_subformulas goal)) ILZMachineState
    (compile_ilz_machine goal)
    (@mk_unary (length (ilz_subformulas goal))
      (ilz_machine_sequent support conclusion)
      (zvec_add (formula_remove (ilz_subformulas goal) (IF.itens A B))
        (zvec_add (formula_add (ilz_subformulas goal) A)
          (formula_add (ilz_subformulas goal) B)))
      (ilz_machine_sequent support conclusion))
    (encode_counter_context (ilz_subformulas goal)
      (linear_context before ++ IF.itens A B :: linear_context after))
    (encode_counter_context (ilz_subformulas goal)
      (linear_context before ++ A :: B :: linear_context after)) _ _ Htarget).
  - cbn [compile_ilz_machine]. apply List.in_or_app. right.
    apply List.in_or_app. right. apply List.in_or_app. left.
    unfold ilz_logical_unary_rules. apply List.in_flat_map.
    exists (ilz_machine_sequent support conclusion). split.
    + now apply ilz_sequent_state_in.
    + apply List.in_flat_map. exists (IF.itens A B). split; [exact Htensor|].
      cbn. now left.
  - apply formula_replace_two_middle_application.
Qed.

Lemma lmap_right_reach : forall goal support context A B,
  List.In support (ilz_supports goal) ->
  List.In (IF.ilmap A B) (ilz_subformulas goal) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent (store_context_support support [A]) B)
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (A :: context))) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support (IF.ilmap A B))
    (encode_counter_context (ilz_subformulas goal) (linear_context context)).
Proof.
  intros goal support context A B Hsupport Hlmap Hreach.
  assert (HA : List.In A (ilz_subformulas goal)).
  { eapply ilz_subformula_child; [exact Hlmap|].
    apply IF.isub_lmap_l. constructor. }
  assert (HB : List.In B (ilz_subformulas goal)).
  { eapply ilz_subformula_child; [exact Hlmap|].
    apply IF.isub_lmap_r. constructor. }
  assert (Hraw : FullZeroReach (compile_ilz_machine goal)
      (ilz_machine_sequent support B)
      (encode_counter_context (ilz_subformulas goal)
        (linear_context context ++ [A]))).
  { eapply store_context_reach_frame with
      (context := [A]) (frame := linear_context context).
    - exact Hsupport.
    - exact HB.
    - repeat constructor; assumption.
    - rewrite <- linear_context_app.
      assert (Hperm : Permutation (A :: context) (context ++ [A])).
      { change (Permutation ([A] ++ context) (context ++ [A])).
        apply Permutation_app_comm. }
      rewrite <- (encode_counter_context_permutation
        (ilz_subformulas goal) _ _
        (linear_context_permutation _ _ Hperm)). exact Hreach. }
  refine (@full_zero_reach_unary
    (length (ilz_subformulas goal)) ILZMachineState
    (compile_ilz_machine goal)
    (@mk_unary (length (ilz_subformulas goal))
      (ilz_machine_sequent support (IF.ilmap A B))
      (formula_add (ilz_subformulas goal) A)
      (ilz_machine_sequent support B))
    (encode_counter_context (ilz_subformulas goal) (linear_context context))
    (encode_counter_context (ilz_subformulas goal)
      (linear_context context ++ [A])) _ _ Hraw).
  - cbn [compile_ilz_machine]. apply List.in_or_app. right.
    apply List.in_or_app. right. apply List.in_or_app. left.
    unfold ilz_logical_unary_rules. apply List.in_flat_map.
    exists (ilz_machine_sequent support (IF.ilmap A B)). split.
    + apply ilz_sequent_state_in; assumption.
    + apply List.in_flat_map. exists (IF.ilmap A B). split; [exact Hlmap|].
      cbn. now left.
  - rewrite encode_counter_context_app, nvec_add_comm_reduction.
    apply formula_add_application.
Qed.

Lemma support_copy_reach : forall goal support frame conclusion A,
  List.In support (ilz_supports goal) ->
  List.In conclusion (ilz_subformulas goal) ->
  List.In (IF.ioc A) (ilz_subformulas goal) ->
  List.In A support ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support conclusion)
    (encode_counter_context (ilz_subformulas goal) (frame ++ [A])) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support conclusion)
    (encode_counter_context (ilz_subformulas goal) frame).
Proof.
  intros goal support frame conclusion A Hsupport Hconclusion Hioc HA Hreach.
  refine (@full_zero_reach_unary
    (length (ilz_subformulas goal)) ILZMachineState
    (compile_ilz_machine goal)
    (@mk_unary (length (ilz_subformulas goal))
      (ilz_machine_sequent support conclusion)
      (formula_add (ilz_subformulas goal) A)
      (ilz_machine_sequent support conclusion))
    (encode_counter_context (ilz_subformulas goal) frame)
    (encode_counter_context (ilz_subformulas goal) (frame ++ [A])) _ _ Hreach).
  - cbn [compile_ilz_machine]. apply List.in_or_app. right.
    apply List.in_or_app. left. unfold ilz_store_rules.
    apply List.in_flat_map.
    exists (ilz_machine_sequent support conclusion). split.
    + apply ilz_sequent_state_in; assumption.
    + apply List.in_flat_map. exists (IF.ioc A). split.
      * now apply ilz_guarded_subformula_in.
      * cbn. unfold add_support.
        destruct (in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec
          A support); [|contradiction].
        now right; left.
  - rewrite encode_counter_context_app, nvec_add_comm_reduction.
    apply formula_add_application.
Qed.

Lemma oc_right_reach : forall goal support context A,
  List.In support (ilz_supports goal) ->
  List.In (IF.ioc A) (ilz_subformulas goal) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support A)
    (nvec_zero (length (ilz_subformulas goal))) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support (IF.ioc A))
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (List.map IF.ioc context))).
Proof.
  intros goal support context A Hsupport Hioc Hreach.
  assert (Hzero : encode_counter_context (ilz_subformulas goal)
      (linear_context (List.map IF.ioc context)) =
      nvec_zero (length (ilz_subformulas goal))).
  { induction context as [|head tail IH]; cbn; [apply encode_counter_context_nil|].
    exact IH. }
  rewrite Hzero.
  refine (@full_zero_reach_test
    (length (ilz_subformulas goal)) ILZMachineState
    (compile_ilz_machine goal)
    (mk_zero (ilz_machine_sequent support (IF.ioc A))
      (ilz_machine_sequent support A)) _ Hreach).
  cbn [compile_ilz_machine]. unfold ilz_zero_rules.
  apply List.in_flat_map. exists support. split; [exact Hsupport|].
  apply List.in_flat_map. exists (IF.ioc A). split; [exact Hioc|].
  cbn. now left.
Qed.

Lemma fold_add_support_absorbed : forall added support,
  List.incl added support ->
  List.fold_right add_support support added = support.
Proof.
  induction added as [|head tail IH]; intros support Hincl; cbn; [reflexivity|].
  rewrite IH by (intros A HA; apply Hincl; now right).
  unfold add_support.
  destruct (in_dec Mell.Reduction.ILZRuntime.runtime_iformula_eq_dec
    head support); [reflexivity|].
  exfalso. apply n. apply Hincl. now left.
Qed.

Lemma lmap_left_reach : forall goal support left_context before after conclusion A B,
  List.In support (ilz_supports goal) ->
  List.In (IF.ilmap A B) (ilz_subformulas goal) ->
  List.In conclusion (ilz_subformulas goal) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support A)
    (encode_counter_context (ilz_subformulas goal)
      (linear_context left_context)) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent (store_context_support support [B]) conclusion)
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (before ++ B :: after))) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support conclusion)
    (encode_counter_context (ilz_subformulas goal)
      (linear_context
        (before ++ left_context ++ IF.ilmap A B :: after))).
Proof.
  intros goal support left_context before after conclusion A B Hsupport Hlmap
    Hconclusion Hleft Hright.
  assert (HA : List.In A (ilz_subformulas goal)).
  { eapply ilz_subformula_child; [exact Hlmap|].
    apply IF.isub_lmap_l. constructor. }
  assert (HB : List.In B (ilz_subformulas goal)).
  { eapply ilz_subformula_child; [exact Hlmap|].
    apply IF.isub_lmap_r. constructor. }
  assert (Hright_raw : FullZeroReach (compile_ilz_machine goal)
      (ilz_machine_sequent support conclusion)
      (encode_counter_context (ilz_subformulas goal)
        (linear_context before ++ B :: linear_context after))).
  { assert (Hstored : FullZeroReach (compile_ilz_machine goal)
        (ilz_machine_sequent support conclusion)
        (encode_counter_context (ilz_subformulas goal)
          ((linear_context before ++ linear_context after) ++ [B]))).
    { eapply store_context_reach_frame with
        (context := [B]) (frame := linear_context before ++ linear_context after).
      - exact Hsupport.
      - exact Hconclusion.
      - repeat constructor; assumption.
      - rewrite <- !linear_context_app.
        assert (Hperm : Permutation (before ++ B :: after)
            ((before ++ after) ++ [B])).
        { repeat rewrite <- List.app_assoc. apply Permutation_app_head.
          change (Permutation ([B] ++ after) (after ++ [B])).
          apply Permutation_app_comm. }
        rewrite <- (encode_counter_context_permutation
          (ilz_subformulas goal) _ _
          (linear_context_permutation _ _ Hperm)). exact Hright. }
    rewrite (encode_counter_context_permutation
      (ilz_subformulas goal)
      (linear_context before ++ B :: linear_context after)
      ((linear_context before ++ linear_context after) ++ [B])).
    - exact Hstored.
    - repeat rewrite <- List.app_assoc. apply Permutation_app_head.
      change (Permutation ([B] ++ linear_context after)
        (linear_context after ++ [B])). apply Permutation_app_comm. }
  set (right_counter := encode_counter_context (ilz_subformulas goal)
    (linear_context before ++ linear_context after)).
  assert (Hpending : FullZeroReach (compile_ilz_machine goal)
      (ilz_machine_lmap_right support conclusion B) right_counter).
  { refine (@full_zero_reach_unary
      (length (ilz_subformulas goal)) ILZMachineState
      (compile_ilz_machine goal)
      (@mk_unary (length (ilz_subformulas goal))
        (ilz_machine_lmap_right support conclusion B)
        (formula_add (ilz_subformulas goal) B)
        (ilz_machine_sequent support conclusion))
      right_counter
      (encode_counter_context (ilz_subformulas goal)
        (linear_context before ++ B :: linear_context after)) _ _ Hright_raw).
    - cbn [compile_ilz_machine]. apply List.in_or_app. right.
      apply List.in_or_app. right. apply List.in_or_app. right.
      unfold ilz_lmap_split_unary_rules. apply List.in_flat_map.
      exists support. split; [exact Hsupport|]. apply List.in_flat_map.
      exists support. split; [exact Hsupport|]. apply List.in_flat_map.
      exists (IF.ilmap A B). split; [exact Hlmap|]. cbn.
      apply List.in_flat_map. exists conclusion. split; [exact Hconclusion|].
      now right; left.
    - unfold right_counter.
      rewrite !encode_counter_context_app, encode_counter_context_cons.
      replace (nvec_add
        (encode_counter_context (ilz_subformulas goal) (linear_context before))
        (nvec_add (encode_counter_context (ilz_subformulas goal) [B])
          (encode_counter_context (ilz_subformulas goal) (linear_context after))))
        with (nvec_add (encode_counter_context (ilz_subformulas goal) [B])
          (nvec_add
            (encode_counter_context (ilz_subformulas goal) (linear_context before))
            (encode_counter_context (ilz_subformulas goal) (linear_context after)))).
      + apply formula_add_application.
      + rewrite <- !nvec_add_assoc. f_equal.
        apply nvec_add_comm_reduction. }
  set (left_counter := encode_counter_context (ilz_subformulas goal)
    (linear_context left_context)).
  set (split_counter := nvec_add left_counter right_counter).
  assert (Hsplit : FullZeroReach (compile_ilz_machine goal)
      (ilz_machine_split (ilz_machine_sequent support A)
        (ilz_machine_lmap_right support conclusion B)) split_counter).
  { refine (@full_zero_reach_split
      (length (ilz_subformulas goal)) ILZMachineState
      (compile_ilz_machine goal)
      (mk_split
        (ilz_machine_split (ilz_machine_sequent support A)
          (ilz_machine_lmap_right support conclusion B))
        (ilz_machine_sequent support A)
        (ilz_machine_lmap_right support conclusion B))
      split_counter left_counter right_counter _ eq_refl _ _).
    - cbn [compile_ilz_machine]. unfold ilz_split_rules.
      apply List.in_or_app. right. apply List.in_flat_map.
      exists support. split; [exact Hsupport|]. apply List.in_flat_map.
      exists support. split; [exact Hsupport|]. apply List.in_flat_map.
      exists A. split; [exact HA|]. apply List.in_flat_map.
      exists B. split; [exact HB|]. apply List.in_map_iff.
      exists conclusion. split; [reflexivity|exact Hconclusion].
    - exact Hleft.
    - exact Hpending. }
  rewrite !linear_context_app. cbn [linear_context].
  refine (@full_zero_reach_unary
    (length (ilz_subformulas goal)) ILZMachineState
    (compile_ilz_machine goal)
    (@mk_unary (length (ilz_subformulas goal))
      (ilz_machine_sequent support conclusion)
      (formula_remove (ilz_subformulas goal) (IF.ilmap A B))
      (ilz_machine_split (ilz_machine_sequent support A)
        (ilz_machine_lmap_right support conclusion B)))
    (encode_counter_context (ilz_subformulas goal)
      (linear_context before ++ linear_context left_context ++
       IF.ilmap A B :: linear_context after))
    split_counter _ _ Hsplit).
  - cbn [compile_ilz_machine]. apply List.in_or_app. right.
    apply List.in_or_app. right. apply List.in_or_app. right.
    unfold ilz_lmap_split_unary_rules. apply List.in_flat_map.
    exists support. split; [exact Hsupport|]. apply List.in_flat_map.
    exists support. split; [exact Hsupport|]. apply List.in_flat_map.
    exists (IF.ilmap A B). split; [exact Hlmap|]. cbn.
    apply List.in_flat_map. exists conclusion. split; [exact Hconclusion|].
    rewrite fold_add_support_absorbed by apply List.incl_refl. now left.
  - unfold split_counter, left_counter, right_counter.
    set (rest := linear_context before ++ linear_context left_context ++
      linear_context after).
    assert (Hperm : Permutation rest
        (linear_context left_context ++
         (linear_context before ++ linear_context after))).
    { unfold rest. apply Permutation_app_swap_app. }
    assert (Heq : nvec_add
        (encode_counter_context (ilz_subformulas goal)
          (linear_context left_context))
        (encode_counter_context (ilz_subformulas goal)
          (linear_context before ++ linear_context after)) =
        encode_counter_context (ilz_subformulas goal) rest).
    { rewrite <- encode_counter_context_app.
      symmetry. now apply encode_counter_context_permutation. }
    rewrite Heq.
    assert (Hsource : encode_counter_context (ilz_subformulas goal)
        (linear_context before ++ linear_context left_context ++
          IF.ilmap A B :: linear_context after) =
        nvec_add (encode_counter_context (ilz_subformulas goal) [IF.ilmap A B])
          (encode_counter_context (ilz_subformulas goal) rest)).
    { rewrite <- encode_counter_context_cons.
      apply encode_counter_context_permutation.
      unfold rest. symmetry.
      replace (IF.ilmap A B ::
          linear_context before ++ linear_context left_context ++
          linear_context after)
        with ([IF.ilmap A B] ++
          (linear_context before ++ linear_context left_context) ++
          linear_context after) by (cbn; now rewrite List.app_assoc).
      replace (linear_context before ++
          linear_context left_context ++ IF.ilmap A B :: linear_context after)
        with ((linear_context before ++ linear_context left_context) ++
          [IF.ilmap A B] ++ linear_context after)
        by (symmetry; apply List.app_assoc).
      apply Permutation_app_swap_app. }
    rewrite Hsource. apply formula_remove_application.
Qed.

Lemma support_in_store_context : forall support context,
  List.incl support (store_context_support support context).
Proof.
  intros support context; revert support.
  induction context as [|head tail IH]; intros support A HA; cbn.
  - exact HA.
  - destruct head; try now apply IH.
    apply IH. apply add_support_in. now right.
Qed.

Lemma guarded_exposed_in_store : forall support before exposed after,
  List.incl (context_guarded_bodies (before ++ after)) support ->
  List.incl (context_guarded_bodies (before ++ exposed ++ after))
    (store_context_support support exposed).
Proof.
  intros support before exposed after Hguard A HA.
  apply context_guarded_bodies_in in HA.
  apply List.in_app_iff in HA as [HA | HA].
  - apply support_in_store_context, Hguard.
    apply context_guarded_bodies_in. apply List.in_app_iff. now left.
  - apply List.in_app_iff in HA as [HA | HA].
    + apply context_guarded_bodies_in_store.
      apply context_guarded_bodies_in. exact HA.
    + apply support_in_store_context, Hguard.
      apply context_guarded_bodies_in. apply List.in_app_iff. now right.
Qed.

Lemma guarded_remove_middle : forall before principal after support,
  List.incl (context_guarded_bodies (before ++ principal :: after)) support ->
  List.incl (context_guarded_bodies (before ++ after)) support.
Proof.
  intros before principal after support Hguard A HA.
  apply Hguard. apply context_guarded_bodies_in.
  apply context_guarded_bodies_in in HA.
  apply List.in_app_iff in HA as [HA | HA].
  - apply List.in_app_iff. now left.
  - apply List.in_app_iff. right. now right.
Qed.

Lemma dereliction_normalized_reach : forall goal support before after conclusion A,
  List.In support (ilz_supports goal) ->
  List.In conclusion (ilz_subformulas goal) ->
  List.In (IF.ioc A) (ilz_subformulas goal) ->
  List.In A support ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent (store_context_support support [A]) conclusion)
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (before ++ A :: after))) ->
  FullZeroReach (compile_ilz_machine goal)
    (ilz_machine_sequent support conclusion)
    (encode_counter_context (ilz_subformulas goal)
      (linear_context (before ++ IF.ioc A :: after))).
Proof.
  intros goal support before after conclusion A Hsupport Hconclusion Hioc HA Hreach.
  assert (Hraw : FullZeroReach (compile_ilz_machine goal)
      (ilz_machine_sequent support conclusion)
      (encode_counter_context (ilz_subformulas goal)
        ((linear_context before ++ linear_context after) ++ [A]))).
  { eapply store_context_reach_frame with
      (context := [A]) (frame := linear_context before ++ linear_context after).
    - exact Hsupport.
    - exact Hconclusion.
    - constructor.
      + eapply ilz_subformula_child; [exact Hioc|].
        apply IF.isub_oc. constructor.
      + constructor.
    - rewrite <- !linear_context_app.
      assert (Hperm : Permutation (before ++ A :: after)
          ((before ++ after) ++ [A])).
      { repeat rewrite <- List.app_assoc. apply Permutation_app_head.
        change (Permutation ([A] ++ after) (after ++ [A])).
        apply Permutation_app_comm. }
      rewrite <- (encode_counter_context_permutation
        (ilz_subformulas goal) _ _
        (linear_context_permutation _ _ Hperm)). exact Hreach. }
  assert (Hcopy := support_copy_reach goal support
    (linear_context before ++ linear_context after) conclusion A
    Hsupport Hconclusion Hioc HA Hraw).
  rewrite !linear_context_app. cbn [linear_context]. exact Hcopy.
Qed.

Lemma encode_linear_map_ioc_zero : forall subformulas context,
  encode_counter_context subformulas
    (linear_context (List.map IF.ioc context)) =
  nvec_zero (length subformulas).
Proof.
  intros subformulas context; induction context as [|head tail IH]; cbn.
  - apply encode_counter_context_nil.
  - exact IH.
Qed.

Theorem ilz_machine_complete_derivation : forall goal context conclusion
    (derivation : Yalla.ill_cut.ill_ll context conclusion),
  List.Forall (fun A =>
    List.In A (ilz_subformulas goal) /\ MELLILZFormula A) context ->
  List.In conclusion (ilz_subformulas goal) ->
  MELLILZFormula conclusion ->
  ILZMachineCompleteAt goal context conclusion.
Proof.
  intros goal context conclusion derivation.
  induction derivation; intros Hall Hconclusion Hformula.
  - unfold ILZMachineCompleteAt. intros support Hsupport Hguard.
    now apply initial_variable_reach.
  - cbn in p. apply Permutation_Type_Permutation in p.
    apply ilz_machine_complete_at_permutation with (left := l1).
    + exact p.
    + apply IHderivation.
      * eapply forall_permutation; [symmetry; exact p|exact Hall].
      * exact Hconclusion.
      * exact Hformula.
  - apply Permutation_Type_Permutation in p.
    assert (Hperm : Permutation
        (l1 ++ List.map IF.ioc lw ++ l2)
        (l1 ++ List.map IF.ioc lw' ++ l2)).
    { apply Permutation_app_head, Permutation_app_tail.
      now apply Permutation_map. }
    apply ilz_machine_complete_at_permutation with
      (left := l1 ++ List.map IF.ioc lw ++ l2).
    + exact Hperm.
    + apply IHderivation.
      * eapply forall_permutation; [symmetry; exact Hperm|exact Hall].
      * exact Hconclusion.
      * exact Hformula.
  - unfold ILZMachineCompleteAt. intros support Hsupport Hguard.
    cbn [linear_context]. rewrite encode_counter_context_nil.
    apply initial_one_reach; assumption.
  - apply List.Forall_app in Hall as [Hleft Hrest].
    inversion Hrest as [|? ? Hone Hright]; subst.
    assert (Hpremise : List.Forall (fun X =>
        List.In X (ilz_subformulas goal) /\ MELLILZFormula X) (l1 ++ l2)).
    { apply List.Forall_app. now split. }
    pose proof (IHderivation Hpremise Hconclusion Hformula) as Hcomplete.
    unfold ILZMachineCompleteAt in *. intros support Hsupport Hguard.
    apply one_left_reach; [exact Hsupport|exact (proj1 Hone)|exact Hconclusion|].
    apply Hcomplete; [exact Hsupport|].
    apply guarded_remove_middle with (principal := IF.ione). exact Hguard.
  - apply List.Forall_app in Hall as [Hleft Hright].
    inversion Hformula; subst.
    assert (HA : List.In A (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Hconclusion|].
      apply IF.isub_tens_l. constructor. }
    assert (HB : List.In B (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Hconclusion|].
      apply IF.isub_tens_r. constructor. }
    pose proof (IHderivation1 Hleft HA H1) as Hcomplete_left.
    pose proof (IHderivation2 Hright HB H2) as Hcomplete_right.
    unfold ILZMachineCompleteAt in *. intros support Hsupport Hguard.
    eapply tensor_right_reach.
    + exact Hsupport.
    + exact Hconclusion.
    + apply Hcomplete_left; [exact Hsupport|].
      apply context_guarded_bodies_incl_app_left with (right := l2). exact Hguard.
    + apply Hcomplete_right; [exact Hsupport|].
      apply context_guarded_bodies_incl_app_right with (left := l1). exact Hguard.
  - assert (Hprincipal : List.In (IF.itens A B) (ilz_subformulas goal) /\
        MELLILZFormula (IF.itens A B)).
    { apply (proj1 (List.Forall_forall _ _) Hall).
      apply List.in_app_iff. right. now left. }
    destruct Hprincipal as [Htens Htens_fragment]. inversion Htens_fragment; subst.
    assert (HA : List.In A (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Htens|].
      apply IF.isub_tens_l. constructor. }
    assert (HB : List.In B (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Htens|].
      apply IF.isub_tens_r. constructor. }
    assert (Hpremise : List.Forall (fun X =>
        List.In X (ilz_subformulas goal) /\ MELLILZFormula X)
        (l1 ++ A :: B :: l2)).
    { apply List.Forall_forall. intros X HX.
      apply List.in_app_iff in HX as [HX | HX].
      - exact ((proj1 (List.Forall_forall _ _) Hall) X
          (List.in_or_app _ _ _ (or_introl HX))).
      - destruct HX as [<- | [<- | HX]]; [now split|now split|].
        apply (proj1 (List.Forall_forall _ _) Hall).
        apply List.in_app_iff. right. now right. }
    pose proof (IHderivation Hpremise Hconclusion Hformula) as Hcomplete.
    unfold ILZMachineCompleteAt in *. intros support Hsupport Hguard.
    apply tensor_left_reach; [exact Hsupport|exact Htens|exact Hconclusion|].
    apply Hcomplete.
    + apply store_context_support_in; [exact Hsupport|].
      repeat constructor; assumption.
    + eapply guarded_exposed_in_store with
        (before := l1) (exposed := [A; B]) (after := l2).
      eapply guarded_remove_middle; exact Hguard.
  - inversion Hformula.
  - assert (Hbad : MELLILZFormula (IF.ilpam A B)).
    { destruct ((proj1 (List.Forall_forall _ _) Hall) (IF.ilpam A B)
        ltac:(apply List.in_app_iff; right; now left)) as [_ Hbad]. exact Hbad. }
    inversion Hbad.
  - inversion Hformula.
  - assert (Hbad : MELLILZFormula (IF.igen A)).
    { destruct ((proj1 (List.Forall_forall _ _) Hall) (IF.igen A)
        ltac:(now left)) as [_ Hbad]. exact Hbad. }
    inversion Hbad.
  - inversion Hformula; subst.
    assert (HA : List.In A (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Hconclusion|].
      apply IF.isub_lmap_l. constructor. }
    assert (HB : List.In B (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Hconclusion|].
      apply IF.isub_lmap_r. constructor. }
    assert (Hpremise : List.Forall (fun X =>
        List.In X (ilz_subformulas goal) /\ MELLILZFormula X) (A :: l)).
    { constructor; [now split|exact Hall]. }
    pose proof (IHderivation Hpremise HB H2) as Hcomplete.
    unfold ILZMachineCompleteAt in *. intros support Hsupport Hguard.
    apply lmap_right_reach; [exact Hsupport|exact Hconclusion|].
    apply Hcomplete.
    + apply store_context_support_in; [exact Hsupport|].
      constructor; [exact HA|constructor].
    + apply guarded_exposed_in_store with
        (before := []) (exposed := [A]) (after := l).
      cbn. exact Hguard.
  - assert (Hprincipal : List.In (IF.ilmap A B) (ilz_subformulas goal) /\
        MELLILZFormula (IF.ilmap A B)).
    { apply (proj1 (List.Forall_forall _ _) Hall).
      apply List.in_app_iff. right. apply List.in_app_iff. right. now left. }
    destruct Hprincipal as [Hlmap Hlmap_fragment]. inversion Hlmap_fragment; subst.
    assert (HA : List.In A (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Hlmap|].
      apply IF.isub_lmap_l. constructor. }
    assert (HB : List.In B (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Hlmap|].
      apply IF.isub_lmap_r. constructor. }
    assert (Hleft_all : List.Forall (fun X =>
        List.In X (ilz_subformulas goal) /\ MELLILZFormula X) l0).
    { apply List.Forall_forall. intros X HX.
      apply (proj1 (List.Forall_forall _ _) Hall).
      apply List.in_app_iff. right. apply List.in_app_iff. now left. }
    assert (Hright_all : List.Forall (fun X =>
        List.In X (ilz_subformulas goal) /\ MELLILZFormula X)
        (l1 ++ B :: l2)).
    { apply List.Forall_forall. intros X HX.
      apply List.in_app_iff in HX as [HX | [<- | HX]].
      - apply (proj1 (List.Forall_forall _ _) Hall).
        apply List.in_app_iff. now left.
      - now split.
      - apply (proj1 (List.Forall_forall _ _) Hall).
        apply List.in_app_iff. right. apply List.in_app_iff. right. now right. }
    pose proof (IHderivation1 Hleft_all HA H1) as Hcomplete_left.
    pose proof (IHderivation2 Hright_all Hconclusion Hformula) as Hcomplete_right.
    unfold ILZMachineCompleteAt in *. intros support Hsupport Hguard.
    eapply lmap_left_reach.
    + exact Hsupport.
    + exact Hlmap.
    + exact Hconclusion.
    + apply Hcomplete_left; [exact Hsupport|].
      intros body Hbody. apply Hguard. apply context_guarded_bodies_in.
      apply context_guarded_bodies_in in Hbody.
      apply List.in_app_iff. right. apply List.in_app_iff. now left.
    + apply Hcomplete_right.
      * apply store_context_support_in; [exact Hsupport|].
        constructor; [exact HB|constructor].
      * intros body Hbody. apply context_guarded_bodies_in in Hbody.
        apply List.in_app_iff in Hbody as [Hbody | [Hbody | Hbody]].
        -- apply support_in_store_context, Hguard.
           apply context_guarded_bodies_in. apply List.in_app_iff. now left.
        -- subst B. apply context_guarded_bodies_in_store.
           apply context_guarded_bodies_in. now left.
        -- apply support_in_store_context, Hguard.
           apply context_guarded_bodies_in. apply List.in_app_iff. right.
           apply List.in_app_iff. right. now right.
  - inversion Hformula.
  - assert (Hbad : MELLILZFormula (IF.ineg A)).
    { destruct ((proj1 (List.Forall_forall _ _) Hall) (IF.ineg A)
        ltac:(apply List.in_app_iff; right; now left)) as [_ Hbad]. exact Hbad. }
    inversion Hbad.
  - inversion Hformula.
  - inversion Hformula.
  - assert (Hbad : MELLILZFormula (IF.iwith A B)).
    { destruct ((proj1 (List.Forall_forall _ _) Hall) (IF.iwith A B)
        ltac:(apply List.in_app_iff; right; now left)) as [_ Hbad]. exact Hbad. }
    inversion Hbad.
  - assert (Hbad : MELLILZFormula (IF.iwith B A)).
    { destruct ((proj1 (List.Forall_forall _ _) Hall) (IF.iwith B A)
        ltac:(apply List.in_app_iff; right; now left)) as [_ Hbad]. exact Hbad. }
    inversion Hbad.
  - assert (Hbad : MELLILZFormula IF.izero).
    { destruct ((proj1 (List.Forall_forall _ _) Hall) IF.izero
        ltac:(apply List.in_app_iff; right; now left)) as [_ Hbad]. exact Hbad. }
    inversion Hbad.
  - inversion Hformula.
  - inversion Hformula.
  - assert (Hbad : MELLILZFormula (IF.iplus A B)).
    { destruct ((proj1 (List.Forall_forall _ _) Hall) (IF.iplus A B)
        ltac:(apply List.in_app_iff; right; now left)) as [_ Hbad]. exact Hbad. }
    inversion Hbad.
  - inversion Hformula as [| | | | ? HA_fragment]; subst.
    assert (HA : List.In A (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Hconclusion|].
      apply IF.isub_oc. constructor. }
    pose proof (IHderivation Hall HA HA_fragment) as Hcomplete.
    unfold ILZMachineCompleteAt in *. intros support Hsupport Hguard.
    apply oc_right_reach with (context := l); [exact Hsupport|exact Hconclusion|].
    specialize (Hcomplete support Hsupport Hguard).
    now rewrite encode_linear_map_ioc_zero in Hcomplete.
  - assert (Hioc : List.In (IF.ioc A) (ilz_subformulas goal) /\
        MELLILZFormula (IF.ioc A)).
    { apply (proj1 (List.Forall_forall _ _) Hall).
      apply List.in_app_iff. right. now left. }
    destruct Hioc as [Hioc Hioc_fragment]. inversion Hioc_fragment; subst.
    assert (HA : List.In A (ilz_subformulas goal)).
    { eapply ilz_subformula_child; [exact Hioc|].
      apply IF.isub_oc. constructor. }
    assert (Hpremise : List.Forall (fun X =>
        List.In X (ilz_subformulas goal) /\ MELLILZFormula X)
        (l1 ++ A :: l2)).
    { apply List.Forall_forall. intros X HX.
      apply List.in_app_iff in HX as [HX | [<- | HX]].
      - apply (proj1 (List.Forall_forall _ _) Hall).
        apply List.in_app_iff. now left.
      - now split.
      - apply (proj1 (List.Forall_forall _ _) Hall).
        apply List.in_app_iff. right. now right. }
    pose proof (IHderivation Hpremise Hconclusion Hformula) as Hcomplete.
    unfold ILZMachineCompleteAt in *. intros support Hsupport Hguard.
    apply dereliction_normalized_reach;
      [exact Hsupport|exact Hconclusion|exact Hioc| |].
    + apply Hguard. apply context_guarded_bodies_in.
      apply List.in_app_iff. right. now left.
    + apply Hcomplete.
      * apply store_context_support_in; [exact Hsupport|].
        constructor; [exact HA|constructor].
      * eapply guarded_exposed_in_store with
          (before := l1) (exposed := [A]) (after := l2).
        eapply guarded_remove_middle; exact Hguard.
  - assert (Hpremise : List.Forall (fun X =>
        List.In X (ilz_subformulas goal) /\ MELLILZFormula X) (l1 ++ l2)).
    { apply List.Forall_forall. intros X HX.
      apply (proj1 (List.Forall_forall _ _) Hall).
      apply List.in_app_iff in HX as [HX | HX].
      * apply List.in_app_iff. now left.
      * apply List.in_app_iff. right. now right. }
    pose proof (IHderivation Hpremise Hconclusion Hformula) as Hcomplete.
    unfold ILZMachineCompleteAt in *. intros support Hsupport Hguard.
    specialize (Hcomplete support Hsupport).
    rewrite !linear_context_app in Hcomplete |- *. cbn [linear_context] in Hcomplete |- *.
    apply Hcomplete. eapply guarded_remove_middle; exact Hguard.
  - assert (Hpremise : List.Forall (fun X =>
        List.In X (ilz_subformulas goal) /\ MELLILZFormula X)
        (l1 ++ IF.ioc A :: IF.ioc A :: l2)).
    { apply List.Forall_forall. intros X HX.
      apply List.in_app_iff in HX as [HX | [HX | [HX | HX]]].
      * apply (proj1 (List.Forall_forall _ _) Hall).
        apply List.in_app_iff. now left.
      * subst X. apply (proj1 (List.Forall_forall _ _) Hall).
        apply List.in_app_iff. right. now left.
      * subst X. apply (proj1 (List.Forall_forall _ _) Hall).
        apply List.in_app_iff. right. now left.
      * apply (proj1 (List.Forall_forall _ _) Hall).
        apply List.in_app_iff. right. now right. }
    pose proof (IHderivation Hpremise Hconclusion Hformula) as Hcomplete.
    unfold ILZMachineCompleteAt in *. intros support Hsupport Hguard.
    specialize (Hcomplete support Hsupport).
    rewrite !linear_context_app in Hcomplete |- *. cbn [linear_context] in Hcomplete |- *.
    apply Hcomplete. intros body Hbody. apply Hguard.
    apply context_guarded_bodies_in. apply context_guarded_bodies_in in Hbody.
    apply List.in_app_iff in Hbody as [Hbody | [Hbody | [Hbody | Hbody]]].
    + apply List.in_app_iff. now left.
    + subst. apply List.in_app_iff. right. now left.
    + subst. apply List.in_app_iff. right. now left.
    + apply List.in_app_iff. right. now right.
  - discriminate f.
  - destruct a.
Qed.

Lemma translated_formula_fragment : forall parameter source,
  MELLILZFormula parameter ->
  MELLILZFormula
    (Yalla.nn_def.trans parameter
      (Yalla.mell_mset.mell2ll (to_yalla source))).
Proof.
  intros parameter source Hparameter. induction source; cbn.
  - constructor; [constructor|exact Hparameter].
  - constructor.
  - constructor; [constructor|exact Hparameter].
  - constructor.
  - constructor; [|exact Hparameter]. constructor.
    + constructor; [exact IHsource1|exact Hparameter].
    + constructor; [exact IHsource2|exact Hparameter].
  - constructor; [exact IHsource2|exact IHsource1].
  - constructor; [|exact Hparameter]. constructor.
    constructor; [exact IHsource|exact Hparameter].
  - constructor. constructor.
    + constructor; [exact IHsource|exact Hparameter].
    + exact Hparameter.
Qed.

Lemma classical_linear_sequent_fragment : forall Gamma parameter,
  MELLILZFormula parameter ->
  List.Forall (fun formula =>
    MELLILZFormula (Yalla.nn_def.trans parameter formula))
    (classical_linear_sequent Gamma).
Proof.
  intros Gamma parameter Hparameter. apply List.Forall_forall.
  intros formula Hformula.
  rewrite classical_linear_sequent_reference in Hformula.
  apply List.in_map_iff in Hformula as [source [<- Hsource]].
  unfold to_yalla_sequent in Hsource.
  pose proof (@Yalla.OLlibs.fmsetlist_Type.elts_perm
    yalla_sequent Yalla.mell_mset.formula Yalla.mell_mset.fmset_formula
    (List.map to_yalla Gamma)) as Hperm.
  apply Permutation_Type_Permutation in Hperm.
  apply (Permutation_in source Hperm) in Hsource.
  apply List.in_map_iff in Hsource as [original [<- Horiginal]].
  apply translated_formula_fragment. exact Hparameter.
Qed.

Lemma close_ilz_context_fragment : forall context conclusion,
  List.Forall MELLILZFormula context ->
  MELLILZFormula conclusion ->
  MELLILZFormula (close_ilz_context context conclusion).
Proof.
  induction context as [|head tail IH]; intros conclusion Hall Hconclusion; cbn.
  - exact Hconclusion.
  - inversion Hall as [|? ? Hhead Htail]; subst.
    apply IH; [exact Htail|]. constructor; assumption.
Qed.

Lemma translate_mell_conclusion_fragment : forall Gamma,
  MELLILZFormula (snd (translate_mell Gamma)).
Proof.
  intro Gamma. unfold translate_mell; cbn.
  apply close_ilz_context_fragment.
  - apply List.Forall_map, classical_linear_sequent_fragment. constructor.
  - constructor.
Qed.

Lemma translate_mell_conclusion_in : forall Gamma,
  List.In (snd (translate_mell Gamma))
    (ilz_subformulas (translate_mell Gamma)).
Proof.
  intro Gamma. eapply ilz_subformulas_complete.
  - unfold ilz_goal_formulas. now left.
  - constructor.
Qed.

Theorem ilz_machine_complete : forall Gamma,
  ILZProvable (translate_mell Gamma) ->
  ilz_machine_accepts (translate_mell Gamma).
Proof.
  intros Gamma [derivation].
  pose proof (ilz_machine_complete_derivation
    (translate_mell Gamma) (fst (translate_mell Gamma))
    (snd (translate_mell Gamma)) derivation) as Hcomplete.
  rewrite translate_mell_fragment in Hcomplete.
  specialize (Hcomplete (Forall_nil _) (translate_mell_conclusion_in Gamma)
    (translate_mell_conclusion_fragment Gamma)).
  unfold ILZMachineCompleteAt in Hcomplete.
  assert (Hempty : List.In [] (ilz_supports (translate_mell Gamma))).
  { apply ilz_supports_complete; [constructor|]. intros A HA. contradiction. }
  specialize (Hcomplete [] Hempty ltac:(intros A HA; contradiction)).
  unfold ilz_machine_accepts.
  cbn [linear_context] in Hcomplete.
  now rewrite encode_counter_context_nil in Hcomplete.
Qed.

Theorem ilz_machine_correct : forall Gamma,
  ILZProvable (translate_mell Gamma) <->
  ilz_machine_accepts (translate_mell Gamma).
Proof.
  intro Gamma; split.
  - apply ilz_machine_complete.
  - apply ilz_machine_sound. apply translate_mell_fragment.
Qed.
