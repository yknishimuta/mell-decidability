From Coq Require Import List Vector ZArith Bool.
From Mell.Core Require Import Vector.
From Mell.Reduction Require Import FullZeroSystem ILZRuntime.

Import ListNotations.
Module RuntimeMachineIF := Yalla.iformulas.

Inductive ILZMachineState : Type :=
| ilz_machine_sequent : list RuntimeMachineIF.iformula ->
    RuntimeMachineIF.iformula -> ILZMachineState
| ilz_machine_split : ILZMachineState -> ILZMachineState -> ILZMachineState
| ilz_machine_contract : list RuntimeMachineIF.iformula ->
    RuntimeMachineIF.iformula -> RuntimeMachineIF.iformula -> ILZMachineState
| ilz_machine_lmap_right : list RuntimeMachineIF.iformula ->
    RuntimeMachineIF.iformula -> RuntimeMachineIF.iformula -> ILZMachineState
| ilz_machine_leaf : ILZMachineState.

Definition is_ioc (formula : RuntimeMachineIF.iformula) : bool :=
  match formula with RuntimeMachineIF.ioc _ => true | _ => false end.

Fixpoint list_powerset {A : Type} (values : list A) : list (list A) :=
  match values with
  | [] => [[]]
  | value :: tail =>
      let subsets := list_powerset tail in
      subsets ++ List.map (List.cons value) subsets
  end.

Fixpoint list_insertions {A : Type} (value : A) (values : list A) :
    list (list A) :=
  match values with
  | [] => [[value]]
  | head :: tail =>
      (value :: head :: tail) ::
      List.map (List.cons head) (list_insertions value tail)
  end.

Fixpoint list_permutations {A : Type} (values : list A) : list (list A) :=
  match values with
  | [] => [[]]
  | head :: tail =>
      List.flat_map (list_insertions head) (list_permutations tail)
  end.

Definition ilz_guarded_subformulas (goal : RuntimeILZGoal) :
    list RuntimeMachineIF.iformula :=
  List.filter is_ioc (runtime_ilz_subformulas goal).

Definition ilz_guarded_bodies (goal : RuntimeILZGoal) :
    list RuntimeMachineIF.iformula :=
  List.flat_map (fun formula =>
    match formula with RuntimeMachineIF.ioc body => [body] | _ => [] end)
    (runtime_ilz_subformulas goal).

Definition ilz_supports (goal : RuntimeILZGoal) :
    list (list RuntimeMachineIF.iformula) :=
  List.flat_map list_permutations
    (list_powerset (ilz_guarded_bodies goal)).

Definition ilz_machine_states (goal : RuntimeILZGoal) : list ILZMachineState :=
  ilz_machine_leaf ::
  List.flat_map (fun support =>
    List.map (ilz_machine_sequent support) (runtime_ilz_subformulas goal))
    (ilz_supports goal).

Definition formula_action (subformulas : list RuntimeMachineIF.iformula)
    (coefficient : Z) (formula : RuntimeMachineIF.iformula) :
    ZVec (length subformulas) :=
  Vector.map
    (fun candidate =>
      if runtime_iformula_eq_dec formula candidate then coefficient else 0%Z)
    (Vector.of_list subformulas).

Definition formula_add (subformulas : list RuntimeMachineIF.iformula)
    (formula : RuntimeMachineIF.iformula) : ZVec (length subformulas) :=
  formula_action subformulas 1 formula.

Definition formula_remove (subformulas : list RuntimeMachineIF.iformula)
    (formula : RuntimeMachineIF.iformula) : ZVec (length subformulas) :=
  formula_action subformulas (-1) formula.

Definition formula_replace (subformulas : list RuntimeMachineIF.iformula)
    (old new : RuntimeMachineIF.iformula) : ZVec (length subformulas) :=
  zvec_add (formula_remove subformulas old) (formula_add subformulas new).

Definition add_support (formula : RuntimeMachineIF.iformula)
    (support : list RuntimeMachineIF.iformula) :=
  if in_dec runtime_iformula_eq_dec formula support
  then support else formula :: support.

Definition support_union (left right : list RuntimeMachineIF.iformula) :
    list RuntimeMachineIF.iformula :=
  List.fold_right add_support right left.

Definition mk_unary {d} source delta target : UnaryZeroRule d ILZMachineState :=
  {| unary_zero_source := source;
     unary_zero_delta := delta;
     unary_zero_target := target |}.

Definition mk_split source left right : SplitZeroRule ILZMachineState :=
  {| split_zero_source := source;
     split_zero_left := left;
     split_zero_right := right |}.

Definition mk_zero source target : FullZeroRule ILZMachineState :=
  {| full_zero_source := source; full_zero_target := target |}.

Definition ilz_sequent_states (goal : RuntimeILZGoal) : list ILZMachineState :=
  List.flat_map (fun support =>
    List.map (ilz_machine_sequent support) (runtime_ilz_subformulas goal))
    (ilz_supports goal).

Definition ilz_store_rules (goal : RuntimeILZGoal) :=
  let subformulas := runtime_ilz_subformulas goal in
  List.flat_map (fun state =>
    match state with
    | ilz_machine_sequent support conclusion =>
        List.flat_map (fun guarded =>
          match guarded with
          | RuntimeMachineIF.ioc body =>
              [mk_unary (ilz_machine_sequent support conclusion)
                 (formula_remove subformulas guarded)
                 (ilz_machine_sequent (add_support body support) conclusion);
               mk_unary (ilz_machine_sequent (add_support body support) conclusion)
                 (formula_add subformulas body)
                 (ilz_machine_sequent (add_support body support) conclusion)]
          | _ => []
          end) (ilz_guarded_subformulas goal)
    | _ => []
    end) (ilz_sequent_states goal).

Definition ilz_logical_unary_rules (goal : RuntimeILZGoal) :=
  let subformulas := runtime_ilz_subformulas goal in
  List.flat_map (fun state =>
    match state with
    | ilz_machine_sequent support conclusion =>
        List.flat_map (fun formula =>
          match formula with
          | RuntimeMachineIF.ione =>
              [mk_unary (ilz_machine_sequent support conclusion)
                 (formula_remove subformulas RuntimeMachineIF.ione)
                 (ilz_machine_sequent support conclusion)]
          | RuntimeMachineIF.itens left_formula right_formula =>
              [mk_unary (ilz_machine_sequent support conclusion)
                 (zvec_add (formula_remove subformulas formula)
                   (zvec_add (formula_add subformulas left_formula)
                     (formula_add subformulas right_formula)))
                 (ilz_machine_sequent support conclusion)]
          | RuntimeMachineIF.ilmap left_formula right_formula =>
              [mk_unary (ilz_machine_sequent support formula)
                 (formula_add subformulas left_formula)
                 (ilz_machine_sequent support right_formula)]
          | RuntimeMachineIF.ineg body =>
              [mk_unary (ilz_machine_sequent support formula)
                 (formula_add subformulas body)
                 (ilz_machine_sequent support RuntimeMachineIF.N);
               mk_unary (ilz_machine_sequent support RuntimeMachineIF.N)
                 (formula_remove subformulas formula)
                 (ilz_machine_sequent support body)]
          | RuntimeMachineIF.ioc body =>
              [mk_unary (ilz_machine_sequent support conclusion)
                 (formula_replace subformulas formula body)
                 (ilz_machine_sequent support conclusion);
               mk_unary (ilz_machine_sequent support conclusion)
                 (formula_remove subformulas formula)
                 (ilz_machine_sequent support conclusion);
               mk_unary (ilz_machine_sequent support conclusion)
                 (formula_remove subformulas formula)
                 (ilz_machine_contract support conclusion body);
               mk_unary (ilz_machine_contract support conclusion body)
                 (zvec_add (formula_add subformulas formula)
                   (formula_add subformulas formula))
                 (ilz_machine_sequent support conclusion)]
          | _ => []
          end) subformulas
    | _ => []
    end) (ilz_sequent_states goal).

Definition ilz_lmap_split_unary_rules (goal : RuntimeILZGoal) :=
  let subformulas := runtime_ilz_subformulas goal in
  let supports := ilz_supports goal in
  List.flat_map (fun left_support =>
    List.flat_map (fun right_support =>
      List.flat_map (fun formula =>
        match formula with
        | RuntimeMachineIF.ilmap left_formula right_formula =>
            List.flat_map (fun conclusion =>
              let left_state :=
                ilz_machine_sequent left_support left_formula in
              let right_pending :=
                ilz_machine_lmap_right right_support conclusion right_formula in
              [mk_unary
                 (ilz_machine_sequent
                   (List.fold_right add_support right_support left_support)
                   conclusion)
                 (formula_remove subformulas formula)
                 (ilz_machine_split left_state right_pending);
               mk_unary right_pending (formula_add subformulas right_formula)
                 (ilz_machine_sequent right_support conclusion)]) subformulas
        | _ => []
        end) subformulas) supports) supports.

Definition ilz_split_rules (goal : RuntimeILZGoal) :=
  let subformulas := runtime_ilz_subformulas goal in
  let supports := ilz_supports goal in
  List.flat_map (fun left_support =>
    List.flat_map (fun right_support =>
      List.flat_map (fun formula =>
        match formula with
        | RuntimeMachineIF.itens left_formula right_formula =>
            [mk_split
              (ilz_machine_sequent
                (List.fold_right add_support right_support left_support) formula)
              (ilz_machine_sequent left_support left_formula)
              (ilz_machine_sequent right_support right_formula)]
        | _ => []
        end) subformulas) supports) supports ++
  List.flat_map (fun left_support =>
    List.flat_map (fun right_support =>
      List.flat_map (fun left_formula =>
        List.flat_map (fun right_formula =>
          List.map (fun conclusion =>
            let left_state :=
              ilz_machine_sequent left_support left_formula in
            let right_pending :=
              ilz_machine_lmap_right right_support conclusion right_formula in
            mk_split (ilz_machine_split left_state right_pending)
              left_state right_pending) subformulas) subformulas) subformulas)
      supports) supports.

Definition ilz_initial_rules (goal : RuntimeILZGoal) :=
  let subformulas := runtime_ilz_subformulas goal in
  List.flat_map (fun support =>
    List.flat_map (fun formula =>
      match formula with
      | RuntimeMachineIF.ivar _ =>
          [mk_unary (ilz_machine_sequent support formula)
             (formula_remove subformulas formula) ilz_machine_leaf]
      | RuntimeMachineIF.ione =>
          [mk_unary (ilz_machine_sequent support RuntimeMachineIF.ione)
             (zvec_zero (length subformulas)) ilz_machine_leaf]
      | RuntimeMachineIF.ioc body =>
          if in_dec runtime_iformula_eq_dec body support then
            [mk_unary (ilz_machine_sequent support formula)
               (zvec_zero (length subformulas)) ilz_machine_leaf]
          else []
      | _ => []
      end) subformulas) (ilz_supports goal).

Definition ilz_zero_rules (goal : RuntimeILZGoal) :=
  List.flat_map (fun support =>
    List.flat_map (fun formula =>
      match formula with
      | RuntimeMachineIF.ioc body =>
          [mk_zero (ilz_machine_sequent support formula)
             (ilz_machine_sequent support body)]
      | _ => []
      end) (runtime_ilz_subformulas goal)) (ilz_supports goal).

Definition compile_ilz_machine (goal : RuntimeILZGoal) :
    FullZeroBVASS (length (runtime_ilz_subformulas goal)) ILZMachineState :=
  {| full_zero_leaves := [ilz_machine_leaf];
     full_zero_unary_rules :=
       ilz_initial_rules goal ++ ilz_store_rules goal ++
       ilz_logical_unary_rules goal ++ ilz_lmap_split_unary_rules goal;
     full_zero_split_rules := ilz_split_rules goal;
     full_zero_test_rules := ilz_zero_rules goal |}.
