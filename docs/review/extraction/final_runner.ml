open Syntax

let nat_of_int = Big_int_Z.big_int_of_int

let nvec1 n =
  Vector.Coq_cons (nat_of_int n, nat_of_int 0, Vector.Coq_nil)

let nvec1_big n =
  Vector.Coq_cons (n, nat_of_int 0, Vector.Coq_nil)

let zvec1 z =
  Vector.Coq_cons (z, nat_of_int 0, Vector.Coq_nil)

let empty_system =
  { System.initial_vectors = []; system_actions = [] }

let initial_zero_system =
  { System.initial_vectors = [nvec1 0]; system_actions = [] }

let unary_plus_two_system =
  { System.initial_vectors = [nvec1 0];
    system_actions =
      [{ System.action_arity = nat_of_int 1; action_offset = zvec1 (nat_of_int 2) }] }

let binary_sum_system =
  { System.initial_vectors = [nvec1 1];
    system_actions =
      [{ System.action_arity = nat_of_int 2; action_offset = zvec1 (nat_of_int 0) }] }

let even_system = unary_plus_two_system

let is_none = function None -> true | Some _ -> false

let string_of_option = function
  | Some answer -> "Some " ^ string_of_bool answer
  | None -> "None"

let mell_decision_path gamma =
  if UnitFragment.unit_sequent_provableb gamma then "unit"
  else if MultiplicativeWeight.multiplicative_weight_refutes gamma then "weight"
  else
    match MELL.mell_goal_saturation_decide gamma with
    | Some true -> "goal-saturation"
    | _ ->
        begin match MELL.mell_full_saturation_decide gamma with
        | Some true -> "full-saturation-true"
        | Some false -> "full-saturation-false"
        | None -> "fallback"
        end

let small_path_scan () =
  let atom n = Atom (nat_of_int n) in
  let coatom n = CoAtom (nat_of_int n) in
  let cases =
    [("par-mismatch", [Par (atom 0, coatom 1)]);
     ("tensor-mismatch", [Tensor (atom 0, One); coatom 1]);
     ("identity-extra-atom", [atom 0; coatom 0; atom 1]);
     ("bottom-one", [Bottom; One]);
     ("two-bottom-one", [Bottom; Bottom; One])] in
  String.concat ";"
    (Stdlib.List.map
      (fun (name, gamma) -> name ^ "=" ^ mell_decision_path gamma)
      cases)

let runtime_machine_summary gamma =
  let goal = ILZRuntime.translate_mell_runtime gamma in
  let machine = MELLToABVASSRuntime.compile_ilz_machine goal in
  String.concat ","
    [string_of_int (Stdlib.List.length (ILZRuntime.runtime_ilz_subformulas goal));
     string_of_int (Stdlib.List.length (MELLToABVASSRuntime.ilz_supports goal));
     string_of_int (Stdlib.List.length machine.FullZeroSystem.full_zero_unary_rules);
     string_of_int (Stdlib.List.length machine.FullZeroSystem.full_zero_split_rules);
     string_of_int (Stdlib.List.length machine.FullZeroSystem.full_zero_test_rules)]

let one_two_step_witness () =
  let instance = Main.reduce_mell [One] in
  let rec scan index = function
    | _front :: _back :: tail ->
        let front_index = nat_of_int (2 * index) in
        let back_index = nat_of_int (2 * index + 1) in
        let leaf = FiniteTree.Coq_tree_leaf (nat_of_int 0) in
        let front = FiniteTree.Coq_tree_node
          (front_index,
           FiniteTree.Coq_forest_cons (leaf, FiniteTree.Coq_forest_nil)) in
        let run = FiniteTree.Coq_tree_node
          (back_index,
           FiniteTree.Coq_forest_cons (front, FiniteTree.Coq_forest_nil)) in
        begin match Certificates.eval_run instance.Main.reach_dimension
          instance.Main.reach_system run with
        | Some value when value = instance.Main.reach_target ->
            Some (index, Code.tree_encode run)
        | _ -> scan (index + 1) tail
        end
    | _ -> None
  in
  scan 0 instance.Main.reach_system.System.system_actions

let one_unary_bfs max_depth =
  let instance = Main.reduce_mell [One] in
  let actions = instance.Main.reach_system.System.system_actions in
  let rec pairs index = function
    | front :: back :: tail -> (index, front, back) :: pairs (index + 1) tail
    | _ -> []
  in
  let rules = pairs 0 actions in
  let leaf = FiniteTree.Coq_tree_leaf (nat_of_int 0) in
  let initial = match Certificates.eval_run instance.Main.reach_dimension
      instance.Main.reach_system leaf with
    | Some value -> [(value, leaf)]
    | None -> []
  in
  let extend (_value, child) (index, front_action, _back_action) =
    if Big_int_Z.eq_big_int front_action.System.action_arity (nat_of_int 1)
    then
      let front = FiniteTree.Coq_tree_node
        (nat_of_int (2 * index),
         FiniteTree.Coq_forest_cons (child, FiniteTree.Coq_forest_nil)) in
      let run = FiniteTree.Coq_tree_node
        (nat_of_int (2 * index + 1),
         FiniteTree.Coq_forest_cons (front, FiniteTree.Coq_forest_nil)) in
      match Certificates.eval_run instance.Main.reach_dimension
        instance.Main.reach_system run with
      | Some result -> Some (result, run)
      | None -> None
    else None
  in
  let rec search depth frontier seen =
    match Stdlib.List.find_opt
      (fun (value, _run) -> value = instance.Main.reach_target) frontier with
    | Some (_value, run) -> Some (depth, Code.tree_encode run)
    | None when depth >= max_depth -> None
    | None ->
        let next = Stdlib.List.map
          (fun item -> Stdlib.List.filter_map (extend item) rules)
          frontier |> Stdlib.List.flatten
        in
        let fresh = Stdlib.List.filter
          (fun (value, _run) ->
             not (Stdlib.List.exists (fun (old, _old_run) -> old = value) seen))
          next
        in
        search (depth + 1) fresh (fresh @ seen)
  in
  search 0 initial initial

let one_unary_value_bfs max_depth =
  let instance = Main.reduce_mell [One] in
  let unary_actions = Stdlib.List.filter
    (fun action ->
      Big_int_Z.eq_big_int action.System.action_arity (nat_of_int 1))
    instance.Main.reach_system.System.system_actions in
  let rec search depth frontier seen =
    if Stdlib.List.exists ((=) instance.Main.reach_target) frontier then
      Some (depth, Stdlib.List.length seen)
    else if depth >= max_depth then None
    else
      let next = Stdlib.List.filter_map
        (fun pair ->
          let action, value = pair in
          System.apply_action instance.Main.reach_dimension action [value])
        (Stdlib.List.concat_map
          (fun value -> Stdlib.List.map (fun action -> (action, value)) unary_actions)
          frontier) in
      let fresh = Stdlib.List.filter
        (fun value -> not (Stdlib.List.exists ((=) value) seen)) next in
      search (depth + 1) fresh (fresh @ seen)
  in
  search 0 instance.Main.reach_system.System.initial_vectors
    instance.Main.reach_system.System.initial_vectors

let one_stateful_bfs max_rounds =
  let goal = ILZRuntime.translate_mell_runtime [One] in
  let machine = MELLToABVASSRuntime.compile_ilz_machine goal in
  let dimension =
    Big_int_Z.big_int_of_int
      (Stdlib.List.length (ILZRuntime.runtime_ilz_subformulas goal)) in
  let system = ZeroTestFree.direct_bottom_up dimension
    Main.ilz_machine_state_eq_dec machine in
  let root_state = ZeroTestFree.direct_root_state dimension
    Main.ilz_machine_state_eq_dec machine
    (MELLToABVASSRuntime.Coq_ilz_machine_sequent
      ([], snd goal)) in
  let root = (root_state, Vector0.nvec_zero dimension) in
  let apply rule children =
    match Vector0.add_displacement dimension rule.Stateful.rule_delta
      (Stdlib.List.map snd children) with
    | Some result -> Some (rule.Stateful.output_state, result)
    | None -> None
  in
  let instantiate known rule =
    match rule.Stateful.input_states with
    | [state] ->
        Stdlib.List.filter_map
          (fun ((child_state, _counters) as child) ->
            if child_state = state then apply rule [child] else None) known
    | [left_state; right_state] ->
        Stdlib.List.concat_map
          (fun ((left, _left_counters) as left_child) ->
            if left = left_state then
              Stdlib.List.filter_map
                (fun ((right, _right_counters) as right_child) ->
                  if right = right_state then apply rule [left_child; right_child]
                  else None) known
            else []) known
    | _ -> []
  in
  let rec rounds round known =
    if Stdlib.List.exists ((=) root) known then
      Some (round, Stdlib.List.length known)
    else if round >= max_rounds then None
    else
      let generated = Stdlib.List.concat_map (instantiate known)
        system.Stateful.stateful_rules in
      let fresh = Stdlib.List.filter
        (fun config -> not (Stdlib.List.exists ((=) config) known)) generated in
      rounds (round + 1) (fresh @ known)
  in
  rounds 0 system.Stateful.initial_configs

let tensor_saturation fuel =
  let gamma = [Tensor (One, One)] in
  let goal = ILZRuntime.translate_mell_runtime gamma in
  let machine = MELLToABVASSRuntime.compile_ilz_machine goal in
  let dimension = Big_int_Z.big_int_of_int
    (Stdlib.List.length (ILZRuntime.runtime_ilz_subformulas goal)) in
  let system = ZeroTestFree.direct_bottom_up dimension
    Main.ilz_machine_state_eq_dec machine in
  let state_count = ZeroTest.full_zero_state_count dimension machine in
  let root_state = ZeroTestFree.direct_root_state dimension
    Main.ilz_machine_state_eq_dec machine
    (MELLToABVASSRuntime.Coq_ilz_machine_sequent ([], snd goal)) in
  let counters = Vector0.nvec_zero dimension in
  let slice = FiniteSaturation.slice_system dimension state_count system
    (FiniteSaturation.needed_states dimension state_count system root_state
      (nat_of_int fuel)) in
  let answer = FiniteSaturation.saturation_decide dimension state_count slice
    root_state counters (nat_of_int fuel) in
  String.concat ","
    [string_of_int (Stdlib.List.length slice.Stateful.initial_configs);
     string_of_int (Stdlib.List.length slice.Stateful.stateful_rules);
     string_of_int (Stdlib.List.length
       (FiniteSaturation.saturation_configs dimension state_count slice
         (nat_of_int fuel)));
     string_of_option answer]

let full_saturation gamma fuel =
  let goal = ILZRuntime.translate_mell_runtime gamma in
  let machine = MELLToABVASSRuntime.compile_ilz_machine goal in
  let dimension = Big_int_Z.big_int_of_int
    (Stdlib.List.length (ILZRuntime.runtime_ilz_subformulas goal)) in
  let state_count = ZeroTest.full_zero_state_count dimension machine in
  let system = ZeroTestFree.direct_bottom_up dimension
    Main.ilz_machine_state_eq_dec machine in
  let root_state = ZeroTestFree.direct_root_state dimension
    Main.ilz_machine_state_eq_dec machine
    (MELLToABVASSRuntime.Coq_ilz_machine_sequent ([], snd goal)) in
  let configs = FiniteSaturation.saturation_configs dimension state_count system
    (nat_of_int fuel) in
  let answer = FiniteSaturation.saturation_decide dimension state_count system
    root_state (Vector0.nvec_zero dimension) (nat_of_int fuel) in
  string_of_int (Stdlib.List.length configs) ^ "," ^ string_of_option answer

let run = function
  | "path-mell-one" -> mell_decision_path [One]
  | "path-mell-identity" ->
      mell_decision_path [Atom (nat_of_int 0); CoAtom (nat_of_int 0)]
  | "path-mell-par-identity" ->
      mell_decision_path [Par (CoAtom (nat_of_int 4), Atom (nat_of_int 4))]
  | "path-mell-tensor-units" ->
      mell_decision_path [Tensor (One, One)]
  | "path-mell-bang-one" -> mell_decision_path [Bang One]
  | "path-mell-empty" -> mell_decision_path []
  | "path-mell-two-ones" -> mell_decision_path [One; One]
  | "path-mell-mismatched-atoms" ->
      mell_decision_path [Atom (nat_of_int 0); CoAtom (nat_of_int 1)]
  | "path-small-scan" -> small_path_scan ()
  | "fallback-bvas-initial" ->
      string_of_bool
        (BVAS.bvas_decide (nat_of_int 1) initial_zero_system (nvec1 0))
  | "fallback-bvas-empty" ->
      string_of_bool
        (BVAS.bvas_decide (nat_of_int 1) empty_system (nvec1 0))
  | "mell-one" -> string_of_bool (MELL.mell_decide [One])
  | "mell-identity" ->
      string_of_bool
        (MELL.mell_decide [Atom (nat_of_int 0); CoAtom (nat_of_int 0)])
  | "mell-tensor-units" ->
      string_of_bool (MELL.mell_decide [Tensor (One, One)])
  | "mell-par-identity" ->
      string_of_bool
        (MELL.mell_decide [Par (CoAtom (nat_of_int 4), Atom (nat_of_int 4))])
  | "mell-bang-one" ->
      string_of_bool (MELL.mell_decide [Bang One])
  | "mell-empty" -> string_of_bool (MELL.mell_decide [])
  | "mell-two-ones" -> string_of_bool (MELL.mell_decide [One; One])
  | "mell-mismatched-atoms" ->
      string_of_bool
        (MELL.mell_decide [Atom (nat_of_int 0); CoAtom (nat_of_int 1)])
  | "mell-one-stage0" ->
      string_of_option (MELL.mell_stage [One] (nat_of_int 0))
  | "mell-one-stage1" ->
      string_of_option (MELL.mell_stage [One] (nat_of_int 1))
  | "mell-one-fuel10" ->
      string_of_option (MELL.mell_search_fuel [One] (nat_of_int 10))
  | "mell-one-fuel100" ->
      string_of_option (MELL.mell_search_fuel [One] (nat_of_int 100))
  | "mell-empty-fuel10" ->
      string_of_option (MELL.mell_search_fuel [] (nat_of_int 10))
  | "mell-empty-fuel100" ->
      string_of_option (MELL.mell_search_fuel [] (nat_of_int 100))
  | "runtime-one-subformulas" ->
      let goal = ILZRuntime.translate_mell_runtime [One] in
      string_of_int (Stdlib.List.length (ILZRuntime.runtime_ilz_subformulas goal))
  | "runtime-one-supports" ->
      let goal = ILZRuntime.translate_mell_runtime [One] in
      string_of_int (Stdlib.List.length (MELLToABVASSRuntime.ilz_supports goal))
  | "runtime-one-rules" ->
      let goal = ILZRuntime.translate_mell_runtime [One] in
      let machine = MELLToABVASSRuntime.compile_ilz_machine goal in
      String.concat ","
        [string_of_int (Stdlib.List.length machine.FullZeroSystem.full_zero_unary_rules);
         string_of_int (Stdlib.List.length machine.FullZeroSystem.full_zero_split_rules);
         string_of_int (Stdlib.List.length machine.FullZeroSystem.full_zero_test_rules)]
  | "runtime-empty-rules" ->
      let goal = ILZRuntime.translate_mell_runtime [] in
      let machine = MELLToABVASSRuntime.compile_ilz_machine goal in
      String.concat ","
        [string_of_int (Stdlib.List.length (ILZRuntime.runtime_ilz_subformulas goal));
         string_of_int (Stdlib.List.length (MELLToABVASSRuntime.ilz_supports goal));
         string_of_int (Stdlib.List.length machine.FullZeroSystem.full_zero_unary_rules);
         string_of_int (Stdlib.List.length machine.FullZeroSystem.full_zero_split_rules);
         string_of_int (Stdlib.List.length machine.FullZeroSystem.full_zero_test_rules)]
  | "runtime-tensor-rules" -> runtime_machine_summary [Tensor (One, One)]
  | "runtime-par-rules" ->
      runtime_machine_summary [Par (CoAtom (nat_of_int 4), Atom (nat_of_int 4))]
  | "runtime-bang-rules" -> runtime_machine_summary [Bang One]
  | "runtime-two-ones-rules" -> runtime_machine_summary [One; One]
  | "reduce-one-dimension" ->
      Big_int_Z.string_of_big_int (Main.reduce_mell [One]).Main.reach_dimension
  | "reduce-one-summary" ->
      let instance = Main.reduce_mell [One] in
      String.concat ","
        [Big_int_Z.string_of_big_int instance.Main.reach_dimension;
         string_of_int (Stdlib.List.length instance.Main.reach_system.System.initial_vectors);
         string_of_int (Stdlib.List.length instance.Main.reach_system.System.system_actions);
         string_of_bool
           (Stdlib.List.exists
             (fun value -> value = instance.Main.reach_target)
             instance.Main.reach_system.System.initial_vectors)]
  | "reduce-empty-summary" ->
      let instance = Main.reduce_mell [] in
      String.concat ","
        [Big_int_Z.string_of_big_int instance.Main.reach_dimension;
         string_of_int (Stdlib.List.length instance.Main.reach_system.System.initial_vectors);
         string_of_int (Stdlib.List.length instance.Main.reach_system.System.system_actions);
         string_of_bool
           (Stdlib.List.exists
             (fun value -> value = instance.Main.reach_target)
             instance.Main.reach_system.System.initial_vectors)]
  | "mell-one-two-step-witness" ->
      begin match one_two_step_witness () with
      | Some (index, code) ->
          string_of_int index ^ "," ^ Big_int_Z.string_of_big_int code
      | None -> "None"
      end
  | "mell-one-unary-bfs" ->
      begin match one_unary_bfs 12 with
      | Some (depth, code) ->
          string_of_int depth ^ "," ^ Big_int_Z.string_of_big_int code
      | None -> "None"
      end
  | "mell-one-unary-value-bfs" ->
      begin match one_unary_value_bfs 24 with
      | Some (depth, count) -> string_of_int depth ^ "," ^ string_of_int count
      | None -> "None"
      end
  | "mell-one-stateful-bfs" ->
      begin match one_stateful_bfs 12 with
      | Some (round, count) -> string_of_int round ^ "," ^ string_of_int count
      | None -> "None"
      end
  | "tensor-saturation3" -> tensor_saturation 3
  | "tensor-saturation4" -> tensor_saturation 4
  | "tensor-saturation5" -> tensor_saturation 5
  | "tensor-saturation6" -> tensor_saturation 6
  | "tensor-saturation7" -> tensor_saturation 7
  | "tensor-saturation8" -> tensor_saturation 8
  | "tensor-saturation9" -> tensor_saturation 9
  | "tensor-saturation10" -> tensor_saturation 10
  | "two-ones-saturation6" -> full_saturation [One; One] 6
  | "two-ones-saturation8" -> full_saturation [One; One] 8
  | "two-ones-saturation10" -> full_saturation [One; One] 10
  | "two-ones-saturation12" -> full_saturation [One; One] 12
  | "code-invalid" ->
      string_of_bool (MELL.decide_code (nat_of_int 16))
  | "code-direct-agree" ->
      let gamma = [Tensor (One, One)] in
      string_of_bool
        (MELL.decide_code (Code0.encode_sequent gamma) = MELL.mell_decide gamma)
  | "codec-invalid-vector-length" ->
      string_of_bool
        (is_none
          (Code1.decode_nvec (nat_of_int 2)
            (Code.list_encode Code.nat_codec [nat_of_int 7])))
  | "codec-invalid-integer-tag" ->
      string_of_bool
        (is_none
          (Main.decode_integer
            (Code.pair_encode Code.nat_codec Code.nat_codec
              (nat_of_int 3, nat_of_int 7))))
  | "codec-invalid-positive-zero" ->
      string_of_bool
        (is_none
          (Main.decode_integer
            (Code.pair_encode Code.nat_codec Code.nat_codec
              (nat_of_int 1, nat_of_int 0))))
  | "codec-invalid-arity-zero" ->
      string_of_bool
        (is_none
          (Main.decode_action (nat_of_int 1)
            (Code.pair_encode Code.nat_codec
              (Main.zvector_codec (nat_of_int 1))
              (nat_of_int 0, zvec1 (nat_of_int 0)))))
  | "codec-invalid-reach-instance" ->
      let empty_zero =
        { System.initial_vectors = []; system_actions = [] } in
      let malformed =
        Cantor.to_nat
          (nat_of_int 0,
           Cantor.to_nat
             (Main.encode_ibvas (nat_of_int 0) empty_zero, nat_of_int 1)) in
      string_of_bool (is_none (Main.decode_reach_instance malformed))
  | "bigint-arithmetic" ->
      let huge = Big_int_Z.power_int_positive_int 2 80 in
      string_of_bool
        (BinInt.Z.add huge (Big_int_Z.minus_big_int huge) =
         Big_int_Z.zero_big_int)
  | "signed-action-negative" ->
      let magnitude = nat_of_int 1000 in
      let action =
        { System.action_arity = nat_of_int 1;
          action_offset = zvec1 (Big_int_Z.minus_big_int magnitude) } in
      let expected = Some (nvec1 0) in
      string_of_bool
        (System.apply_action (nat_of_int 1) action [nvec1_big magnitude] = expected)
  | "bvas-initial" ->
      string_of_bool
        (BVAS.bvas_decide (nat_of_int 1) initial_zero_system (nvec1 0))
  | "bvas-empty" ->
      string_of_bool
        (BVAS.bvas_decide (nat_of_int 1) empty_system (nvec1 0))
  | "bvas-unary-plus-two" ->
      string_of_bool
        (BVAS.bvas_decide (nat_of_int 1) unary_plus_two_system (nvec1 2))
  | "bvas-binary" ->
      string_of_bool
        (BVAS.bvas_decide (nat_of_int 1) binary_sum_system (nvec1 2))
  | "bvas-even-odd" ->
      string_of_bool
        (BVAS.bvas_decide (nat_of_int 1) even_system (nvec1 1))
  | "bvas-d0-empty" ->
      string_of_bool
        (BVAS.bvas_decide (nat_of_int 0)
          { System.initial_vectors = []; system_actions = [] }
          Vector.Coq_nil)
  | mode -> invalid_arg ("unknown regression mode: " ^ mode)

let () =
  if Array.length Sys.argv <> 2 then begin
    prerr_endline "usage: final_runner MODE";
    exit 2
  end;
  print_endline (run Sys.argv.(1))
