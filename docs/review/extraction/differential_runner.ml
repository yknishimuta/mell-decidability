open Syntax

let n = Big_int_Z.big_int_of_int
let big s = Big_int_Z.big_int_of_string s
let neg x = Big_int_Z.minus_big_int x
let b = string_of_bool
let option_bool = function Some x -> "Some " ^ b x | None -> "None"
let is_none = function None -> true | Some _ -> false

let nvec1 x = Vector.Coq_cons (x, n 0, Vector.Coq_nil)
let zvec1 x = Vector.Coq_cons (x, n 0, Vector.Coq_nil)

let plus_two =
  { System.action_arity = n 1; action_offset = zvec1 (n 2) }
let minus_one =
  { System.action_arity = n 1; action_offset = zvec1 (neg (n 1)) }
let binary_minus_one =
  { System.action_arity = n 2; action_offset = zvec1 (neg (n 1)) }

let even_system =
  { System.initial_vectors = [nvec1 (n 0)]; system_actions = [plus_two] }
let intermediate_system =
  { System.initial_vectors = [nvec1 (n 0)];
    system_actions = [minus_one; plus_two] }
let binary_system =
  { System.initial_vectors = [nvec1 (n 1)];
    system_actions = [binary_minus_one] }
let empty_system =
  { System.initial_vectors = []; system_actions = [] }

let leaf = FiniteTree.Coq_tree_leaf (n 0)
let unary_run =
  FiniteTree.Coq_tree_node
    (n 0, FiniteTree.Coq_forest_cons (leaf, FiniteTree.Coq_forest_nil))
let binary_run =
  FiniteTree.Coq_tree_node
    (n 0, FiniteTree.Coq_forest_cons
      (leaf, FiniteTree.Coq_forest_cons (leaf, FiniteTree.Coq_forest_nil)))
let bad_intermediate_run =
  FiniteTree.Coq_tree_node
    (n 1, FiniteTree.Coq_forest_cons
      (FiniteTree.Coq_tree_node
        (n 0, FiniteTree.Coq_forest_cons (leaf, FiniteTree.Coq_forest_nil)),
       FiniteTree.Coq_forest_nil))

let even_code = [(nvec1 (n 0), [nvec1 (n 2)])]
let zero_code = [(nvec1 (n 0), [])]
let odd_code = [(nvec1 (n 1), [nvec1 (n 2)])]
let nat_code = [(nvec1 (n 0), [nvec1 (n 1)])]

let encode_semi d value = (Code2.semi_codec d).Code.encode value
let encode_reach0 () =
  let system = { System.initial_vectors = [Vector.Coq_nil]; system_actions = [] } in
  Cantor.to_nat
    (n 0, Cantor.to_nat (Main.encode_ibvas (n 0) system,
                         Code1.encode_nvec (n 0) Vector.Coq_nil))

let sentence f = Syntax0.close_sentence f
let exists_true = sentence (Syntax0.Exists
  (Syntax0.Eq (Syntax0.Var (n 0), Syntax0.Num (neg (n 1)))))
let exists_false = sentence (Syntax0.Exists
  (Syntax0.ANd (Syntax0.Lt (Syntax0.Var (n 0), Syntax0.Num (n 0)),
                  Syntax0.Le (Syntax0.Num (n 0), Syntax0.Var (n 0)))))
let forall_true = sentence (Syntax0.Forall
  (Syntax0.Eq (Syntax0.Var (n 0), Syntax0.Var (n 0))))
let forall_false = sentence (Syntax0.Forall
  (Syntax0.Eq (Syntax0.Var (n 0), Syntax0.Num (n 0))))
let nested = sentence (Syntax0.Forall (Syntax0.Exists
  (Syntax0.Eq (Syntax0.Var (n 0),
               Syntax0.Plus (Syntax0.Var (n 1), Syntax0.Num (n 1))))))
let divisible = sentence (Syntax0.Exists
  (Syntax0.Eq (Syntax0.Scale (n 3, Syntax0.Var (n 0)),
               Syntax0.Num (neg (n 12)))))

let vector_result expected actual = b (actual = Some expected)

let run = function
  | "codec-sequent-roundtrip" ->
      b (Code0.decode_sequent (Code0.encode_sequent [One]) = Some [One])
  | "codec-sequent-duplicate" ->
      b (Code0.decode_sequent (Code0.encode_sequent [One; One]) = Some [One; One])
  | "codec-sequent-big" ->
      let huge = Big_int_Z.power_int_positive_int 2 80 in
      b (Code0.decode_sequent (Code0.encode_sequent [Atom huge]) = Some [Atom huge])
  | "codec-sequent-invalid" -> b (Code0.decode_sequent (n 16) = None)
  | "codec-reach-roundtrip" ->
      b (match Main.decode_reach_instance (encode_reach0 ()) with
         | Some r -> r.Main.reach_dimension = n 0 &&
             r.Main.reach_target = Vector.Coq_nil &&
             r.Main.reach_system.System.initial_vectors = [Vector.Coq_nil] &&
             r.Main.reach_system.System.system_actions = []
         | None -> false)
  | "codec-reach-invalid" ->
      let malformed = Cantor.to_nat
        (n 0, Cantor.to_nat (Main.encode_ibvas (n 1) empty_system, n 1)) in
      b (Main.decode_reach_instance malformed = None)
  | "codec-run-roundtrip" ->
      b (Code1.decode_run (Code.tree_encode binary_run) = Some binary_run)
  | "codec-semi-roundtrip" ->
      b (Code2.decode_semi (n 1) (encode_semi (n 1) even_code) = Some even_code)
  | "codec-semi-duplicate" ->
      let component = (nvec1 (n 0), [nvec1 (n 2)]) in
      let value = [component; component] in
      b (Code2.decode_semi (n 1) (encode_semi (n 1) value) = Some value)
  | "codec-semi-d0" ->
      let value = [(Vector.Coq_nil, [])] in
      b (Code2.decode_semi (n 0) (encode_semi (n 0) value) = Some value)
  | "codec-vector-invalid" ->
      b (Code1.decode_nvec (n 2) (Code.list_encode Code.nat_codec [n 7]) = None)
  | "run-leaf" -> vector_result (nvec1 (n 0))
      (Certificates.eval_run (n 1) even_system leaf)
  | "run-unary" -> vector_result (nvec1 (n 2))
      (Certificates.eval_run (n 1) even_system unary_run)
  | "run-binary-duplicate" -> vector_result (nvec1 (n 1))
      (Certificates.eval_run (n 1) binary_system binary_run)
  | "run-bad-action" -> b (is_none (Certificates.eval_run (n 1) even_system
      (FiniteTree.Coq_tree_node
        (n 7, FiniteTree.Coq_forest_cons (leaf, FiniteTree.Coq_forest_nil)))))
  | "run-bad-arity" -> b (is_none (Certificates.eval_run (n 1) even_system
      (FiniteTree.Coq_tree_node (n 0, FiniteTree.Coq_forest_nil))))
  | "run-bad-initial" -> b (is_none (Certificates.eval_run (n 1) even_system
      (FiniteTree.Coq_tree_leaf (n 3))))
  | "run-negative-intermediate" ->
      b (is_none (Certificates.eval_run (n 1) intermediate_system bad_intermediate_run))
  | "invariant-even-accept" -> b (Invariant.check_invariantP
      (n 1) even_system even_code (nvec1 (n 1)))
  | "invariant-closure-reject" -> b (Invariant.check_invariantP
      (n 1) even_system zero_code (nvec1 (n 1)))
  | "invariant-initial-reject" -> b (Invariant.check_invariantP
      (n 1) even_system odd_code (nvec1 (n 0)))
  | "invariant-target-reject" -> b (Invariant.check_invariantP
      (n 1) even_system nat_code (nvec1 (n 1)))
  | "presburger-exists-true" -> b (Decide.presburger_decide exists_true)
  | "presburger-exists-false" -> b (Decide.presburger_decide exists_false)
  | "presburger-forall-true" -> b (Decide.presburger_decide forall_true)
  | "presburger-forall-false" -> b (Decide.presburger_decide forall_false)
  | "presburger-nested" -> b (Decide.presburger_decide nested)
  | "presburger-divisible" -> b (Decide.presburger_decide divisible)
  | "fast-unit-yes" -> b (UnitFragment.unit_sequent_provableb [One])
  | "fast-unit-no" -> b (UnitFragment.unit_sequent_provableb [Atom (n 0)])
  | "fast-unit-exponential" -> b (UnitFragment.unit_sequent_provableb [Bang One])
  | "fast-weight-refutes" -> b (MultiplicativeWeight.multiplicative_weight_refutes [One; One])
  | "fast-weight-not-applicable" -> b (MultiplicativeWeight.multiplicative_weight_refutes [Bang One])
  | "fast-goal-yes" -> option_bool (MELL.mell_goal_saturation_decide
      [Atom (n 0); CoAtom (n 0)])
  | "fast-goal-none" -> option_bool (MELL.mell_goal_saturation_decide
      [Atom (n 0); CoAtom (n 1)])
  | "fast-full-yes" -> option_bool (MELL.mell_full_saturation_decide [One])
  | "fast-full-no" -> option_bool (MELL.mell_full_saturation_decide [])
  | "stage-bvas-yes" -> option_bool (Stage.bvas_stage
      (n 1) even_system (nvec1 (n 0)) (n 0))
  | "stage-bvas-mismatch" -> option_bool (Stage.bvas_stage
      (n 1) even_system (nvec1 (n 1)) (n 0))
  | "stage-bvas-no" ->
      let stage = Nat.add (Nat.mul (n 2) (encode_semi (n 1) even_code)) (n 1) in
      option_bool (Stage.bvas_stage (n 1) even_system (nvec1 (n 1)) stage)
  | "stage-mell-yes" -> option_bool (MELL.mell_stage [One] (n 0))
  | "stage-mell-no" -> option_bool (MELL.mell_stage [] (n 1))
  | "fuel-zero" -> option_bool (MELL.mell_search_fuel [One] (n 0))
  | "fuel-one-yes" -> option_bool (MELL.mell_search_fuel [One] (n 1))
  | "fuel-one-no" -> option_bool (MELL.mell_search_fuel [] (n 1))
  | "big-nat-add" ->
      let huge = Big_int_Z.power_int_positive_int 2 80 in
      Big_int_Z.string_of_big_int (Nat.add huge (n 1))
  | "codec-nat-big" ->
      let huge = Big_int_Z.power_int_positive_int 2 80 in
      b ((Code.nat_codec.Code.decode (Code.nat_codec.Code.encode huge)) = Some huge)
  | "big-nat-sub" ->
      let huge = Big_int_Z.power_int_positive_int 2 80 in
      Big_int_Z.string_of_big_int (Nat.sub (Nat.add huge (n 7)) huge)
  | "big-z-cancel" ->
      let huge = Big_int_Z.power_int_positive_int 2 80 in
      Big_int_Z.string_of_big_int (BinInt.Z.add huge (BinInt.Z.opp huge))
  | "z-div-negative" ->
      Big_int_Z.string_of_big_int (BinInt.Z.div (neg (n 7)) (n 3))
  | "z-mod-negative" ->
      Big_int_Z.string_of_big_int (BinInt.Z.modulo (neg (n 7)) (n 3))
  | "signed-action" -> b (System.apply_action (n 1) minus_one
      [nvec1 (n 1)] = Some (nvec1 (n 0)))
  | "decide-code-invalid" -> b (MELL.decide_code (n 16))
  | "public-mell-yes" -> b (MELL.mell_decide [One])
  | "public-mell-no" -> b (MELL.mell_decide [])
  | name -> invalid_arg ("unknown differential fixture: " ^ name)

let () =
  if Array.length Sys.argv <> 2 then begin
    prerr_endline "usage: differential_runner FIXTURE";
    exit 2
  end;
  print_endline (run Sys.argv.(1))
