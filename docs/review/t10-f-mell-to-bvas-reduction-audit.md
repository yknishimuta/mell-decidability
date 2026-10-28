# T10-F Task 6F — MELL to BVAS many-one reduction audit

## Scope and checkpoints

- Branch: `work/mell-formalization`
- Task baseline: `bf03d1b2ce7441dcc854ec968786a3cdb55b941c`
- F1 checkpoint: `72a0713aa4c4c54a1fcc1118f99fbb7e14d2090b`
- F2 checkpoint: `f4a94a8beccde6888d8bdb5d998860acda6b0d44`
- F3 checkpoint: `4cb5db0ff4482a5e5f194316b77f8ff047bb0b9d`
- Scope stops after the executable reduction, its code-level many-one theorem,
  regression, and trust audit. Tasks 11 and 12 are not included.

The implementation follows Lazić–Schmitz, TOCL 2015, Fact 8, Section 4.1.2,
Claim 9.1, and the exact full-zero-test elimination underlying Lemma 3. It
does not add affine/contractive, lossy/expansive, additive, fork, or
coverability semantics.

## F1: ordinary MELL and ILZ

The executable translation and its exact bridge are:

```coq
Definition translate_mell (Gamma : sequent) : ILZGoal.

Theorem mell_ilz_iff : forall Gamma,
  Provable Gamma <-> ILZProvable (translate_mell Gamma).
```

The source is the existing cut-free, exchange-enabled one-sided MELL calculus.
The bridge uses Yalla's multiplicative-exponential fragment with cut, mix0,
and mix2 disabled.  Empty sequents, units, dual atoms, multiplicatives, and
exponentials are handled by the translation; no general weakening or
contraction is introduced.

## F2: finite ILZ machine and store frames

`compile_ilz_machine` enumerates the finite subformula set, finite exponential
supports, sequent/intermediate states, unary rules, split rules, and full-zero
promotion rules. Its machine type has no fork constructor, and
`ilz_machine_fork_free` records this fact.

The frame-sensitive store lemma is:

```coq
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
```

The proof generalizes the frame across induction. A non-`ioc` head remains a
linear occurrence; the induction hypothesis is instantiated with
`frame ++ [head]`, and `app_assoc` supplies only the required rebracketing. An
`ioc` head is moved into the finite support by the generated store rule. Thus
the proof does not use an invalid frame weakening principle and preserves
linear multiplicity. `Forall_app` is applied at explicit sites only; there is
no unbounded repeat proof search.

The resulting Claim 9.1 correspondence is:

```coq
Theorem ilz_machine_correct : forall Gamma,
  ILZProvable (translate_mell Gamma) <->
  ilz_machine_accepts (translate_mell Gamma).
```

## F3: exact full-zero-test elimination

`remove_zero_tests` is a transparent finite construction. For a finite state
support of size `n`, it uses `n` layers and `n*d` counters. Unary rules update
only the current layer, split rules split every block, and a full-zero rule
from `q` to `q'` becomes a bottom-up rule whose child is `(i+1,q')` and whose
parent is `(i,q)`. Lower layers are thereafter frozen.

The constructive run normalization removes repeated zero-labelled states on
each branch and yields the required test-count bound. The backward proof uses
`LayeredLowerZero`: every lower block at a layer state is zero. Since later
rules cannot alter a frozen lower block, all-zero leaves recover the exact
zero condition at each simulated test.

```coq
Theorem remove_zero_tests_correct : forall d State eq_dec
    (system : FullZeroBVASS d State) state counters,
  List.In state (full_zero_states system) ->
  FullZeroReach system state counters <->
  SReach (remove_zero_tests eq_dec system)
    (zero_test_root_state eq_dec system state)
    (zero_test_root_counters system counters).
```

The explicit support premise prevents the fallback index for an absent state
from being confused with a real state. The compiled ILZ root is proved to be
in that support by `translate_mell_root_in_states`.

`FullZeroReach` already presents proof-search deductions bottom-up: leaves are
the initial configurations, split children combine into their source, and the
compiled unary action is negated in `layered_unary_rule`. Consequently
`remove_zero_tests` directly produces the existing bottom-up `SBVAS`; no
separate unproved orientation adapter remains.

## F4: state erasure and executable many-one map

```coq
Record ReachInstance : Type := {
  reach_dimension : nat;
  reach_system : IBVAS reach_dimension;
  reach_target : NVec reach_dimension
}.

Definition Holds (instance : ReachInstance) : Prop :=
  Reach (reach_system instance) (reach_target instance).

Definition reduce_mell (Gamma : sequent) : ReachInstance.

Theorem reduce_mell_correct : forall Gamma : sequent,
  Provable Gamma <-> Holds (reduce_mell Gamma).
```

`reduce_mell` composes `translate_mell`, `compile_ilz_machine`,
`remove_zero_tests`, and the previously verified fresh-gate `erase_states`.
Its target is exactly `encode_state_config` of the layered root state and the
zero vector in the first layer. Every component is a transparent Gallina
function; no existential witness or choice operator is used to construct the
instance.

The concrete Gödel coding uses structural codecs for integers, fixed-length
vectors, positive-arity actions, finite IBVAS data, and the dependent
`ReachInstance` dimension:

```coq
Definition encode_reach_instance : ReachInstance -> nat.
Definition decode_reach_instance : nat -> option ReachInstance.

Lemma decode_reach_instance_encode : forall instance,
  decode_reach_instance (encode_reach_instance instance) = Some instance.

Definition reduce_mell_code : nat -> option nat.

Theorem reduce_mell_code_correct : forall Gamma,
  reduce_mell_code (encode_sequent Gamma) =
    Some (encode_reach_instance (reduce_mell Gamma)).

Theorem reduce_mell_many_one : forall Gamma,
  Provable Gamma <->
  encoded_reachability
    (encode_reach_instance (reduce_mell Gamma)).
```

Malformed sequent codes map to `None`. `encoded_reachability` decodes one
concrete reachability instance and applies `Holds`; the round trip prevents
encoding collisions from changing the theorem. Integer tags outside `0`, `1`,
and `2`, noncanonical zero tags, positive/negative tags with magnitude zero,
zero-arity actions, wrong vector lengths, and malformed nested instance
payloads are rejected with `None`; none is normalized or truncated.

## Regression and trust audit

The dedicated regression covers `One`, atomic identity, tensor/par,
promotion, exponential weakening and contraction, the unprovable empty and
two-unit sequents, sequent-to-instance code transport, instance codec round
trip, malformed integer tags and magnitudes, zero-arity actions, malformed
dependent instance payloads, and encoded reachability. A dimension-zero
two-state example exercises a genuine state-changing full-zero test and its
preservation by `remove_zero_tests`. The audit also checks the exact
`layered_test_rule_shape`, frozen-lower-block invariant, backward recovery,
store-frame theorem, and fork-free theorem. Earlier checkpoint regressions
cover all ILZ rule families, store ordering and duplicates, support
idempotence, zero-test-free/one/multiple-test runs, split distribution, and
fresh-gate state erasure.

Targeted commands completed with exit code 0:

- `make check-t10-f`;
- `make audit-t10-f` (public `Check`, `Print Assumptions`, prohibited scan,
  and targeted `coqchk -silent`);
- `make audit-logic audit-bvas-core audit-codecs audit-bridges`.

The local structural theorems `mell_ilz_iff`, `ilz_machine_correct`,
`remove_zero_tests_correct`, `ilz_plain_machine_correct`, and
`reduce_mell_correct` are closed under the global context. The concrete
dependent action/instance codec round trip, and therefore the two code-level
theorems, report only `Classical_Prop.classic`; this is the existing proof
irrelevance route already used by `Mell.BVAS.Code`, not a new axiom or a choice
operator. No `ClassicalEpsilon`, `ClassicalChoice`, UIP/K axiom,
`Eq_rect_eq`, functional extensionality, `Admitted`, `admit`, `Abort`, or new
mathematical `Axiom` occurs in the Task 6F sources.

## Independent review

A fresh read-only reviewer first found two Important issues: permissive
integer decoding and insufficient explicit regression coverage. The decoder
was made canonical and rejecting, and the regression suite was expanded as
described above. On re-review it returned **PASS**, with no remaining Critical,
Important, or Minor finding. It specifically rechecked store-frame recursion,
the ILZ equivalence directions, state-changing `q -> q'` zero tests, negated
unary orientation, frozen lower blocks, all-zero leaves, root support, state
erasure, strict dependent decoding, and the final theorem composition.

Final verification completed with exit code 0 for the forced full
`_CoqProject` rebuild (`make -f Makefile.coq clean` followed by
`make -f Makefile.coq -j2`) and for `make -f Makefile.coq validate`.  The
latter ran `coqchk -silent` over the complete `_CoqProject` dependency
closure.  The global context summary includes axioms from unrelated imported
libraries; the theorem-local `Print Assumptions` results above are the trust
boundary for Task 6F.  The Task 6F target diff and staged diff were checked
separately so that pre-existing generated audit logs with trailing whitespace
were not modified or staged.

## Remaining obligations

No Task 6F proof obligation is intentionally deferred. Tasks 11 and 12 are
outside this scope.
