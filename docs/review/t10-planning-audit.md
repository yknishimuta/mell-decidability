# T10-P background mathematics and MELL-reduction audit

Date: 2026-10-18

Baseline: `510b71ad03a7d2fb12db9cb5f45efa891b6dc77a`

Scope: planning and source audit only.  This document does not claim any T10
mathematical theorem has been implemented.

## 1. Normative inputs and notation

The controlling documents are the original design and implementation plan in
`/Users/nishimuta/Downloads/mell-codex-design`, together with the repository's
T09 contract and audit.  The six work groups are T10-A through T10-F below.
T10-G is a separate prerequisite task introduced by this audit to reduce the
finite-cover axiom footprint without changing either finite-cover statement.

Primary sources:

- Leroux, *Vector Addition Systems Reachability Problem (A Simpler
  Solution)*, 2012, DOI 10.29007/bnx2:
  <https://easychair.org/publications/paper/Blr/open>
- Bizière--Leroux--Sutre, *Bridging the Gap Between Plain VASS and
  Branching VASS*, FoSSaCS 2026, DOI 10.1007/978-3-032-22730-0_4:
  <https://link.springer.com/chapter/10.1007/978-3-032-22730-0_4>
- Bizière--Leroux--Sutre, *Solving the Reachability Problem for Branching
  Vector Addition Systems via Semilinear Inductive Invariants*, arXiv
  2607.09558v1: <https://arxiv.org/html/2607.09558v1>
- Lazić--Schmitz, *Nonelementary Complexities for Branching VASS, MELL,
  and Extensions*, 2015:
  <https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/LS-tocl15.pdf>

The plans introduce these common aliases.  They are part of the proposed API,
so downstream tasks must not silently change their domains.

```coq
Definition NSet (d : nat) := NVec d -> Prop.
Definition ZSet (d : nat) := ZVec d -> Prop.
Definition QSet (d : nat) := QVec d -> Prop.

Definition SameSet {A} (X Y : A -> Prop) : Prop :=
  forall x, X x <-> Y x.

Definition NonnegativeSet {d} (P : ZSet d) : Prop :=
  forall z, P z -> forall i, (0 <= Vector.nth z i)%Z.

Definition Semilinear {d} (X : NSet d) : Prop :=
  exists code : SemiCode d, forall x, X x <-> denote code x.
```

`AlmostSemilinear`, `QDefinable`, `VAS`, `VASReach`, and VASS sections are
new mathematical interfaces.  Their definitions are fixed in the individual
plans before any theorem that uses them.  In particular, a VASS section first
restricts the unprojected coordinates to zero and its control state to the
selected finite set, and only then projects.

## 2. Existing declarations verified at the baseline

The following types were obtained from Coq 8.20.1 with
`Set Printing Implicit`.  These names, rather than paraphrases of previous
tasks, are the reuse boundary for T10.

```coq
@denote : forall d : nat, SemiCode d -> NVec d -> Prop

decode_semi_encode :
  forall (d : nat) (code : SemiCode d),
    decode_semi d (@encode_semi d code) = Some code

compile_membership_correct :
  forall (d : nat) (code : SemiCode d)
         (env : Mell.Presburger.Semantics.environment),
    Mell.Presburger.Semantics.formula_semantics env
      (@compile_membership d code) <->
    exists value : NVec d,
      @denote d code value /\
      forall coordinate : nat, coordinate < d ->
        env coordinate = Z.of_nat (@vector_entry d value coordinate)

@Periodic : forall d : nat, (ZVec d -> Prop) -> Prop
@Cone : forall d : nat, (ZVec d -> Prop) -> QVec d -> Prop

periodic_cone_union_strict :
  forall (d : nat) (set : ZVec d -> Prop)
         (components : list (Component d)),
    @Periodic d set ->
    List.Forall (fun component => @Periodic d (snd component)) components ->
    @Decomposes d set components ->
    forall point : QVec d,
      @Cone d set point <-> @StrictConeUnion d components point

@IRunLe : forall d : nat, IRun d -> IRun d -> Prop

run_amalgamation :
  forall (d : nat) (S : IBVAS d) (root left right : IRun d),
    @ValidIRun d S root -> @ValidIRun d S left ->
    @ValidIRun d S right -> @IRunLe d root left ->
    @IRunLe d root right ->
    exists merged : IRun d,
      @ValidIRun d S merged /\ @IRunLe d left merged /\
      @IRunLe d right merged /\
      @nvec_add d (@irun_target d root) (@irun_target d merged) =
      @nvec_add d (@irun_target d left) (@irun_target d right)

stateful_run_reach_iff :
  forall (d q : nat) (S : SBVAS d q) (state : Fin.t q)
         (counters : NVec d),
    @SReach d q S state counters <->
    exists run : SRun d q,
      @ValidSRun d q S run /\
      @root_config d q run = (state, counters)

erase_states_correct :
  forall (d q : nat) (S : SBVAS d q) (state : Fin.t q)
         (counters : NVec d),
    @SReach d q S state counters <->
    @Reach (d + q + List.length (@stateful_rules d q S))
      (@erase_states d q S) (@encode_state_config d q S state counters)

@ContextOrder :
  forall d q : nat, SBVAS d q -> SRun d q -> SRun d q -> Prop

context_order_wqo :
  forall (d q : nat) (S : SBVAS d q),
    @KruskalAfProp.af.afs (SRun d q)
      (@ValidSRun d q S) (@ContextOrder d q S)

context_order_finite_cover :
  forall (d q : nat) (S : SBVAS d q),
    exists basis : list {run : SRun d q | @ValidSRun d q S run},
      forall run : {run : SRun d q | @ValidSRun d q S run},
        exists base : {run0 : SRun d q | @ValidSRun d q S run0},
          List.In base basis /\
          @ContextOrder d q S (proj1_sig base) (proj1_sig run)

irun_le_wqo :
  forall (d : nat) (S : IBVAS d),
    @KruskalAfProp.af.afs (IRun d) (@ValidIRun d S) (@IRunLe d)

irun_le_finite_cover :
  forall (d : nat) (S : IBVAS d),
    exists basis : list {run : IRun d | @ValidIRun d S run},
      forall run : {run : IRun d | @ValidIRun d S run},
        exists base : {run0 : IRun d | @ValidIRun d S run0},
          List.In base basis /\ @IRunLe d (proj1_sig base) (proj1_sig run)

@Provable : sequent -> Prop
@encode_sequent : sequent -> nat
decode_sequent_encode :
  forall Gamma : sequent,
    decode_sequent (encode_sequent Gamma) = Some Gamma
```

T10-E must reuse `ContextOrder` and its finite cover; it must not replace it
with `IRunLe` or the ordered-decoration sufficient relation.  T10-F must use
`erase_states_correct`; it must not recreate a naive state erasure.

## 3. Proposed public contracts

The types below are the completion contracts.  Names used only inside a
contract, such as `NPeriodic`, `AlmostSemilinear`, or `VASSSection`, must be
defined exactly as specified in the corresponding plan before the theorem is
stated.

### T10-A: arithmetic and set closure

```coq
semilinear_finite_union :
  forall d (sets : list (NSet d)),
    List.Forall Semilinear sets ->
    Semilinear (fun x => exists X, List.In X sets /\ X x)

semilinear_minkowski_sum :
  forall d (X Y : NSet d),
    Semilinear X -> Semilinear Y ->
    Semilinear (fun z => exists x y, X x /\ Y y /\ z = nvec_add x y)

semilinear_product :
  forall d e (X : NSet d) (Y : NSet e),
    Semilinear X -> Semilinear Y ->
    Semilinear (fun z =>
      X (Vector.shiftin_left d e z) /\ Y (Vector.shiftin_right d e z))

semilinear_projection :
  forall d e (f : Fin.t e -> Fin.t d) (X : NSet d),
    Semilinear X ->
    Semilinear (fun y => exists x, X x /\
      forall i, Vector.nth y i = Vector.nth x (f i))

semilinear_intersection :
  forall d (X Y : NSet d),
    Semilinear X -> Semilinear Y ->
    Semilinear (fun x => X x /\ Y x)

semilinear_complement :
  forall d (X : NSet d),
    Semilinear X -> Semilinear (fun x => ~ X x)

qdefinable_projection :
  forall d e (f : Fin.t e -> Fin.t d) (X : QSet d),
    QDefinable X ->
    QDefinable (fun y => exists x, X x /\
      forall i, y i == x (f i))

qdefinable_intersection :
  forall d (X Y : QSet d),
    QDefinable X -> QDefinable Y ->
    QDefinable (fun x => X x /\ Y x)
```

`Vector.shiftin_left/right` are interface names to be implemented as explicit
split projections and proved inverse to `Vector.append`; they are not assumed
library declarations.

### T10-B: signed periodic order (R11)

```coq
Definition PeriodicLe {d} (P : ZSet d) (x y : ZVec d) : Prop :=
  P (zvec_sub y x).

Definition FinitelyGeneratedPeriodic {d} (P : ZSet d) : Prop :=
  exists generators : list (ZVec d),
    (forall g, List.In g generators -> P g) /\
    forall x, P x <-> zvec_generated generators x.

periodic_order_wqo_iff_finitely_generated :
  forall d (P : ZSet d),
    Periodic P ->
    (KruskalAfProp.af.afs P (PeriodicLe P) <->
     FinitelyGeneratedPeriodic P)
```

The forward proof is Appendix A, Lemma 2.1.  Its R11-critical branch must
define `Q_s = f_s(P) ∩ N^d`, restrict the transported periodic order to
`Q_s`, take its product with Dickson only on `Q_s`, and prove that product
equivalent to `PeriodicLe Q_s`.  No coordinate order on an unrestricted
signed carrier is permitted.

### T10-C: cone, lattice, closed linearization, center, and faces

```coq
rational_closed_cone_finitely_generated :
  forall d (C : QSet d),
    QDefinable C -> IsCone C -> TopologicallyClosed C ->
    exists generators : list (QVec d),
      SameSet C (qcone_generated generators)

lattice_gordan :
  forall d (G : ZSet d) (C : QSet d),
    FinitelyGeneratedGroup G ->
    RationalPolyhedralCone C ->
    FinitelyGeneratedPeriodic
      (fun z => G z /\ C (zvec_to_qvec z))

closed_linearization_finitely_generated :
  forall d (P : ZSet d),
    Periodic P -> NonnegativeSet P -> AsymptoticallyDefinable P ->
    FinitelyGeneratedPeriodic (ClosedLinearization P)

closed_linearization_full :
  forall d (P : ZSet d),
    Periodic P -> FullPeriodic (ClosedLinearization P)

closed_linearization_push_in :
  forall d (P : ZSet d),
    Periodic P -> NonnegativeSet P ->
    exists p : ZVec d, P p /\
      forall g x, Difference P g ->
        ClosedLinearization P (zvec_sub x p) ->
        exists r : nat, forall n : nat,
          P (zvec_add g (zvec_nsmul (r + n) x))

center_characterization :
  forall d (P : ZSet d),
    Periodic P ->
    SameSet (Center P)
      (fun v => Difference P v /\ PositiveSpanningCombination P v)

center_absorbs_closed_linearization :
  forall d (P : ZSet d),
    Periodic P ->
    SameSet (Minkowski (Center P) (ClosedLinearization P)) (Center P)

rational_polyhedral_faces_finite :
  forall d (C : QSet d),
    RationalPolyhedralCone C ->
    exists faces : list (QSet d),
      forall F, IsFace C F <-> exists F', List.In F' faces /\ SameSet F F'
```

The `closed_linearization_push_in` membership `x ∈ p+Q` is encoded as
`ClosedLinearization P (x-p)`.  This is Lemma 4.7, not the false claim that
`x` itself belongs to `Q`.  Lemmas 4.8 and 4.9 are the final two center
contracts.  Faces always contain zero; an external library's empty face is
excluded by the adapter rather than identified with the minimal face.

### T10-D: Leroux VAS theorem

```coq
vas_reach_relation_inter_semilinear :
  forall d q (V : VAS d q)
         (R : SConfig d q -> SConfig d q -> Prop),
    StatefulRelationSemilinear R ->
    StatefulRelationAlmostSemilinear (fun source target =>
      R source target /\
      VASReach V (fst source) (snd source)
                 (fst target) (snd target))

vas_post_inter_semilinear :
  forall d q (V : VAS d q)
         (X Y : SConfig d q -> Prop),
    StatefulSemilinear X -> StatefulSemilinear Y ->
    StatefulAlmostSemilinear (fun target =>
      Y target /\ exists source,
        X source /\
        VASReach V (fst source) (snd source)
                   (fst target) (snd target))
```

The first is the finite-control lifting of the Section 6 theorem immediately
preceding Corollary 6.3; the second is exactly the finite-control forward half
needed later.  The source paper states the vector-only form, so the proof must
specialize per source/target state and reassemble the finitely many state
pairs; it may not silently erase states.  The proof
must close Sections 2--6: the Jančar run order (Lemma 4.1), transformer
composition and periodicity (Lemmas 5.1--5.2), intraproduction closure and
realisation (Lemmas 5.5--5.7), finite production graphs (Corollary 5.12),
Kirchhoff relations (Lemmas 5.14--5.15 and Corollary 5.16), minimal-run
decomposition (Lemma 6.1), intersection closure (Lemma 6.2), and projection.

### T10-E: FoSSaCS BVASS section theorem

```coq
Definition VASSSectionOf {d q} (B : SBVAS d q)
    (W : VASSSection d q) : Prop :=
  forall state counters,
    SReach B state counters <-> VASSSectionReach W state counters.

bvass_reach_is_vass_section :
  forall d q (B : SBVAS d q),
    exists W : VASSSection d q, VASSSectionOf B W

bvass_reach_inter_semilinear :
  forall d q (B : SBVAS d q) (R : SConfig d q -> Prop),
    StatefulSemilinear R ->
    StatefulAlmostSemilinear
      (fun config =>
        R config /\ SReach B (fst config) (snd config))
```

`VASSSectionReach` means: reach a selected VASS control state, require every
counter outside the retained first `d` coordinates to be zero, then project.
Theorem 12 is derived by:

1. `context_order_finite_cover` and the genuine `ContextOrder`;
2. Proposition 5 and Lemma 8's amalgamation/replacement equalities;
3. Lemma 9's `Extend(B,F)` run with the same target and branching depth at
   most `length basis - 1`;
4. Lemma 11's effective bounded-depth VASS construction and exact section
   equality.

Corollary 14 then uses T10-D on the VASS section, semilinear intersection
closure, restriction before projection, and preservation of almost
semilinearity by projection.  No computable finite run basis is claimed.

### T10-F: constructive many-one reduction from MELL to IBVAS reachability

```coq
Record ReachInstance : Type := {
  reach_dimension : nat;
  reach_system : IBVAS reach_dimension;
  reach_target : NVec reach_dimension
}.

Definition Holds (instance : ReachInstance) : Prop :=
  Reach (reach_system instance) (reach_target instance).

reduce_mell : sequent -> ReachInstance

reduce_mell_correct :
  forall Gamma : sequent,
    Provable Gamma <-> Holds (reduce_mell Gamma)

reduce_mell_code : nat -> option nat

reduce_mell_code_correct :
  forall Gamma,
    reduce_mell_code (encode_sequent Gamma) =
    Some (encode_reach_instance (reduce_mell Gamma))

reduce_mell_many_one :
  forall Gamma,
    Provable Gamma <->
    encoded_reachability (encode_reach_instance (reduce_mell Gamma))
```

`reduce_mell` is a transparent Gallina computation assembled from four
proved transformations, never a witness selected from an existential:

1. the Fact 8 Kolmogorov translation and its cut/subformula obligations;
2. Section 4.1.2's finite-subformula ILZ encoding, specialized to the
   multiplicative-exponential fragment so that no fork rule is generated;
3. Lemma 3's first, logspace many-one zero-test elimination, with dimension
   `|Q| * d`, at most `|Q|-1` tests per shortened branch, transition
   `(i,q) -> (i+1,q')`, no update of old blocks, and zero old blocks at every
   leaf;
4. orientation to bottom-up `SReach`, followed by `erase_states`.

The dimension-preserving oracle/Turing-reduction half of Lemma 3 is outside
the contract and must not appear in `reduce_mell`.

## 4. Finite-cover axiom investigation (T10-G)

### 4.1 Exact dependency

`theories/Order/FiniteBasis.v` imports `Classical_Prop`,
`ClassicalChoice`, and `ClassicalEpsilon`.  In
`almost_full_finite_cover`, failure of a finite cover is turned into an
escaping sequence.  The two calls to

```coq
ClassicalEpsilon.constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop),
    (exists x : A, P x) -> {x : A | P x}
```

select its first element and every successor; `dependent_choice` then builds
the sequence contradicted by almost-fullness.  Both
`context_order_finite_cover` and `irun_le_finite_cover` instantiate this
generic lemma.  At the baseline their `Print Assumptions` is exactly:

```text
ClassicalEpsilon.constructive_indefinite_description
Classical_Prop.classic
```

The WQO theorems, `stateful_run_reach_iff`, `erase_states_correct`, and
`ordered_embed_implies_context_insert` are closed under the global context.

### 4.2 Propagation and runtime impact

If T10-E consumes `context_order_finite_cover` unchanged, the two assumptions
propagate through `bvass_reach_is_vass_section`, Corollary 14, the proof of S,
and the closed T12 correctness/termination theorems.  This is a logical trust
dependency and must remain visible in every `Print Assumptions` ledger.

It does not by itself add a runtime oracle.  The basis and separator witnesses
are existential propositions and are not eliminated into `Set` by the
decider.  `bvas_decide_of_separator` converts only the proposition
`exists n, bvas_stage ... n <> None` into a natural-number search, using
`ConstructiveEpsilon.constructive_indefinite_ground_description_nat` on a
decidable predicate.  Standard extraction erases the separator proof and
runs that search over the executable stage.  The extraction audit must still
check the generated code; proof erasure is not a substitute for that check.

### 4.3 Axiom-reduction assessment

The generic theorem for an arbitrary type and arbitrary relation genuinely
needs a choice-like step in its current minimal-bad-sequence proof.  Merely
rewriting that proof cannot justify claiming a choice-free theorem.

The two concrete carriers are nevertheless finite-data/countable carriers:
valid `IRun` and `SRun` values have natural encodings, validity is decidable,
`IRunLe` is decidable, and the strong stateful decorated relation is
decidable and implies `ContextOrder`.  Therefore a specialized theorem can
choose the least encoded escaping run with the constructive natural-number
search theorem, then use the AF contradiction.  For the stateful theorem it
is sufficient to obtain a finite cover for the strong relation and weaken
each comparison with `ordered_embed_implies_context_insert`; no decision
procedure for existential `ContextOrder` is required.

This is a feasible independent implementation task, T10-G.  Its acceptance
condition is that both existing public finite-cover types are unchanged and
their `Print Assumptions` no longer contains
`ClassicalEpsilon.constructive_indefinite_description`.  Removing
`Classical_Prop.classic` is a secondary objective, not a licence to weaken
the result.  T10-G must finish before T10-E so the removed dependency does not
enter the section theorem.

## 5. Dependency graph and implementation order

```text
T09 ───────────────► G finite-cover axiom reduction ─────► E BVASS section
 │                         │                                │
 │                         └─ unchanged finite-cover types  │
 │                                                          ▼
 ├────────► B signed order ──► C cone/lattice/center ──► T11 separator
 │                                  ▲                  ▲
 ├────────► A closures/definability ┼────► D VAS ─────┘
 │                                  └──────── E ───────┘
 │
 T02 + T09 state erasure ───────────────► F MELL reduction ─► T12
```

Implementation order:

1. T10-A establishes the common set/definability interfaces.
2. T10-G removes the avoidable finite-cover choice dependency before any new
   theorem consumes the covers.
3. T10-B and T10-F may proceed independently after their shared interfaces
   are fixed.
4. T10-C follows A and B.
5. T10-D follows A and C's rational-definability interface.
6. T10-E follows A, D, G, and the complete T09 stateful/context development.

T10-F is independent of the S-background mathematics but must complete before
T12.  No T11 proof is part of T10.

## 6. Cross-task acceptance policy

Every task has a failing statement/import test (RED), a proof implementation
and focused regression suite (GREEN), a module-specific `coqchk`, exact
`Check` output, `Print Assumptions`, and a source-to-lemma review performed by
someone other than the implementer.  Acceptance additionally requires:

- no `Admitted`, `admit`, `Abort`, new mathematical `Axiom`, or disabled
  guard/positivity/universe check;
- no weakening of the public types in Section 3;
- no change to T01--T09 public theorem types unless a separately authorized
  blocker is reported;
- no extracted `AXIOM TO BE REALIZED`, `Obj.magic`, external oracle, or
  meaning-changing integer override in executable T10-F artifacts;
- explicit target-only staging; the untracked `vendor/presburger/` files are
  never staged or modified.

## 7. Open proof obligations, not blockers to planning

All T10 mathematical obligations remain open because T10-P deliberately
creates no Coq implementation.  The highest-risk obligations are:

1. the R11 order equivalence on `Q_s`, not merely a WQO upper bound;
2. rational-closure finite generation and lattice Gordan over the actual
   subgroup `P-P`;
3. Leroux's cycle realization and production-graph finiteness, which cannot
   be replaced by citing Corollary 6.3;
4. FoSSaCS Lemma 9's same-target bounded-depth transformation using the
   genuine context order;
5. the reverse direction of zero-test elimination, including the corrected
   destination state `q'` and leaf-zero recovery;
6. T10-G's complete codecs and decidability proofs for concrete runs.
