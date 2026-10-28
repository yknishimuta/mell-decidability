# T10-C2-L0 audit

Date: 2026-10-20

Baseline: `a88ba40c26f4d6ff5a2641a5baa9f310a8d1441f`

Revision note: the `FullPeriodic` definition recorded by the original L0
commit was subsequently corrected by C2-L0-R after direct comparison with
Biziere--Leroux--Sutre (2026), Section 2.3.  The current definition and the
correction audit are recorded in `t10-c2-l0-r-audit.md`; all other L0 results
in this document remain current.

Scope: C2-L0 only.  This change fixes the definitions of the difference
group, closed linearization, full periodicity, and asymptotic definability,
and proves finite generation of the difference group.  It does not prove
the closure-definability or closed-linearization results assigned to C2-L1
and C2-L2.

## Definitions and public statements

With `ZSet d := ZVec d -> Prop` and `QSet d := QVec d -> Prop`:

```coq
Difference : forall d : nat, ZSet d -> ZSet d

ClosedLinearization : forall d : nat, ZSet d -> ZSet d

closed_linearization_spec :
  forall (d : nat) (set : ZSet d) (value : ZVec d),
    ClosedLinearization set value <->
    Difference set value /\
    QClosure (Cone set) (zvec_to_qvec value)

FullPeriodic : forall d : nat, ZSet d -> Prop

AsymptoticallyDefinable : forall d : nat, ZSet d -> Prop

difference_is_integer_additive_group :
  forall (d : nat) (set : ZSet d),
    Periodic set -> IntegerAdditiveGroup (Difference set)

integer_additive_group_periodic_le_total :
  forall (d : nat) (set : ZSet d),
    IntegerAdditiveGroup set ->
    forall left right : ZVec d,
      set left -> set right -> PeriodicLe set left right

integer_additive_group_order_wqo :
  forall (d : nat) (set : ZSet d),
    IntegerAdditiveGroup set -> afs set (PeriodicLe set)

difference_group_finitely_generated :
  forall (d : nat) (set : ZSet d),
    Periodic set -> FinitelyGeneratedGroup (Difference set)
```

`Difference set value` has witnesses `left,right` in `set` with
`value = left - right`; it is not replaced by the ambient integer lattice.
`ClosedLinearization set value` is definitionally the intersection shown by
`closed_linearization_spec`.  The old L0 version of `FullPeriodic` required a
`FinitelyGeneratedGroup` and a finite-V `RationalPolyhedralCone`; C2-L0-R
renames that stronger notion `PolyhedralFullPeriodic` and restores the
paper's general `FullPeriodic`.  `AsymptoticallyDefinable set` is exactly
`QDefinable (Cone set)`.

## Proof connection to T10-B

For a periodic set `P`, subtraction identities prove that `Difference P`
contains zero and is closed under addition and additive inverse.  For any
`IntegerAdditiveGroup G`, the difference `right-left` of two carrier elements
is again in `G`; hence `PeriodicLe G` is total on its carrier.  `afs_full`
therefore supplies the WQO premise for
`periodic_order_wqo_iff_finitely_generated`.  Its finite natural-monoid
generators are converted to integer group generators.  Conversely, every
integer combination remains in the additive group, including negative
coefficients.

The only imported non-constructive dependency of the final theorem is the
`Classical_Prop.classic` already present in T10-B's
`periodic_order_wqo_iff_finitely_generated` direction.

## RED/GREEN and boundary regressions

RED was recorded before the production module existed: compiling
`ClosedLinearizationL0Examples.v` failed because
`Mell.Geometry.ClosedLinearization` was absent.

GREEN covers dimension zero, the zero monoid, `2N`, `N^2`, a mixed-sign
generated periodic set, and a low-rank two-dimensional set.  It also defines
the periodic set `P = {0} union {z | 2 <= z}` and proves that the integer point
`1` is not in `P` but is in `ClosedLinearization P`.  Thus the regression
explicitly prevents identifying `P` with its closed linearization.

## Verification

- `make check-t10-c2-l0`: success.
- `make audit-t10-c2-l0`: success.
- `coqchk -silent` on `Mell.Geometry.ClosedLinearization` and
  `Mell.Audit.ClosedLinearizationL0Examples`: success.
- Forbidden-source scan for `Admitted`, declared `Axiom`, and `Abort`:
  success (no matches).
- Assumption scan: `Classical_Prop.classic` only; no
  `ClassicalEpsilon.constructive_indefinite_description`, UIP/K,
  `Eqdep.Eq_rect_eq.eq_rect_eq`, or functional extensionality.

The focused command writes logs under `docs/review/logs/`; these pre-existing
untracked/log artifacts are not staged by the C2-L0 commit.

## Independent review

The first review identified a Critical contract mismatch: the initial
`FullPeriodic` draft accepted an arbitrary additive group and arbitrary cone.
It was corrected to reuse G1-I's `FinitelyGeneratedGroup` and
`RationalPolyhedralCone`.  The reviewer rechecked the corrected tree and
approved it with no remaining Critical, Important, or Minor findings.  The
review also independently confirmed the exact `P-P` definition, the closed
linearization equation, the T10-B WQO connection, both generation directions,
the boundary examples, and the assumptions/coqchk results.

C2-L0-R later established from the primary paper's explicit footnote that
this review used the older, stronger Definition 2.6 convention rather than
the paper's deliberate generalization.  The L0-R correction therefore
supersedes only that `FullPeriodic` ruling.
