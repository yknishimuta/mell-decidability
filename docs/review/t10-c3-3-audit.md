# T10-C3-3 audit: closed-linearization push-in

Date: 2026-10-21

Baseline: `157fb678c68254350fd1198e80c287c5cb5601c2`

Scope: T10-C3-3 only.  This unit formalizes Bizière--Leroux--Sutre
(2026), Lemma 4.7.  It does not begin C4.

## Public results

With `Set Printing Implicit`, the public types are:

```coq
center_anchor
     : forall (d : nat) (set : ZSet d),
       @Periodic d set ->
       exists anchor : ZVec d, set anchor /\ @Center d set anchor

closed_linearization_push_in_offset
     : forall (d : nat) (set : ZSet d),
       @Periodic d set ->
       exists anchor : ZVec d,
         set anchor /\
         (forall offset q : ZVec d,
          @Difference d set offset ->
          @ClosedLinearization d set q ->
          exists radius : nat,
            forall n : nat,
            set
              (@zvec_add d offset
                 (@zvec_nsmul d (radius + n) (@zvec_add d anchor q))))

closed_linearization_push_in
     : forall (d : nat) (set : ZSet d),
       @Periodic d set ->
       @ClosedLinearizationL2.NonnegativeSet d set ->
       exists anchor : ZVec d,
         set anchor /\
         (forall offset point : ZVec d,
          @Difference d set offset ->
          @ClosedLinearization d set (@zvec_sub d point anchor) ->
          exists radius : nat,
            forall n : nat,
            set (@zvec_add d offset (@zvec_nsmul d (radius + n) point)))
```

The named final theorem preserves the pre-existing T10-P contract.  Its
condition `ClosedLinearization set (point - anchor)` is the formal encoding
of `point` belonging to `anchor + ClosedLinearization set`.  The
`closed_linearization_push_in_offset` theorem records the equivalent form
used in the C3-3 instruction: `point = anchor + q`.  It is also stronger in
that it needs no nonnegativity premise.  The equality between the two forms
is `zvec_sub_add_cancel`.

## Anchor construction

`finite_p_spanning` supplies a finite list `generators` in `set` whose
rational span is `VecOf set`.  The anchor is `zvec_rsum generators`.
`periodic_rsum` proves that it belongs to `set`.  The constant coefficient
vector with every entry equal to one is strictly positive, and
`qgroup_combination_const` identifies its combination with the anchor.
Together with `periodic_member_in_difference`, the reverse implication of
`center_characterization` proves `Center set anchor`.

This construction handles an empty spanning list: the anchor is zero, the
coefficient vector is empty, and strict positivity is vacuous.  It also
handles dimension zero without a special assumption.

## Push-in connection

The anchor is fixed before `offset` and `q`.  For each pair,
`center_add_closed_linearization` proves `Center set (anchor + q)`.  Unfolding
`Center` at the requested `offset` supplies that pair's own radius and the
tail for every natural `n`.  No radius common to all pairs is asserted.

The final T10-P theorem instantiates `q` with `point - anchor` and rewrites
`anchor + (point - anchor)` to `point`.  `NonnegativeSet` is retained in the
public type for the original contract but is not needed by the stronger
offset-form proof.  No finite-generation or asymptotic-definability premise
is added.

## RED/GREEN and regression evidence

RED was run before `CenterPushIn.v` existed:

```text
Error: Cannot find a physical path bound to logical path
CenterPushIn with prefix Mell.Geometry.
```

GREEN and kernel audit:

```text
make CORE_LOG_DIR=/tmp/mell-c3-3-green check-t10-c3-3
  exit 0

make CORE_LOG_DIR=/tmp/mell-c3-3-audit audit-t10-c3-3
  exit 0
  coqchk -silent: exit 0

opam exec --switch . -- make -f Makefile.coq -j2
  exit 0
```

The focused examples cover dimension zero, the zero monoid, `2N`, the
nonnegative quadrant, all integers, the gap monoid, and a low-rank generated
periodic set.  They also cover `q = 0`, a negative difference offset, and one
fixed anchor used with two distinct `(offset,q)` pairs.

## Trust audit

`Print Assumptions` reports for each of `center_anchor`,
`closed_linearization_push_in_offset`, and `closed_linearization_push_in`:

```text
Axioms:
Classical_Prop.classic : forall P : Prop, P \/ ~ P
```

This is inherited through `finite_p_spanning` and its finite-basis path.
The C3-3 source introduces no axiom.  The source scan found no `Admitted`,
`Axiom`, `Abort`, UIP/K, `Eq_rect_eq`, functional extensionality,
`ClassicalEpsilon.constructive_indefinite_description`, or oracle.

## Independent review

An independent reviewer returned **READY** with zero Critical, Important,
or Minor findings.  The reviewer independently checked the baseline and
branch, rebuilt both proof sources, checked the exact T10-P quantifier order,
ran `Print Assumptions`, ran `coqchk -silent`, and repeated the forbidden-
construct and `git diff --check` scans.  The reviewer specifically confirmed
the empty-list/dimension-zero anchor, fixed-anchor ordering, per-pair radius,
negative-offset/distinct-`q` regression, and absence of C4 scope expansion.
