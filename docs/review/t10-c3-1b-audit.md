# T10-C3-1B audit: center characterization

Date: 2026-10-20

Baseline: `9e19b9add46dfbac242719b2e7cb4c897d14b37e`

Scope: C3-1B only.  This unit formalizes Bizière--Leroux--Sutre (2026),
Lemma 4.8.  It does not begin C3-2.

## Definition and public theorem

`PositiveSpanningCombination set value` contains:

1. a finite list `generators` whose every occurrence belongs to `set`;
2. an equivalence `VecOf set point <-> QSpan generators point` for every
   rational vector `point`;
3. one rational coefficient for every occurrence of `generators`;
4. `Vector.Forall (fun coefficient => 0 < coefficient) coefficients`;
5. `QVecEq` between `zvec_to_qvec value` and the aligned rational linear
   combination.

Thus zero coefficients are rejected, duplicate generators are retained as
separate occurrences, and linear independence is not assumed.

With `Set Printing Implicit`, the final theorem is:

```coq
center_characterization
     : forall (d : nat) (set : ZSet d) (value : ZVec d),
       @Periodic d set ->
       @Center d set value <->
       @Difference d set value /\
       @PositiveSpanningCombination d set value
```

The two directions are separately exposed as:

```coq
center_implies_positive_spanning
     : forall (d : nat) (set : ZSet d) (value : ZVec d),
       @Periodic d set ->
       @Center d set value ->
       @PositiveSpanningCombination d set value

positive_spanning_implies_center
     : forall (d : nat) (set : ZSet d) (value : ZVec d),
       @Periodic d set ->
       @Difference d set value ->
       @PositiveSpanningCombination d set value ->
       @Center d set value
```

## Forward direction

`finite_p_spanning` supplies a finite list in `P`.  Its integer sum is `p`.
The Center hypothesis is applied to the genuine difference `0-p`; at tail
index one it provides

```text
p' = (radius + 1) * value - p in P.
```

The list `p' :: ps` spans the same rational space because `p'` already lies
in `VecOf P`.  Assigning the strictly positive coefficient
`1 / (radius + 1)` to every occurrence gives `value`.  Positivity follows
from the explicit successor denominator.

## Reverse direction

For an arbitrary offset `g in Difference P`, witnesses give `g+p in P`.
The required `value in Difference P` similarly gives `value+q in P`.
Spanning supplies rational coefficients for `-(p+q)`.

The positive coefficients and the offset coefficients are independently
cleared with `qvector_clear_denominators`.  If the resulting integer vectors
are `b` and `a`, the multiplier

```text
scale = 1 + sum_i |a_i|
```

makes every coefficient `scale*b_i+a_i` strictly positive.  This yields
positive naturals and a member

```text
radius*value - offset_scale*(p+q) in P,
```

where both `radius` and `offset_scale` are explicitly positive.  Adding
copies of `p` and `q` proves that `radius*value`, `radius*value-p`, and
`radius*value-q` all belong to `P`.

For every `n >= radius^2+radius`, write
`n = quotient*radius + remainder` with `remainder < radius`.  The lower bound
gives `quotient >= remainder+1`.  The proof combines:

```text
g+p
remainder * (value+q)
radius*value-p
remainder * (radius*value-q)
(quotient-remainder-1) * (radius*value)
```

to obtain `g+n*value in P`.  The same radius works for the whole Center tail.

## Regression boundary

Examples cover dimension zero, the zero monoid, `2N`, all of `Z`, the gap
monoid, and a low-rank generated periodic set.  The `P=Z, value=0` example
uses the dependent list `[1;-1]` with coefficients `[1;1]`.  A separate
duplicate-list example uses `[1;1]` with coefficients `[1/2;1/2]`, exercising
denominator clearing.  The empty list is tested in dimension zero, and a
candidate vector containing coefficient zero is proved not strictly
positive.

RED was observed before implementation: the audit module failed because
`Mell.Geometry.CenterCharacterization` did not exist.

## Trust boundary

The reverse implication is constructive and closed under the global
context.  The forward implication and the final equivalence inherit only
`Classical_Prop.classic` from `finite_p_spanning`, specifically from the
existing finite-basis proof behind `difference_group_finitely_generated`.
No ClassicalEpsilon, UIP/K, `Eq_rect_eq`, functional extensionality, new
axiom, or oracle is used.

## Verification record

The final implementation was checked with:

- `make CORE_LOG_DIR=/tmp/mell-c3-1b-logs audit-t10-c3-1b` (exit 0),
  including the focused build, public-type and assumption audit, forbidden
  dependency scan, and `coqchk -silent` for both changed Coq modules.
- `make CORE_LOG_DIR=/tmp/mell-c3-1b-regression check-t10-c3-0 check-t10-c3-1a`
  (exit 0), covering the two immediately preceding Center stages.
- `opam exec --switch . -- make -f Makefile.coq -j2` (exit 0), covering the
  complete generated Coq build.
- `git diff --check` on the authorized target files (exit 0).

An independent reviewer returned **Ready**, with no critical, important, or
minor findings.  The reviewer independently checked the definition, both
proof directions (including denominator clearing and the `radius^2+radius`
tail argument), boundary examples, public assumptions, and both modules with
`coqchk -silent`.
