# T10-C4-3B-1-HRep-A1 audit

## Scope and baseline

- Baseline: `97e3e4a9c943d3eeac6f528689aedbd648d8f9ce`.
- Scope: arithmetic and order preservation for the existing `Z`/`int` and
  `Q`/`rat` scalar adapters.
- The A0 definitions `z_to_int`, `int_to_z`, `q_to_rat`, and `rat_to_q`, and
  the A0 public theorem statements, are unchanged.
- HRep-A2 vector/matrix adapters and all cone and H-representation work are
  deliberately excluded.

## Public arithmetic types

The integer API is:

```coq
z_to_int_zero : z_to_int Z.zero = (0 : int)
z_to_int_one : z_to_int Z.one = (1 : int)
z_to_int_add : forall left right : Z,
  z_to_int (Z.add left right) = (z_to_int left + z_to_int right)%R
z_to_int_sub : forall left right : Z,
  z_to_int (Z.sub left right) = (z_to_int left - z_to_int right)%R
z_to_int_mul : forall left right : Z,
  z_to_int (Z.mul left right) = (z_to_int left * z_to_int right)%R
z_to_int_le_iff : forall left right : Z,
  Z.le left right <-> is_true ((z_to_int left <= z_to_int right)%R)
z_to_int_lt_iff : forall left right : Z,
  Z.lt left right <-> is_true ((z_to_int left < z_to_int right)%R)
z_to_int_nonnegative_iff : forall value : Z,
  Z.le Z.zero value <-> is_true (((0 : int) <= z_to_int value)%R)
z_to_int_positive_iff : forall value : Z,
  Z.lt Z.zero value <-> is_true (((0 : int) < z_to_int value)%R)
```

The rational arithmetic API is:

```coq
q_to_rat_zero : q_to_rat 0 = (0 : rat)
q_to_rat_one : q_to_rat 1 = (1 : rat)
q_to_rat_add : forall left right : Q,
  q_to_rat (Qplus left right) =
    (q_to_rat left + q_to_rat right)%R
q_to_rat_opp : forall value : Q,
  q_to_rat (Qopp value) = (- q_to_rat value)%R
q_to_rat_sub : forall left right : Q,
  q_to_rat (Qminus left right) =
    (q_to_rat left - q_to_rat right)%R
q_to_rat_mul : forall left right : Q,
  q_to_rat (Qmult left right) =
    (q_to_rat left * q_to_rat right)%R
q_to_rat_inv : forall value : Q,
  q_to_rat (Qinv value) = (q_to_rat value)^-1%R
q_to_rat_div : forall left right : Q,
  q_to_rat (Qdiv left right) =
    (q_to_rat left / q_to_rat right)%R
q_to_rat_inject_Z : forall value : Z,
  q_to_rat (inject_Z value) = ((z_to_int value)%:~R : rat)
```

## Public order types

```coq
q_to_rat_le_iff : forall left right : Q,
  Qle left right <->
    is_true ((q_to_rat left <= q_to_rat right)%R)
q_to_rat_lt_iff : forall left right : Q,
  Qlt left right <->
    is_true ((q_to_rat left < q_to_rat right)%R)
q_to_rat_nonnegative_iff : forall value : Q,
  Qle 0 value <-> is_true (((0 : rat) <= q_to_rat value)%R)
q_to_rat_positive_iff : forall value : Q,
  Qlt 0 value <-> is_true (((0 : rat) < q_to_rat value)%R)
q_to_rat_nonpositive_iff : forall value : Q,
  Qle value 0 <-> is_true ((q_to_rat value <= (0 : rat))%R)
q_to_rat_negative_iff : forall value : Q,
  Qlt value 0 <-> is_true ((q_to_rat value < (0 : rat))%R)
q_to_rat_inject_Z_le_iff : forall left right : Z,
  Z.le left right <->
    is_true ((q_to_rat (inject_Z left) <= q_to_rat (inject_Z right))%R)
q_to_rat_inject_Z_lt_iff : forall left right : Z,
  Z.lt left right <->
    is_true ((q_to_rat (inject_Z left) < q_to_rat (inject_Z right))%R)
q_to_rat_mul_positive_le_iff : forall left right factor : Q,
  Qlt 0 factor ->
  (Qle left right <->
    is_true (((q_to_rat left * q_to_rat factor) <=
      (q_to_rat right * q_to_rat factor))%R))
q_to_rat_mul_positive_lt_iff : forall left right factor : Q,
  Qlt 0 factor ->
  (Qlt left right <->
    is_true (((q_to_rat left * q_to_rat factor) <
      (q_to_rat right * q_to_rat factor))%R))
rat_to_q_nonnegative : forall value : rat,
  is_true (((0 : rat) <= value)%R) -> Qle 0 (rat_to_q value)
rat_to_q_positive : forall value : rat,
  is_true (((0 : rat) < value)%R) -> Qlt 0 (rat_to_q value)
```

MathComp prints propositions coerced from booleans without the explicit
`is_true`; the source types above show the Prop/boolean boundary exactly.

## Proof connections and inverse zero

- Integer addition is proved structurally over the four `Posz`/`Negz`
  sign combinations; subtraction reuses addition and A0 negation, while
  multiplication reuses the existing A0 multiplication theorem.
- Integer order uses `leP`/`ltP`, `Nat2Z.inj_*`, and the two established
  round trips.
- Rational addition, negation, and multiplication reuse `addq_frac`,
  `oppq_frac`, `mulq_frac`, `addq_subdefE`, and `mulq_subdefE`.
- `Qinv 0` and MathComp `0^-1` both equal zero.  The zero-numerator branch
  uses `invr0`; nonzero branches use A0 `q_to_rat_eq_iff`, `Qmult_inv_r`,
  `mulfI`, and `mulrV`.  Thus `q_to_rat_inv` is total and has no added
  nonzero premise.
- Order reflection unfolds `fracqE`, uses positivity of converted `Qden`,
  and applies `ler_pdivl_mulr`/`ler_pdivr_mulr` or their strict variants.
  After cross multiplication, `ler_int`/`ltr_int`, integer multiplication,
  and the integer order equivalences close the proof.
- Positive-factor order preservation uses `ler_pmul2r`.
- The reverse sign corollaries reuse `rat_to_q_to_rat` and the new order
  equivalences; no second normalization proof is introduced.

## RED/GREEN and regression

RED first failed on missing `z_to_int_zero`, then on missing
`q_to_rat_zero`, confirming that the focused file exercised the new API.
GREEN was reached incrementally for integer arithmetic/order, rational
arithmetic, inverse/division, and rational order.

`QratArithmeticExamples.v` covers zero, one, minus one, large signed integer
addition/multiplication/order, `1/2`, `2/4`, `-3/6`, noncanonical zero,
positive/negative/zero arithmetic, division by a nonzero rational,
`Qinv 0`, a negative inverse, distinct-denominator comparisons,
`1/2 < 3/4`, `-3/2 < -1`, positive-factor order preservation, and order
after `rat_to_q`.  Both directions of `1/2 <= 2/4` are proved, so an equal
but non-Leibniz-equal standard `Q` pair is exercised through order.

Commands that exited zero:

```text
make OPAMEXEC= check-t10-c4-3b-1-hrep-a1
make OPAMEXEC= audit-t10-c4-3b-1-hrep-a1
make -f Makefile.coq -j2
```

## Kernel and assumptions

The focused audit ran:

```text
coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper \
  Mell.Geometry.QratAdapter Mell.Audit.QratArithmeticExamples
```

It exited zero.  `Print Assumptions` was run for 30 integer/rational
arithmetic and order results; all 30 printed `Closed under the global
context`, with no `Axioms:` report.  The source gate found no `Admitted`,
`Abort`, new `Axiom`, `Classical_Prop.classic`, `ClassicalEpsilon`, UIP/K,
`Eq_rect_eq`, functional extensionality, constructive indefinite
description, or external oracle.

## Independent review

An independent read-only Coq/MathComp review reported no Critical,
Important, or Minor findings.  It confirmed preservation of the A0
definitions and theorem types, completeness of the requested arithmetic and
order API (including inverse zero), the nonnormalized and signed regressions,
the 30 closed assumption checks, and the A1 scope boundary.  Its assessment
was ready to commit; it separately identified the pre-existing logs,
`FaceStrippingBasesExamples.v`, and `vendor/presburger/` as excluded state.

## Boundary for HRep-A2

HRep-A2 still owns vector and row/column conversions and their componentwise
equality/order facts.  No vector adapter, cone semantics, generated-cone
meaning, H-representation, homogenization, or integer H-representation is
implemented by A1.
