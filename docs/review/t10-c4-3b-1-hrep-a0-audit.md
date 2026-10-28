# T10-C4-3B-1-HRep-A0 audit

## Scope and baseline

- Baseline: `8a49518a5bf27c6c9f100dd85b45c03aa312ac54`.
- Scope: scalar conversion between Coq `Z`/`Q` and MathComp `int`/`rat` only.
- HRep-A1, vector and matrix adapters, cone semantics, and H-representations are not implemented here.
- Pre-existing audit logs, `theories/Audit/FaceStrippingBasesExamples.v`, and `vendor/presburger/` were not modified or staged.

## Definitions

`z_to_int` and `int_to_z` are structural conversions.  Negative MathComp
integers use `Negz n`, whose value is `-(n+1)`; the definitions preserve that
offset explicitly.

`q_to_rat` uses `fracq` on the converted `Qnum` and the strictly positive
`Qden`.  `rat_to_q` uses `numq` and `denq`; `denq_gt0` proves that the fallback
negative branch of `positive_of_positive_int` is unreachable for a `rat`.

## Public types

With `Set Printing Implicit`:

```coq
z_to_int
     : Z -> int
int_to_z
     : int -> Z
int_to_z_to_int
     : forall value : Z, int_to_z (z_to_int value) = value
z_to_int_to_z
     : forall value : int, z_to_int (int_to_z value) = value
z_to_int_opp
     : forall value : Z, z_to_int (- value) = (- z_to_int value)%R
q_to_rat
     : Q -> rat
rat_to_q
     : rat -> Q
q_to_rat_eq_iff
     : forall left right : Q,
       q_to_rat left = q_to_rat right <-> (left == right)%Q
rat_to_q_to_rat
     : forall value : rat, q_to_rat (rat_to_q value) = value
q_to_rat_to_q
     : forall value : Q, (rat_to_q (q_to_rat value) == value)%Q
```

Here `(left == right)%Q` is Coq's `Qeq`, not MathComp boolean equality.

## Proof connections

- Integer round trips use `positive_nat_Z`, `SuccNat2Pos`, and the exact
  `Posz`/`Negz` representation.
- `q_to_rat_eq_iff` uses `fracq_eq` and cross multiplication.  Positive
  denominators are discharged by `positive_to_int_nonzero`.
- `rat_to_q_to_rat` uses `denq_gt0` to obtain the positive denominator shape,
  then `valqK` to recover the original normalized MathComp rational.
- `q_to_rat_to_q` follows from the preceding two results and the proved
  equivalence between `rat` equality and `Qeq`.

## RED/GREEN and regression

RED exposed two representation-boundary errors before the final proof:

1. an invalid tactic-level `change ... in` parse under the combined Coq and
   MathComp notation environment;
2. accidental parsing of `left == right` as MathComp boolean equality rather
   than Coq `Qeq`.

The implementation now uses an explicit unfold and explicit `Qeq`.

GREEN commands:

```text
_opam/bin/coqc -Q theories Mell -Q vendor/minicooper MiniCooper \
  theories/Geometry/QratAdapter.v
_opam/bin/coqc -Q theories Mell -Q vendor/minicooper MiniCooper \
  theories/Audit/QratAdapterExamples.v
make OPAMEXEC= check-t10-c4-3b-1-hrep-a0
make -f Makefile.coq -j2
```

All exited 0.  The focused examples cover canonical zero, one, minus one,
large signed integers, `1/2`, `2/4`, `-3/6`, `0/2` and `0/7` passed through
the adapter, a pair that is `Qeq` but not Leibniz-equal, and the general `rat`
round trip.

## Kernel and assumptions

```text
coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper \
  Mell.Geometry.QratAdapter Mell.Audit.QratAdapterExamples
```

exited 0.

```text
Print Assumptions q_to_rat_eq_iff.
Closed under the global context

Print Assumptions rat_to_q_to_rat.
Closed under the global context

Print Assumptions q_to_rat_to_q.
Closed under the global context
```

The target files contain no `Admitted`, `Axiom`, `Abort`, UIP/K,
`Eq_rect_eq`, functional extensionality,
`ClassicalEpsilon.constructive_indefinite_description`, or external oracle.
The automated audit requires exactly three `Closed under the global context`
lines and rejects any `Axioms:` report.

## Independent review

An independent read-only review found the conversion definitions and proofs
sound and within A0 scope.  It requested two pre-commit corrections: exercise
`0/2` through the adapter, and make the automated assumptions gate verify all
three public theorems.  Both corrections are included in the focused
regression and audit target above.

## Boundary for HRep-A1

No arithmetic homomorphism or order-isomorphism API beyond negation and the
internal multiplication lemmas needed for the round trips is claimed.  In
particular, addition, multiplication, division, and order preservation for
the public `Q`/`rat` adapter remain HRep-A1 obligations.
