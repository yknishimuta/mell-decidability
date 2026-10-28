# T10-D Task 3B audit: Leroux Lemma 5.7

## Scope and result

This task formalizes Leroux (2012), Lemma 5.7 only.  It adds the missing
direction of the bounded-coordinate characterization: every unbounded
coordinate admits an intraproduction that is positive in that coordinate,
and finitely many such witnesses can be summed into one witness.

The final theorem is `lemma_5_7_bounded_coordinates_intraproduction` in
`Mell.VAS.IntraproductionsLemma57`.  Production graphs and all Task 4
constructions remain out of scope.

## B0--B5 proof route

`unbounded_gamma_coordinate_witness` is the classical negation conversion
from the absence of a uniform natural bound to a configuration above any
given bound.

For `qgamma_unbounded_strict_comparable_pair`, the implementation uses the
finite-cover route (route A), not an encoded infinite sequence.  The exact
chain is:

1. `nvec_le_restricted_afs d (QGamma system gamma)` supplies restricted
   almost-fullness of componentwise order on `QGamma`.
2. `restricted_af_finite_cover_classic` supplies a finite list of subtype
   elements of `QGamma` that is downward-basis complete.
3. The maximum of the selected coordinate over this finite basis is formed.
4. Unboundedness supplies an upper configuration strictly above that maximum.
5. Its covering basis element is componentwise below it and strictly below
   it at the requested coordinate.

This route does not assume decidability of `QGamma`, VAS reachability, or an
executable witness selector.  It constructs no infinite sequence and invokes
neither countable choice nor dependent choice.

Task 3A's `lemma_5_6_intraproduction_dominates` converts the strict comparable
pair into an intraproduction positive at the selected coordinate.  A complete
finite enumeration `fin_index_list` of `Fin.t d`, Prop-level finite induction,
`intraproduction_zero`, and `intraproduction_add` combine the coordinatewise
witnesses.  The zero-dimensional case is the empty enumeration and therefore
uses the zero intraproduction.

Finally, Task 3A's
`bounded_coordinate_intraproduction_zero` supplies the forward implication;
the combined positivity property supplies the converse by classical case
analysis.  Thus the result is exactly

```text
exists h in H_gamma, forall i,
  BoundedGammaCoordinate system gamma i <-> h(i) = 0.
```

## Production-graph corollaries

`bounded_coordinate_add_intraproduction` proves that adding any
intraproduction preserves every bounded coordinate.

`lemma_5_7_unbounded_coordinate_growth` packages the Lemma 5.7 witness and
shows that, from any `q` in `QGamma`, natural multiples of that witness remain
in `QGamma` and exceed every requested bound at every unbounded coordinate.
This is the interface reserved for the later production-graph task.

## Regression coverage

`Mell.Audit.VASIntraproductionsLemma57Examples` checks:

- dimension zero;
- an empty action system with every coordinate bounded and witness zero;
- the one-dimensional `+1` system with its coordinate unbounded and witness
  one;
- the mixed two-dimensional vertical system, with the first coordinate
  bounded and the second unbounded;
- a two-axis system with both coordinates unbounded and intraproduction
  `(1,1)`;
- the strict comparable-pair theorem;
- the prior capacity-dip example, where `QGamma` contains a configuration
  below the capacity.

The imported Task 3A regression also retains zero-action, invalid-production,
and positive/negative-action cases.

## Axiom and selection audit

Separate `Print Assumptions` commands are recorded for:

- `qgamma_unbounded_strict_comparable_pair`;
- `unbounded_coordinate_positive_intraproduction`;
- `intraproduction_positive_on_all_unbounded`;
- `lemma_5_7_bounded_coordinates_intraproduction`.

All four depend only on `Classical_Prop.classic`.  In particular, the
finite-cover implementation in `Mell.Order.PeriodicOrder` uses classical
propositional case analysis/NNPP and does not depend on
`ClassicalEpsilon.constructive_indefinite_description`, countable choice, or
dependent choice.  No `QGamma` membership decider is introduced.

The focused audit target additionally rejects `Admitted`, `Axiom`, `Abort`,
`ClassicalEpsilon`, constructive indefinite description, UIP/K,
`Eq_rect_eq`, functional extensionality, and oracle markers in the new files.

## Remaining Task 4 obligations

Task 4 must still define the production graph and prove its graph-specific
reachability and Kirchhoff properties.  It may use the Lemma 5.7 witness to:

- preserve all bounded coordinates while shifting configurations by
  intraproductions;
- grow every unbounded coordinate beyond any finite threshold;
- keep all shifted configurations inside `QGamma` via Lemma 5.5.

No production graph, Kirchhoff relation, or capacity-transformer asymptotic
definability theorem is proved here.

## Verification at HEAD before commit

- Focused build and regression: `make audit-t10-d-task3b` passed.
- The focused audit replayed all public `Check` commands and the four separate
  `Print Assumptions` commands.
- `coqchk -silent` passed for `Mell.VAS.IntraproductionsLemma57` and
  `Mell.Audit.VASIntraproductionsLemma57Examples`.
- Full `_CoqProject` regression via `make -f Makefile.coq -j2` passed.
- Target-file `git diff --check` and forbidden-construction scans passed.
