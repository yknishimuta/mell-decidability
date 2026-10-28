# T09 stateful BVASS / context-order audit

Date: 2026-10-18

Normative inputs:

- `docs/superpowers/specs/2026-10-18-t09-stateful-bvass-contract-amendment.md`
- Bizière--Leroux--Sutre, *Bridging the Gap Between Plain VASS and
  Branching VASS*, Definition 4, Section 3.2, and Proposition 5
- design audit items R03 and R05

## Corrected R05 definition

The rejected partial implementation exposed `ContextOrder` through a fixed
child-position `OrderedDecorEmbed`.  That relation is strictly stronger than
the paper's order: for example, the valid binary runs with children `[q;r]`
and `[r;q]` are context-isomorphic, but the positional decorations do not
embed.  It also fails to express independently chosen contexts at every
original node.

The corrected `ContextOrder` is witnessed by:

1. one `SContext` for every node of the source run (`SContextFamily`);
2. equality of the hole and context-root states (`CompatibleContextFamily`);
3. nonnegative total family effect at every original subtree
   (`HereditarilyPositive`);
4. unordered tree isomorphism between the inserted run and the target.

`SRunIsomorphic` removes one target child occurrence at a time.  It therefore
preserves child-state multiplicities, handles duplicate states as distinct
occurrences, and is independent of list order.  It does not identify rules,
stored configurations, or the number of child occurrences.

The signed effect of a context is its root counter minus its hole counter.
`context_family_effect` sums these effects structurally over the original
subtree.  `context_family_effect_exact` proves, from the two valid-run
equations, that this sum is exactly the inserted-root counter minus the
source-root counter.  Consequently hereditary positivity means the paper's
subtree effect sum is componentwise nonnegative; it does not require every
prefix on a context path to be nonnegative.

Reflexivity uses the hole-only identity family.  Transitivity transports the
second family across unordered run isomorphism and composes the two families
node by node.  The insertion, compatibility, hereditary-positivity, and final
isomorphism obligations are proved separately.

## R03 remains separate

`IRunLe` is the Appendix B.1/R03 order on stateless `IBVAS` runs.  It was not
redefined as `ContextOrder`, and no T06 amalgamation theorem was transferred
to the stateful system.  The stateful WQO uses the strong decorated relation
only as a sufficient relation and applies
`ordered_embed_implies_context_insert` in one direction.

## Regression witnesses

`theories/Audit/BridgeExamples.v` checks:

- `[q;r]` versus `[r;q]` in both `ContextOrder` directions;
- separate occurrence matching for two children with the same state;
- rejection of unequal root states;
- rejection when the root effect is nonnegative but a proper-subtree family
  effect is negative;
- the R05 gap where positional decoration rejects a child permutation that
  unordered context isomorphism accepts.

## Equality and axiom audit

Dependent equality in state erasure and the WQO bridge is discharged using
structural vector/finite-index elimination.  The public erasure, context
order, WQO, and finite-cover theorems do not depend on
`Eqdep.Eq_rect_eq.eq_rect_eq` or on a UIP/K axiom.  The two finite-cover
theorems retain only the classical assumptions inherited from the generic
almost-full-relation finite-cover library.

Verification output is recorded in:

- `docs/review/logs/check-bridges.log`
- `docs/review/logs/audit-bridges.log`
- `docs/review/logs/coqchk-bridges.log`
