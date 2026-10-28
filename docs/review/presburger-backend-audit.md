# T07a Presburger backend audit

Date: 2026-10-17

## Decision

Use the Gallina core from `Armael/minicooper` at commit
`3f051307039456a88cf093921278b0dcf224f7cf` as the T07 quantifier
elimination backend.  Adoption is limited to `MyTactics.v`, `LinSimpl.v`,
`Constant.v`, and `Theory.v`; the Template-Coq tactic frontend is not part of
the trusted or executable core.

This decision supersedes the initial design candidate
`rocq-archive/presburger`. The selected backend is pinned in both
`docs/review/sources.json` and `docs/review/toolchain-lock.json`; it is not a
floating Git dependency.

The backend correctness theorem used by the adapter has the complete type:

```coq
MiniCooper.Theory.interpret_qe :
  forall (cenv : nat -> Z) (f : MiniCooper.Theory.formula)
    (env : nat -> Z),
    MiniCooper.Theory.all_under_ex
      (fun p t => MiniCooper.Theory.wft 0 t /\
        MiniCooper.Theory.wfp p) f ->
    MiniCooper.Theory.interpret_formula cenv env
      (MiniCooper.Theory.qe f) <->
    MiniCooper.Theory.interpret_formula cenv env f
```

The project boundary exposes the corresponding closed-sentence theorem:

```coq
Mell.Presburger.Decide.presburger_decide_correct :
  forall s : sentence,
    presburger_decide s = true <-> sentence_semantics s
```

The project adapter establishes the remaining obligations as follows:

- `Presburger/QE.v` compiles project terms with backend smart constructors and
  proves `compile_formula_well_formed : wff_ue (compile_formula f)`;
- `Presburger/Syntax.v` validates de Bruijn indices at each binder and packages
  only `formula_closed 0 f = true` formulas as `sentence`; the project syntax
  has no constructor for backend abstract constants;
- `Presburger/Semantics.v` proves that a closed formula is independent of all
  environment entries, and `presburger_decide` repeats the closure check at
  runtime so proof erasure cannot expose a free-variable decision API;
- `Presburger/QE.v` proves term/formula compilation and full QE meaning
  preservation against the project's standard `Z` semantics;
- `Presburger/Decide.v` proves the quantifier-free Boolean evaluator correct
  by induction on backend `wff`, whose constructors have no existential case,
  and proves `presburger_decide_correct` for every `sentence`; and
- `Audit/PresburgerExamples.v` separately extracts the final decision function
  and its dependencies. The extraction audit checks all generated `.ml` files
  and compiles them with OCaml 4.14.2-flambda.

## Candidate comparison

| Candidate | Integer order and nonnegativity | Arbitrary alternation | Gallina correctness | Coq 8.20.1 / extraction | License | Result |
| --- | --- | --- | --- | --- | --- | --- |
| `pi8027/vass` `1ee42366a450d2743b52399a21ff80571b7bca94` | Yes (`f_leq`, standard `Z` interpretation) | Yes | `Presburger_algorithmP` | Source inspection indicates executable Gallina | No license grant in the inspected repository; GitHub metadata reports no license | Rejected: copying or dependency use is not licensed |
| `rocq-archive/presburger` `2b2636f989a93c6f374401f797319c3bad4596e9` | No: atoms are equality and congruence only | Quantifiers exist, but cannot express order | Gallina QE core | Port work is possible | LGPL-2.1-or-later | Rejected: cannot preserve T08 integer/nonnegative semantics |
| `Armael/minicooper` `3f051307039456a88cf093921278b0dcf224f7cf` | Yes: equality, strict order, and divisibility over `Z` | Yes; universal quantification is `not exists not` | `interpret_cooper`, `interpret_qe`, and `wf_qe` | Core compiled on 8.20.1; QE and final-style examples compute; QE extraction inspected | LGPL-3.0-only | Selected, subject to the adapter obligations above |

Other GitHub candidates found by repository search were either incomplete,
unlicensed, or not Presburger decision procedures.  Coq's bundled `omega`
support is a tactic/plugin interface rather than the required standalone,
extractable closed-formula Gallina decision function.

## Compatibility and execution evidence

The selected four-file core compiled with Coq 8.20.1 after these proof-only
port changes:

- replace the removed `Omega` import by `ZArith Lia`;
- replace uses of the removed `omega` tactic by `lia`;
- adjust five proof scripts where Coq 8.20 closes a goal earlier or requires
  explicit bullets.

No datatype, semantic definition, quantifier-elimination function, or
computational branch was changed.  A probe extracted `qe` to 1,240 lines of
OCaml and found no `AXIOM TO BE REALIZED`, `Obj.magic`, `failwith`, external
oracle, exception, or assertion fallback.  The extracted artifact contains
both `cooper` and recursive `qe` definitions.

Evaluation probes on Coq 8.20.1 produced:

| Closed integer sentence | Result |
| --- | --- |
| `forall x, exists y, y = x + 1` | `true` |
| `forall x, exists y, 2*y = x` | `false` |
| `forall x, exists y, x = 2*y or x = 2*y + 1` | `true` |
| `exists n, n >= 0 and n = -1` | `false` |

The source archive SHA-256 is
`81539eaea305f0a02a270ee71a489be15474f955c5b5b8a46ce06e6ab54140b1`.
The upstream LGPL v3 license SHA-256 is
`a5681bf9b05db14d86776930017c647ad9e6e56ff6bbcfdf21e5848288dfaf1b`;
the vendored copy, which differs only by a final newline, has SHA-256
`e3a994d82e644b03a792a930f574002658412f62407f5fee083f2555c5f23118`.
Vendoring must preserve the license, authorship/source notice, pinned commit,
and the port patch ledger.

## Logical assumptions

`Print Assumptions interpret_cooper` and
`Print Assumptions interpret_qe` report only `Classical_Prop.classic`.
This is used in semantic proofs and is erased by extraction.  The executable
`qe` is transparent Gallina computation and does not use classical choice, an
unimplemented mathematical result, or an external oracle.  T07's final audit
must state this boundary and print the assumptions of the project-level
correctness theorem.

## Independent review

An independent source and probe review accepted the selection subject to the
same adapter obligations.  It found no hidden defect in ordered semantics,
quantifier alternation, completeness scope, or extraction.  In particular,
the backend's `wff_ue` is not a closedness predicate; closure and exclusion of
`CAbstract` must be implemented by this project rather than inferred from
`wff_ue`.
