# T10-D Task 5D implementation plan

1. Audit the Task 2B/4B/5B/5C public APIs and record their exact types.
2. Add a failing audit module that names the Task 5D public contracts.
3. Implement positive scaling, support masks, same-key extensionality, and finite representative selection in `FiniteKirchhoffRelations.v`.
4. Implement the cone/union equivalence, finite-union definability, Corollary 5.16, and the run-transformer corollary in `KirchhoffCorollary516.v`.
5. Add focused boundary regressions and the Task 5D audit report.
6. Run focused builds after each checkpoint, then force the full `_CoqProject` build, `coqchk -silent`, type/assumption audits, forbidden-construct scan, `git diff --check`, and an independent review.
7. Stage only Task 5D files, commit locally, and stop before Task 6.
