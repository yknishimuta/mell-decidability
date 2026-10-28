# Mechanized Decidability of Propositional MELL

## Project overview

This repository formalizes decidability for classical, commutative, propositional multiplicative exponential linear logic (MELL) in the Rocq proof assistant. It connects cut-free MELL proof search to branching vector addition systems (BVAS), proves the semilinear separation theorem needed for BVAS reachability, and extracts a total OCaml decision procedure.

The project is research software. Its machine-checked theorems prove totality and correctness, but they do not provide a useful complexity bound for arbitrary inputs.

## Main verified results

The project establishes two principal results in Rocq:

- **Decidability of BVAS reachability:** We formalize the semilinear separation theorem and establish decidability of reachability for branching vector addition systems.
- **Decidability of propositional MELL:** We verify the correctness of the reduction from MELL provability to BVAS reachability and prove the totality and correctness of a decision procedure for MELL provability.

Exact theorem statements and assumptions are checked in `theories/Audit/Statements.v` and documented in `docs/review/final-trust-report.md`.

## Formalized mathematical foundations

The development includes finite-tree and vector infrastructure, initialized BVAS runs and their well-quasi-orders, semilinear and periodic-set geometry, rational polyhedral cones, closed linearization, WSVAS exact amalgamation, safe linearization, face stripping, safety-witness rank descent, the semilinear separator theorem, and the MELL-to-BVAS many-one reduction.

The main separation argument formalizes Sections 3--7 of Bizière--Leroux--Sutre, *Solving the Reachability Problem for Branching Vector Addition Systems via Semilinear Inductive Invariants*, arXiv:2607.09558v1, with the corrections recorded in the audit documents.

## Mathematical provenance and scope of contribution

The mathematical results formalized in this repository build on the following prior work:

- **Clotilde Bizière, Jérôme Leroux, and Grégoire Sutre (2026).** [*Solving the Reachability Problem for Branching Vector Addition Systems via Semilinear Inductive Invariants*](https://arxiv.org/abs/2607.09558v1). arXiv preprint, arXiv:2607.09558v1, July 10, 2026.  
  The semilinear separation theorem for BVAS reachability, its proof architecture, and the resulting decidability argument.

- **Ranko Lazić and Sylvain Schmitz (2015).** [*Nonelementary Complexities for Branching VASS, MELL, and Extensions*](https://doi.org/10.1145/2733375). *ACM Transactions on Computational Logic*, 16(3), Article 20. [Reference PDF](https://lsv.ens-paris-saclay.fr/Publis/PAPERS/PDF/LS-tocl15.pdf).  
  The reduction through intuitionistic linear logic and branching counter systems with full zero tests, together with the elimination of those tests.

- **Philippe de Groote, Bruno Guillaume, and Sylvain Salvati (2004).** [*Vector Addition Tree Automata*](https://doi.org/10.1109/LICS.2004.1319601). In *Proceedings of the Nineteenth Annual IEEE Symposium on Logic in Computer Science (LICS 2004)*, pp. 64–73. IEEE Computer Society. [Author PDF](https://members.loria.fr/PdeGroote/papers/lics04.pdf).  
  The earlier correspondence between MELL provability and branching counter systems.

- **Clotilde Bizière, Jérôme Leroux, and Grégoire Sutre (2026).** [*Bridging the Gap Between Plain VASS and Branching VASS*](https://doi.org/10.1007/978-3-032-22730-0_4). In Nathalie Bertrand and Stefan Milius (eds.), *Foundations of Software Science and Computation Structures (FoSSaCS 2026)*, Lecture Notes in Computer Science, vol. 16503, pp. 65–87. Springer.  
  Structural and geometric results for branching vector addition systems used in the separation proof.

- **Jérôme Leroux (2012).** [*Vector Addition Systems Reachability Problem (A Simpler Solution)*](https://doi.org/10.29007/bnx2). In Andrei Voronkov (ed.), *Turing-100: The Alan Turing Centenary*, EPiC Series in Computing, vol. 10, pp. 214–228. EasyChair.  
  Background results on VAS reachability and semilinear inductive invariants.

The contribution of this repository is the reconstruction and mechanization of these arguments in Rocq, including the documented repairs, the verified composition of reductions, and the development of executable decision procedures.

The source versions, theorem correspondences, and changes to the published arguments are recorded in [`docs/review/sources.json`](docs/review/sources.json) and [`docs/review/final-trust-report.md`](docs/review/final-trust-report.md).

The original mathematical results remain attributed to the works listed above.

## Requirements and pinned dependencies

The reference environment uses:

- Coq 8.20.1 (the versioned release name predates the rename to Rocq);
- OCaml 4.14.2;
- Zarith 1.14;
- opam 2.x and `ocamlfind` 1.9.9~preview;
- the exact Coq packages and Git commits in `mell-formalization.opam.locked`.

Create a repository-local switch and install the locked dependencies:

```sh
opam switch create . ocaml-base-compiler.4.14.2
opam install . --deps-only --locked
```

The rejected experimental source tree `vendor/presburger/` is not required and is intentionally ignored. The only required vendored source is `vendor/minicooper/`.

## Building the Rocq development (Coq 8.20.1)

Generate the build makefile and build all 269 registered source files:

```sh
make Makefile.coq
opam exec --switch . -- make -f Makefile.coq -j2
```

`Makefile.conf` is an optional local override containing machine-specific paths. It is ignored and is not required for a clean build.

The opam package build invokes `make OPAMEXEC= check-core`; opam has already installed the build environment, so this avoids recursively treating opam's temporary package-build directory as another local switch.

## Running validate and coqchk

Run the generated validation target and the final statement/assumption audit:

```sh
opam exec --switch . -- make -f Makefile.coq validate
opam exec --switch . -- make check-final
opam exec --switch . -- make audit-final
```

`validate` runs `coqchk -silent -o` over all registered compiled modules and their dependency closure. `audit-final` checks the final theorem statements and assumption allowlist, verification scope, source policy, extraction policy, and forbidden constructs. Raw command logs are regenerated under `docs/review/logs/` and are intentionally not versioned.

## Extracting the OCaml decision procedure

The extraction driver is `theories/Decision/Extract.v`. Generate and compile the extracted closure with:

```sh
opam exec --switch . -- make extract-final
```

Generated `.ml`/`.mli` files are reproducible build products and are ignored by Git. The handwritten runner `docs/review/extraction/final_runner.ml` and the extraction driver remain versioned. Extraction uses `ExtrOcamlNatBigInt` and `ExtrOcamlZBigInt`; fixed-width OCaml integers are not used for Gallina naturals or integers.

## Runtime regression tests

Compile the native runner and execute the required 22-case matrix:

```sh
opam exec --switch . -- make check-runtime-mell
```

The matrix covers positive and negative MELL examples, positive and negative BVAS examples, malformed codecs, large integer arithmetic, and signed actions. All 22 small regressions passed in the audited environment. A finite-fuel result of `None` still means “not found within this fuel”; it is never reported as `false`.

## Licensing

Project-owned source and documentation are licensed under the MIT License; see the root `LICENSE`. This grant does not replace or modify licenses for third-party material.

The bundled `vendor/minicooper/` subset is licensed LGPL-3.0-only. It comes from Armael/minicooper commit `3f051307039456a88cf093921278b0dcf224f7cf`; its upstream notice and LGPLv3 text remain in that directory, and the Coq 8.20 proof-only port is documented in `vendor/minicooper/PORTING.md`. The GPLv3 text incorporated by LGPLv3 is provided as `LICENSES/GPL-3.0-only.txt`.

External opam dependencies, including Coq 8.20.1, YALLA, the Kruskal libraries, Coq-Polyhedra, MathComp, Finmap, bigenough, OCaml, `ocamlfind`, and Zarith, remain subject to their respective licenses. Exact versions, source hashes, and licenses are recorded in `docs/review/sources.json` and summarized in `THIRD_PARTY_NOTICES`.

Generated OCaml extraction output is not part of the normal Git source tree. If it is distributed as a release artifact, the distributor must review and include the notices and license texts required for the extracted Coq 8.20.1, YALLA, MiniCooper, and other incorporated third-party material; it must not be labelled wholesale as MIT-licensed.

This public repository starts from a clean, source-only root commit and does not contain the generated extraction files from the earlier development history. Exact fixed upstream versions, source archive checksums, and extraction reconstruction instructions are recorded in [`docs/third-party-source-reproduction.md`](docs/third-party-source-reproduction.md). Separating the public history does not determine or cure any legal question concerning earlier distributions; historical LGPL compliance remains unresolved.

## AI-assisted development

This formalization was developed with assistance from OpenAI Codex and ChatGPT, including proof development, code implementation, documentation, and review support.
Responsibility for the correctness, integrity, and interpretation of the published results rests with the human maintainer.

## Reproducibility and citation

Use the Git commit being cited together with `mell-formalization.opam.locked` and `docs/review/sources.json`. The final theorem, extraction, runtime, and independent-review evidence is summarized in `docs/review/final-trust-report.md`; task-specific audit files preserve the proof and correction history.

For academic citation, cite both the repository commit and the primary mathematical sources listed in `docs/review/sources.json`.
