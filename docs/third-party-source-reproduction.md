# Third-party source and extraction reproduction

This document records the fixed upstream source and build information needed
to reproduce the MELL project's OCaml extraction outputs. Generated OCaml
files are not committed to this clean public Git history.

This is a technical reproducibility record, not a legal-compliance warranty.
Separating this public history from the earlier development history does not
alter earlier Git blobs or determine or cure any question concerning an
earlier distribution. Historical LGPL compliance remains unresolved.

## Fixed source versions

| Component | Fixed source | License | Source archive SHA-256 |
|---|---|---|---|
| Rocq/Coq | 8.20.1, tag `V8.20.1`, commit `fd609f07dab2d2720695882a711cd0a022068ea8` | LGPL-2.1-only | `09ad16977bb6645050b7e715f015d4333df7ff5a6a486d120f82e19be59a4767` |
| YALLA | 2.0.6, commit `e4dabaf0656a5c924bf86061a0179bd796626343`, including OLlibs 2.0.7 | LGPL-3.0-or-later | `a3eff3e456333e72a85c758530588d6d7c7ee071b9e56b013245b55e540e8e9c` |
| MiniCooper | commit `3f051307039456a88cf093921278b0dcf224f7cf` | LGPL-3.0-only | `81539b3881df365f1b5d4ab65685d669f077227023b3596c9a603109d0c9955b` |

The normal source tree vendors the four MiniCooper files actually used by the
formalization. Their upstream notice and license are in
[`vendor/minicooper/NOTICE`](../vendor/minicooper/NOTICE) and
[`vendor/minicooper/LICENSE`](../vendor/minicooper/LICENSE); the Coq 8.20 port
is documented in
[`vendor/minicooper/PORTING.md`](../vendor/minicooper/PORTING.md).

The complete fixed upstream archives, project source snapshots, extraction
drivers, license texts, and checksum manifest have also been assembled as:

```text
mell-p3d-corresponding-source-1.0.0.tar.gz
SHA-256 970e2fb53169ac35aed6cd7a67f914f65f7a7ca0652f00b4d10fa4a591e12842
```

That archive is maintained outside this Git repository. A distributor that
conveys extraction artifacts must provide the applicable source and notices
through a durable distribution channel; the checksum above authenticates the
prepared source package but is not itself a download location.

## Current extraction build

The audited environment is Rocq/Coq 8.20.1, OCaml 4.14.2, Zarith 1.14,
YALLA 2.0.6 with OLlibs 2.0.7, and the dependencies fixed in
[`mell-formalization.opam.locked`](../mell-formalization.opam.locked).

After installing those dependencies, generate the Coq makefile, compile every
registered module, and run the project extraction target:

```sh
make Makefile.coq
make -f Makefile.coq -j2
make extract-final
```

The target runs the extraction driver
[`theories/Decision/Extract.v`](../theories/Decision/Extract.v). Generated
files are written under `docs/review/extraction/final/` and are ignored by
Git. The handwritten runner
[`docs/review/extraction/final_runner.ml`](review/extraction/final_runner.ml)
remains versioned.

## Historical reconstruction inputs

For byte-level investigation of the earlier generated outputs, the prepared
corresponding-source archive contains source-only project snapshots at:

- `25f84582a9cebf9984e919a194169579d241deda` for the final extraction;
- `f60ec029ce1aa37c4d6e73a26aea748c0a8c33f6` for the Presburger extraction.

Each snapshot must be built completely before invoking its extraction driver.
The final snapshot rebuilt 260 registered modules and produced 134 generated
files. The Presburger snapshot rebuilt 36 registered modules and produced 36
generated files. These facts describe technical reconstruction only and do
not reclassify the legal status of any earlier distribution.

Additional dependency source identities and licenses are recorded in
[`review/sources.json`](review/sources.json) and
[`../THIRD_PARTY_NOTICES`](../THIRD_PARTY_NOTICES).
