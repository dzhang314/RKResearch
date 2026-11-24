# RKCert release compatibility: published snapshot 1e545bba

Four matching Lean / Mathlib release pairs on x86-64 Linux: stable 4.34.1, 4.35.0 and 4.36.0; current preview 4.37.0-rc1. No historical release candidates. This is separate from the earlier 152-module report and changes no root workflow or default pin.

## Scope and identity

All 207 original Lean files (192 RKCert proof modules, one umbrella, and fourteen audit scripts) were matched by exact paths and individual Git blob IDs against commit `1e545bba1299aa7baf88e01ee458524571672120`. The recursive upstream tree and per-source Git blob IDs are provided. The original SHA-256 source-manifest digest is `6d7d570f38c360b8bc701e7ca8b85d8d929090d66b5703b5a91688273fa286f8`; the single post-patch source-manifest digest tested on every row is `b72478a9cea1fdb47ae7facd01d8d92aa381ce6b9ebc78f658681bcd8d54da34`. The manifest is the SHA-256 of a sorted list of per-file SHA-256 hashes with relative paths. The `portability.patch` file applies directly to the real published tree, including its original whitespace. `incremental-portability.patch` is only the additional change after applying the previous 24-file compatibility patch to that same tree.

All 192 individual proof modules and the umbrella are explicit build targets, including the audit-only regression. All fourteen audit files run; 308 queries report on 302 distinct declarations. The fifteen named same-release kernel replays are exactly those in `focused-modules.json`. The offline verifier also checks that the clean build log explicitly lists every one of the 193 project targets, not merely the successful aggregate. This includes the prior endpoints plus the new even-DIRK, ERK order-eight, Lobatto-factor, finite-midpoint, DIRK15-support and joint-hidden certificate endpoints. The accepted reported axiom set is `propext`, `Classical.choice`, `Quot.sound` or none.

## Reproduce a release row

Use Python 3, Git and the matching official Linux Lean release. From the directory of this README:

```sh
python3 check_release.py --project /path/to/RKResearch/ai-generated/lean \
  --version v4.34.1 --output /path/to/new-isolated-run
```

Pass `--lean-bin /path/to/lean/bin` if the exact release is not selected by Elan. The output must be new and outside the project. The script accepts only the exact published or exact candidate source manifest, copies all proof files, and applies the full patch only to the copy. `--prepare-only` checks these steps offline. `--kernel all` requests every project module rather than the fifteen focused replays.

The status refers to the exact release binary Git commit, Mathlib same-tag revision, all eight official transitive dependencies, and the project proof bytes. The runtime checks package HEADs, clean sources, inherited locks and Mathlib's own lean-toolchain declaration. Only the official master Mathlib cache for the direct-import closure is requested, with eight simultaneous transfers. All four `locks` sets and official Linux-distribution archive hashes are supplied. Source and lock identities are checked again after the run.

`results.json` contains the row-level outcomes; `verified/<tag>/` retains the observed compiler, build, audit and replay outputs. Run `python3 verify_evidence.py` to recheck the sealed evidence offline without Lean. This verifies internal checksums and the consistency of the reported results; to verify the ZIP's identity, use its separately supplied digest. The offline verifier also reconstructs `audit-reporting-differences.json` from the raw audit text: exact reported axiom subsets may vary between releases, even though all stay inside the same three allowed standard axioms. Differences alone cannot distinguish changes in imported proof terms from changes in reporting. Kernel replays use the same release's kernel and trust imports. They are not an independent implementation, and axiom diagnostics are not a proof of general compiler soundness. The matrix does not imply support for other proof revisions, release tags, or platforms.

## Additional proof-only changes from the 152-module common patch

Changed in the additional patch: `RKCert/Dirk15CubicOrbit.lean`, `RKCert/ERKLowEndpointCore.lean`, `RKCert/ERKLowLobatto.lean`.

Four proof lines differ: one uses `Module.End.one_eq_id` and `LinearMap.id_apply` for the identity endomorphism, and three explicitly use `Polynomial.coeff_monomial` to evaluate coefficients off the monomial degree. No theorem statement, arithmetic certificate, allowed axiom, or heartbeat threshold changed. The exact trailing space already present in the published `DirkShortTrace.lean` is preserved.
