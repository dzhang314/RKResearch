# RKCert release compatibility: published snapshot eb274e3

Four matching Lean / Mathlib release pairs on x86-64 Linux: stable 4.34.1, 4.35.0 and 4.36.0; current preview 4.37.0-rc1. No historical release candidates. These results are separate from the earlier 152- and 192-module reports. This patch changes no workflow, default pin, public statement or dependency.

## Scope and identity

All 303 original Lean files (280 RKCert proof modules, one umbrella, and twenty-two audit scripts) were matched by exact paths and individual Git blob IDs against commit `eb274e3318ac8192541b980deed9d1116d266bef`. The recursive upstream tree and per-source Git blob IDs are provided. The original SHA-256 source-manifest digest is `d16e52a4aea379854b5eb7e615a028e0b3a5975ae91cc90a0ad3d47088301177`; the single post-patch source-manifest digest tested on every row is `5764aead631377f3d70deef5afc65d766eef32fbccb00dc0a439d7412688288f`. The manifest is the SHA-256 of a sorted list of per-file SHA-256 hashes with relative paths. The `repository-root.patch` applies at the repository root and changes only files under `ai-generated/lean/RKCert/` (`git apply --check /path/to/repository-root.patch` previews it). `portability.patch` has identical proof changes but applies from the Lean project directory; its intake preserves all published source whitespace. `incremental-portability.patch` is only the additional change from the previous 27-file compatibility patch on the exact new tree.

All 280 individual proof modules and the umbrella are explicit build targets, including the audit-only regression. All twenty-two audit files run; 428 queries report on 422 distinct declarations. The thirty named same-release kernel replays are exactly those in `focused-modules.json`. The offline verifier also checks that the clean build log explicitly lists every one of the 281 project targets, not merely the successful aggregate. The replays include the prior endpoints and the newly archived local-DIRK, Radau, order 14/16–19 ERK, and order 18/20 and order-22-and-up DIRK results, along with their principal arithmetic certificate modules. The accepted reported axiom set is `propext`, `Classical.choice`, `Quot.sound` or none.

## Reproduce a release row

Use Python 3, Git and the matching official Linux Lean release. From the directory of this README:

```sh
python3 check_release.py --project /path/to/RKResearch/ai-generated/lean \
  --version v4.34.1 --output /path/to/new-isolated-run
```

Pass `--lean-bin /path/to/lean/bin` if the exact release is not selected by Elan. Optional `--threads` sets compiler parallelism (default 4); separate audit and replay invocations run two at a time. The output must be new and outside the project. The script accepts only the exact published or exact candidate source manifest, copies all proof files, and applies the full patch only to the copy. `--prepare-only` checks these steps offline. `--kernel all` requests every project module rather than the thirty focused replays.

The status refers to the exact release binary Git commit, Mathlib same-tag revision, all eight official transitive dependencies, and the project proof bytes. The runtime checks package HEADs, clean sources, inherited locks and Mathlib's own lean-toolchain declaration. Only the official master Mathlib cache for the direct-import closure is requested, with eight simultaneous transfers. All four `locks` sets and official Linux-distribution archive hashes are supplied. Source and lock identities are checked again after the run.

`results.json` contains the row-level outcomes; `verified/<tag>/` retains the observed compiler, build, audit and replay outputs. Run `python3 verify_evidence.py` to recheck the sealed evidence offline without Lean. This verifies internal checksums and the consistency of the reported results; to verify the ZIP's identity, use its separately supplied digest. The offline verifier also reconstructs `audit-reporting-differences.json` from the raw audit text: exact reported axiom subsets may vary between releases, even though all stay inside the same three allowed standard axioms. Differences alone cannot distinguish changes in imported proof terms from changes in reporting. Kernel replays use the same release's kernel and trust imports. They are not an independent implementation, and axiom diagnostics are not a proof of general compiler soundness. The matrix does not imply support for other proof revisions, release tags, or platforms.

## Additional proof-only changes from the 192-module common patch

Changed in the additional patch: `RKCert/DirkLocalProjection.lean`, `RKCert/DirkLocalWords.lean`, `RKCert/ERKFiniteLeakage.lean`, `RKCert/ERKFiniteShifts.lean`, `RKCert/ERKOrderNineRadau.lean`, `RKCert/ERKOrderedQ7Knots.lean`, `RKCert/ERKOrderedQ7Leakage.lean`, `RKCert/ERKOrderedQ7Shifts.lean`, `RKCert/RadauPhysicalNondivisibility.lean`.

Nine proof modules were changed beyond the independently verified 27-file patch. These are compatibility edits inside existing proofs: spell polynomial scalar coefficients as a constant polynomial multiplication, explicitly reduce off-degree monomial coefficients in the fixed Radau quartic, and use the stable linear-map identity and composition equations. The local-projection induction simplifies both products together so it does not depend on the order of single-occurrence rewrites. No theorem statements, hypotheses, numerical factors, audit scripts, module structure, options, or heartbeat limits changed. No extra trust declaration or package was introduced.

The original 27-file patch alone failed on 4.34.1 at coefficient-normalization steps in ERKFiniteShifts and ERKOrderedQ7Shifts. A later incremental trial isolated the remaining local-projection and Radau quartic proof adjustments. Those diagnostic runs are not counted as completed matrix rows.


The exact trailing space already present in the published `DirkShortTrace.lean` is preserved.
