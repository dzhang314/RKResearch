# RKCert release compatibility

This is a manual four-pair verifier. It does not change the project's main pin, create a repository-root workflow, or publish anything. A successful run on one pair is not a claim about any other pair.

## Supported pairs for this snapshot

Lean and Mathlib always have the identical tag. See `versions.json` for the exact Lean commit, Mathlib commit, Linux release archive size and release archive SHA-256 (in that order). Each `locks/<tag>/` holds the exact downstream manifest and configuration. All transitive package revisions also come from that tag's official Mathlib manifest.

- `v4.34.1`, `v4.35.0`, `v4.36.0`: stable releases.
- `v4.37.0-rc1`: the current requested preview. Historical release candidates are outside this matrix.

## Reproduce

Prerequisites: Python 3, Git, curl, enough disk for the one pair's dependency closure, and the matching official Lean toolchain. Pass the release's binary directory with `--lean-bin` if it is not the toolchain normally selected by Elan. Work one release at a time. The output directory must be new and outside the source checkout.

Example, using the proof project directory containing `RKCert.lean`:

```sh
python3 ai-generated/release-compatibility/check_release.py \
  --project /path/to/RKCert-project --version v4.34.1 \
  --output /path/to/new-work/v4.34.1
```

Add `--prepare-only` for a no-network source/lock preparation check, or `--kernel all` for separate in-process default-kernel replays of every project module rather than the eight main endpoints. The script checks the exact toolchain's Git commit. It does not download a compiler itself; Elan may install a missing selected toolchain. Official distribution SHA-256 values are provided for installations outside Elan. Git fetches only the exact source revisions in the pair's lock. Cache downloads cover only direct Mathlib imports and their transitive closure, from the official master cache. They are limited to eight simultaneous transfers.

The source input must match the published `73574fefa5544ae838ad3257f20baf672c0e4c23` proof tree or the precisely fingerprinted portability candidate; `portability.patch` is applied only to the isolated copy. The compatibility edits are confined to proof bodies and retain the original public statements: endomorphism composition and identity use common Mathlib APIs; coefficient extraction uses stable polynomial lemmas; rank-one spanning uses the native singleton basis; named induction branches and expensive implicit grade inference are made explicit. No heartbeat threshold is raised, and no theorem statement, axiom or external solver is added. No file from another pair is used as a project proof artifact. For a newer source commit, take a new exact fingerprint and rerun the full matrix. A release should not be claimed until same-tag Mathlib exists and every check succeeds on that source.

Machine-readable results are in `results.json`; `verified/<tag>/` keeps the corresponding build, eight audit and eight replay logs. The measured platform is x86-64 Linux, not every supported operating system.

## What is checked

The build explicitly requests the aggregate **and each of the 152 proof modules**, including the audit-only `DirkGradeSixRegression` module. It checks that all module output files exist. Eight audit scripts issue 227 queries for 223 distinct declarations. Each returned declaration name must match the baseline list; each reported axiom must be one of `propext`, `Classical.choice`, `Quot.sound` (or the declaration reports none). The default focused replays cover the logarithmic ERK theorem, order-12 ghost gate, SDIRK order-six ring theorem, the grade-six DIRK regression, ERK order 12, the reverse order-12 obstruction, the DIRK parity floor, and the low-order ERK structural result.

Source fingerprints and exact dependency commits are checked again after testing. Raw output and the machine-readable pass result go to the work directory's `release-evidence/`.

A build establishes elaboration and kernel acceptance by **that** Lean release on the checked inputs, not general compiler soundness. Axiom listings are diagnostics, not a substitute for independent verification. Individual `leanchecker` replays exercise the release's own kernel with imports; they are not an independently implemented checker or a fresh replay of all Mathlib.

## Check the recorded evidence without a toolchain

Run `python3 verify_evidence.py` in this directory to verify the bundle's file checksums and cross-check all four rows against the supplied locks, compiler-version logs, build results, axiom outputs, and replay logs. It runs offline, rejects missing or altered evidence, and does not rerun the proofs. A checksum list inside the archive is not a signature; use the separately supplied ZIP hash to check the identity of the whole archive.
