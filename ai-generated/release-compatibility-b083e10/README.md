# RKCert release compatibility: b083e10

The input is the exact published `b083e10b47b15b67bf0306ba49ecc44052acf9ad` tree. All 513 Lean paths and blob IDs were checked against its Git tree, including the 36 earlier portability edits already on main. The published source manifest SHA-256 is `bdf39b8dc65cdd73b2b68ab0b8bc45f9781fa85ea92b5804466390532545e4d3`. The one common candidate checked across these releases has manifest SHA-256 `f31683d3c15004a0eaf7692cfe214a0ef600bcd95d65d98f864f171824fb3267`.

The support matrix is **Lean and Mathlib 4.34.1, 4.35.0, 4.36.0, and current 4.37.0-rc1**, with exact same-tag dependencies on x86-64 Linux. No historical RC was tested. The three pinned 4.36 release-checkout configuration blobs are identical to the published repository. No workflow or pin is changed.

## Proof patch

`repository-root.patch` applies at the repository root; use `git apply --check /path/to/repository-root.patch` first. `portability.patch` makes the same edits from `ai-generated/lean`. These contain only the new changes from `b083e10`; the prior 36-file patch is already in that commit. If you already applied the standalone one-file Radau repair and no other source changes, use `repository-root-after-collision.patch` instead; the CLI detects that exact intermediate source fingerprint and applies only the remaining proof edits.

The supplemental edits are confined to the 189 newly added proof modules. They use stable identity/composition and noninclusion lemmas, explicit polynomial coefficient extraction, ordinary cancellation by a verified nonzero scalar, and explicit proof grades and indices to keep the original elaboration budgets. An interpolation proof uses the original characteristic-zero assumption explicitly; no signatures, mathematical coefficients, compiler options, or heartbeat limits changed.

One already isolated integration correction keeps the original p14 ReverseTrace.pair_polynomial name and gives the distinct Radau identity the name ReverseTrace.pair_polynomial_radau. Only the definition name and its single internal use differ in that file; both propositions are unchanged. On v4.36.0 the original two-module import actually failed with the duplicate named declaration, while the repaired full published umbrella and its two original audits passed. The distinct one-file-only receipt was verified before these ports and is not a four-pair portability claim.

The stage-by-stage excerpt in `porting-diagnostics.json` records exact oldest-release smoke failures and the independent name-collision diagnostic. Those smoke attempts do not count toward the final clean matrix.

## Recheck

Use Python 3.9 or newer, Git, curl, and the matching official release. The four configurations in `locks/` include all eight exact transitive dependency revisions. `versions.json` includes both upstream Git commits and the official Linux compiler archive size and SHA-256.

```sh
python3 check_release.py --project /path/to/RKResearch/ai-generated/lean \
  --version v4.34.1 --output /path/to/new-isolated-run
```

Use `--lean-bin /path/to/bin` if the exact Lean release is not selected by Elan. The output must be new and disjoint from the input. `--prepare-only` checks source, patch and pin setup without network or compiler use. `--jobs` controls parallel proof compilers (default two). `--kernel all` asks for a named kernel replay of every project proof module.

Lake fetches the official matching Mathlib cache for the direct-import closure. Each proof file, including the umbrella and audit-only regression, is then compiled by that exact `lean -o` compiler in project dependency order, **with initially empty project outputs and no reused project proof objects for any claimed matrix row**. Unneeded generated C files are not retained; this is a proof compatibility check, not a native-code build or benchmark. The earlier 189-module diagnostic reused the previous same-version proof artifacts to isolate failures and is not a matrix pass.

All 43 original Lean audit scripts run and return 875 matching query results covering 864 distinct declarations. Each release has 43 default-kernel replays, whose exact module names are in `focused-modules.json`. The reports allow `propext`, `Classical.choice`, `Quot.sound`, or none. Any variation in reported standard subsets is tabulated; it establishes neither its cause nor general compiler soundness. The replays use the same release's kernel with imports and are not independent checkers.

`results.json` contains the release rows. `python3 verify_evidence.py` rechecks the sealed evidence offline, including all 470 module/source hash pairs, every audit result, the release lockfile identities, and the exact replay set. The seal is a checksum list, not a signature.
