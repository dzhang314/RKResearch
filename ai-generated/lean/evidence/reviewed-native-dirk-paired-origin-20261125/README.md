# Two true origin-zero stage residuals on the original tableau

Import `RKCert.ReviewedNative.DIRKPairedOriginResidue`. Over an arbitrary
field, take the primitive `G = X*(X-C γ)^2` and its partner `H = X*G`.
A primitive `P` defines the original-tableau residual
`A P′(c) - P(c)` and receipt polynomial `T_P = P-C γ*P′`. The
product rule gives the exact identity `T_H = X*T_G-C γ*G`.
When `γ ≠ 0`, the two receipt polynomials vanish together at a clock
if and only if the clock is `γ`. No small integer division or
characteristic-zero premise is used.

Both original residuals vanish at physical row zero when that row
has just its diagonal `γ`. At a joint-clean recipient with diagonal
`γ`, zero strictly upper entries in that row, and actual clock
different from `γ`, at least one of the earlier derivative receipts
is nonzero. If all earlier jointly clean rows have clock `γ`, this
same disjunction is about the true earlier joint-off rows: both
derivative observables drop those earlier clean rows. The result
does not assert existence of a recipient, paid incoming probes,
fibre coherence, a prefix rank, or any method-order/stage bound.

## Exact measured check

The [raw body](../../RKCert/ReviewedNative/DIRKPairedOriginResidue.lean)
and [unchanged standalone typed audit](../../AuditReviewedNativeDIRKPairedOriginResidue.lean)
exited zero on Lean v4.36.0 with Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The four typed examples
check the receipt identity, the expanded common-root equivalence,
the actual origin, and the earlier physical joint-off receipt.
The [unchanged raw output](typed-audit-output.txt) reports exactly
`propext`, `Classical.choice` and `Quot.sound` for each of four
named declarations. The audit emitted no object.

[Acceptance](acceptance.tsv) records the exact source, exit and raw
log hashes; the body primary is an observed build hash, not a shipped
binary. The single proof repair preserves the diagonal binder in the
reverse implication without changing the statement or imports. The
five checked project dependencies matched the same published source
bytes at `66849fbe91f450d45bf33c47a4a8171ccb769d6f`. This is
serial replay in one project resolver with 3,133 pinned external
modules, not a cold build or evidence on any other toolchain pair.
Normalized defects, centered payment, and joint-pivot consumers
are outside this packet.

From the repository root, with the pinned toolchain and dependencies
already available:

```sh
sha256sum -c ai-generated/lean/evidence/reviewed-native-dirk-paired-origin-20261125/checked-sources.sha256
cd ai-generated/lean
LEAN_NUM_THREADS=1 lake build +RKCert.ReviewedNative.DIRKPairedOriginResidue
LEAN_NUM_THREADS=1 lake env lean -j1 -M3000 AuditReviewedNativeDIRKPairedOriginResidue.lean
```
