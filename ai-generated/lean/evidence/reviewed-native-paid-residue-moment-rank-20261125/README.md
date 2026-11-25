# Rank bound from paid residue moments

Import `RKCert.ReviewedNative.PaidResidueMomentRank`. Over a field,
let `S` be a finite set of distinct clocks and `w x i` the entry of
channel `i` at clock `x`. Assume each channel's actual moments
`∑ x ∈ S, P(x) * w x i` vanish for every polynomial of degree at
most `d`. If `r` is the rank of that literal residue matrix, then
`min(S.card,d+1)+r ≤ S.card`, including the zero-rank and empty cases.

In the proof, select `min(S.card,d+1)` clock labels and build their
Lagrange test rows on `S`. Evaluation gives an explicit right inverse
by zero extension. The literal test matrix times the residue matrix
is zero, so its kernel contains the residue column range. Rank/nullity
gives the bound. Filtering zero residue rows preserves payment; on
the actual active support, positive rank (or one actual nonzero entry)
therefore forces at least `d+1+r` distinct active clocks. The same
statement applies to two channels without inferring rank two from
both columns being nonzero.

This theorem needs neither a tableau nor fibre recovery. It does
not prove that any particular incoming probes are paid, or establish
a method-order or stage bound.

## Exact measured check

The [body](../../RKCert/ReviewedNative/PaidResidueMomentRank.lean)
and [standalone typed audit](../../AuditReviewedNativePaidResidueMomentRank.lean)
both exited zero with Lean v4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The body imports no
other project module. It retained one nonblocking unused-section-
variable lint warning. The audit checks five published declarations,
including the rank of the literal matrix column map and the bound for
two channels with one actual nonzero entry. The audit emitted no
object, and the [unchanged output](typed-audit-output.txt) lists only
`propext`, `Classical.choice`, and `Quot.sound` for each of its five
named declarations. The audit's single annotation repair uses the
qualified stock matrix-to-linear-map function without changing the
tested formula or the accepted body.

[Acceptance](acceptance.tsv) gives the exact source, exit and raw
log hashes. The recorded primary hash is evidence, not a shipped
binary. The two checks used one serial resolver with 3,532 stock
module keys and pinned inputs. The source and package hashes were
verified against `b31f9188a998b760d736b2c81abdfe39cfeb9178`; this is
not a cold build or a compatibility claim for another toolchain.

From the repository root, with the pinned toolchain and dependencies
already available:

```sh
sha256sum -c ai-generated/lean/evidence/reviewed-native-paid-residue-moment-rank-20261125/checked-sources.sha256
cd ai-generated/lean
LEAN_NUM_THREADS=1 lake build +RKCert.ReviewedNative.PaidResidueMomentRank
LEAN_NUM_THREADS=1 lake env lean -j1 -M3000 AuditReviewedNativePaidResidueMomentRank.lean
```
