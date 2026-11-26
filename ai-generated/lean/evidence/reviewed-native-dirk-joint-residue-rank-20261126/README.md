# Conditional rank of the two actual incoming DIRK residues

Import `RKCert.ReviewedNative.DIRKJointResidueMomentRank`. The two
channels are the original-tableau cleared stage residuals of
`G=X(X−γ)^2` and `H=XG`; no generic scalar combination or changed
tableau is used. The earlier joint-off fibres are physical rows
with a common actual clock. For each fibre the two entries are
literal sums of the original receiver taps times the two residues.

Suppose the recipient is jointly clean with upper entries zero,
diagonal `γ≠0`, and actual clock different from `γ`, and all earlier
jointly clean clocks are `γ`. The raw receipt forces a nonorigin
nonzero residue if zero paired residue implies zero actual tap mass
on each relevant earlier fibre away from `γ`. This recovery is an
explicit input, not a conclusion from order or common diagonal. If
both actual probes are separately paid for degrees at most `d`,
grouping yields the literal paid moment matrix. Its actual active
rank `r` is positive and the number of active clocks is at least
`d+1+r`. Neither rank two nor a method-order or stage bound is
asserted by this module.

The separate centered payment bridge earns the original probes if
the recipient annihilates `zeroSpace A (4+d+1)` on columns zero at
row zero, with the displayed tree-order casts units. The first row
must have only the diagonal `γ`. These grade and annihilation inputs
do not supply fibre recovery, and no quadratic products are assumed
paid or used to infer it here.

## Exact measured check

The [body](../../RKCert/ReviewedNative/DIRKJointResidueMomentRank.lean)
and [unchanged typed audit](../../AuditReviewedNativeDIRKJointResidueMomentRank.lean)
each exited zero with Lean v4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The body log was empty.
The five typed clients check actual probe regrouping, the nonorigin
active witness from literal fibre recovery, the rank bound from
paid probes, the centered payment bridge, and the conditional joint
rank conclusion. The audit emitted no object. Its [unchanged output](typed-audit-output.txt)
reports only `propext`, `Classical.choice`, and `Quot.sound` for each
of five named declarations.

[Acceptance](acceptance.tsv) records the exact source, exit and raw
log hashes. The primary hash is observed build evidence, not a
shipped object. All 16 measured project providers matched the
actual source blobs at `f6052221c849f1593d4da00fd565a82b9e6c591c`.
The checks used one serial resolver with 3,535 stock module keys and
pinned inputs. Neither a cold build nor another toolchain pair was
measured. There is no separate recovery provider, generalized
signature argument, or order-specific consumer in this release.

From the repository root, with the pinned toolchain and dependencies
already available:

```sh
sha256sum -c ai-generated/lean/evidence/reviewed-native-dirk-joint-residue-rank-20261126/checked-sources.sha256
cd ai-generated/lean
LEAN_NUM_THREADS=1 lake build +RKCert.ReviewedNative.DIRKJointResidueMomentRank
LEAN_NUM_THREADS=1 lake env lean -j1 -M3000 AuditReviewedNativeDIRKJointResidueMomentRank.lean
```
