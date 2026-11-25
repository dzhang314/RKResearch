# Causal defect pivots at a clean lower-triangular recipient

Import `RKCert.ReviewedNative.CausalDefectPrefixLowerTriangular`.
For the actual recipient row `k`, only the upper entries of that
row are required to be zero. Its diagonal multiplies the recipient's
entry of a probe, so it contributes nothing to a quadratic-defect
probe at a stage where that defect is zero.

The checked `paid_prefix_pivots_of_off_mass_or_clock` uses the actual
original tableau, independently paid polynomial probes through degree
`d`, and agreement of nonzero defects among earlier off copies of the
same clock. A nonzero sum of the earlier off taps **or** nonzero
clock-weighted sum gives at least `d + 2` active earlier off clocks and
the same `TriangularPrefix` witness on the literal physical prefix.
The theorem is over a field and does not assume constant diagonal.

Over a characteristic-zero field, `off_mass_or_clock_of_first_clean`
proves the disjunction if the recipient has nonzero diagonal and every
earlier stage is off. The clock keeps a diagonal term; the theorem
does not silently treat the first nonzero clean clock after earlier
clean zero-clock stages as the first clean stage. No payment,
coherence, stage bound, method order, or sharper origin result is
deduced from nonzero diagonal alone.

## Exact measured check and version boundary

The [body](../../RKCert/ReviewedNative/CausalDefectPrefixLowerTriangular.lean)
and [unchanged standalone typed audit](../../AuditReviewedNativeCausalDefectPrefixLowerTriangular.lean)
exited zero on **Lean v4.36.0 only**, with Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The six typed clients cover
the actual split, residue equivalence, clock identity, both receipt
contracts and both causal pivot conclusions. The
[unchanged raw audit](typed-audit-output.txt) reports only
`propext`, `Classical.choice` and `Quot.sound` for each of six
named declarations. No audit object was emitted.

The paired public import and private `import all` reuse only the
same v4.36.0 strict core, including its private/IR data. This packet
does not validate any earlier source snapshot's compatibility matrix
or either proof with a different compiler/Mathlib pair. A different
pair needs its own build of the strict core and this consumer.

[Acceptance](acceptance.tsv) identifies the exact source, exit and log
bytes; the primary hash records the measured body object, not a
shipped binary. All 15 provider source blobs are unchanged and match
their measured bytes at `5f50e1fde455fdfce5ec99a0802f0244e4d2127c`.
The actual run was serial replay in one coherent project object
root and 3,538 pinned external modules, not a cold package build.

From the repository root, with that same pinned toolchain and its
dependencies already present:

```sh
sha256sum -c ai-generated/lean/evidence/reviewed-native-causal-defect-prefix-lower-triangular-20261125/checked-sources.sha256
cd ai-generated/lean
LEAN_NUM_THREADS=1 lake build +RKCert.ReviewedNative.CausalDefectPrefixLowerTriangular
LEAN_NUM_THREADS=1 lake env lean -j1 -M3000 AuditReviewedNativeCausalDefectPrefixLowerTriangular.lean
```
