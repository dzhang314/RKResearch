# ERK order eight: physical localization of the four-off case

Import `RKCert.ReviewedNative.ERKOrderEightFourOffPhysicalPlacement`.
The checked producer is
`RKResearch.Certified.Graded.FourOffPhysical.physical_placement_of_order8_four_off`.
It takes a strictly lower tableau on `Fin 10`, the original reviewed
`RKResearch.HasOrder 8 A b`, and four distinct clocks carrying the
actual quadratic stage defect, over an ordered field. It does not take
a caller-supplied rank, clean profile, positivity of individual weights,
or stage position.

The producer earns the tagged rank and mass data and, within this
four-off case, the unique repeated tag with its second occurrence at
physical index 8, clean rows 6, 7 and 9, and first nonzero clean row
at index 4 or 5. Indices are zero-based. Agreeing abscissas without
agreeing clean/off tags do not count as a repeated tag. The output is
actual physical data `∃ P i k, Placement A b P i k`, **not** a four-off
contradiction, an all-ten-stage exclusion, or an eleven-stage lower
bound. No stage table or coverage count changes.

## Exact measured check

The four body modules and the original
[no-output typed audit](../../AuditReviewedNativeERK8FourOffPhysicalPlacement.lean)
exited zero with Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The audit checks both the
producer's type and the literal expanded chronology. The
[unchanged raw audit](typed-audit-output.txt) reports the exact rank,
repeat, row-six and placement declarations, with no axioms beyond
`propext`, `Classical.choice`, and `Quot.sound`. It emitted no object.

[Acceptance](acceptance.tsv) records exact source, exit, and raw log
hashes; primary object hashes describe the measured build, not files
included in this overlay. Previously published dependencies, including
the tagged census and `UnitBetaSquareMass`, are unchanged at integration
base `87ed3feb597e09618efec984b52a2ee6473fb3bb`. Narrow proof repairs
explicitly supply tag/degree arguments in Rank, give existing linear
algebra and residue arguments their expected types in Repeat, expose
literal coordinates and normalize the clock and transpose presentations
in Rows, and correct a zero product rewrite and equality orientation in
Placement. The statements and mathematical steps did not change.

From the repository root, with the pinned toolchain and dependencies
already present:

```sh
sha256sum -c ai-generated/lean/evidence/reviewed-native-erk8-four-off-physical-20261125/added-sources.sha256
cd ai-generated/lean
lake build +RKCert.ReviewedNative.ERKOrderEightFourOffPhysicalPlacement
lake env lean -j1 -M3000 AuditReviewedNativeERK8FourOffPhysicalPlacement.lean
```

The measured evidence is a serial replay against exact warm dependencies
in one project object root; it is not a separate cold package build.
