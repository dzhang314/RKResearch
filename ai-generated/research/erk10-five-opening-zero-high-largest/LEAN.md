# Portable scalar certification

Run the compiler for each target release from the repository root:

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10ZeroHighLargestScalars.lean

The stock compilers 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 all
elaborate the same source with no Mathlib import. For
`pureZeroHeadDet`, `pureZeroRepeatFactors`,
`forwardResidualSecondDifference`, and `pureZeroDistinctExit`,
the only axioms reported are `propext`, `Classical.choice`, and
`Quot.sound`. These are exact scalar certificates, not a Lean
claim of impossible rooted order for the whole chart.
