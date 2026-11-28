# Portable eight-label one-triple scalar gates

The separate core module
[ERK10EightLabelTripleScalars.lean](../../lean/RKCert/ReviewedNative/ERK10EightLabelTripleScalars.lean)
checks the denominator-cleared delayed-second-copy \(3\times3\)
determinant, the two-primitive third-copy determinant, and the
exceptional \(b=a/2\) zero-tap conclusion. It imports no Mathlib.
Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 passed with only
standard axioms. The full physical-rank/chronology proof and
adaptation of the prior nonic to the raw terminal chart are
mathematical.

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10EightLabelTripleScalars.lean
    sha256sum -c ai-generated/research/erk10-five-opening-eight-label-triple/lean-checked.sha256
