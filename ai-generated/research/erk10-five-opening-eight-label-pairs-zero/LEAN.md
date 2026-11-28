# Portable raw two-pair scalar evidence

The core-only
[ERK10EightPairRawScalars.lean](../../lean/RKCert/ReviewedNative/ERK10EightPairRawScalars.lean)
checks both corrected closing-coordinate formulas without dividing
by a physical or pooled weight, the sixth-target elimination, and
a dormant contrast coefficient gate. The reused \(3\times3\)
delayed-close determinant is checked in
[ERK10EightLabelTripleScalars.lean](../../lean/RKCert/ReviewedNative/ERK10EightLabelTripleScalars.lean).
Lean 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1 passed with standard
axioms only. The physical chronology and raw terminal proof are
mathematical, and the already archived nonic scalar replay is separate.

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10EightPairRawScalars.lean
    sha256sum -c ai-generated/research/erk10-five-opening-eight-label-pairs-zero/lean-checked.sha256
