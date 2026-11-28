# Portable triple-and-pair scalar gates

The standalone core module
[ERK10TriplePairScalars.lean](../../lean/RKCert/ReviewedNative/ERK10TriplePairScalars.lean)
checks the shifted \(3\times3\) chronology determinant, the zero-first
score coefficient, and the common exceptional square/clock exit.
It imports no Mathlib and passes Lean 4.34.1, 4.35.0, 4.36.0 and
4.37.0-rc1, with standard axioms only. The rank, nilpotent bridge,
weights projection, and complete physical chronology case proof
are mathematical.

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10TriplePairScalars.lean
    sha256sum -c ai-generated/research/erk10-five-opening-triple-pair/lean-checked.sha256
