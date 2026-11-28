# Cross-release packed Bézout receipts

These are resource-light, standalone alternatives to the two original
GF(103) Lean receipts for the exact live-cubic projection. They use the
same frozen Bézout coefficients and no Mathlib imports, axiomatic
native execution, or changed mathematical hypotheses. Kernel reduction
checks one exact Nat multiplication, the residue of every relevant
27-bit digit, and the absence of higher digits. The generator checks
that its inputs have at most 3121 coefficients, all below 103, and that
the sum of two integer convolution coefficients never reaches the
packing base: \(2\cdot3121\cdot102^2<2^{27}\). Thus there is no carry.

From this directory, regenerate the two .lean files after placing this
supplement next to the two main research packets:

    python3 generate-packed.py five \
        ../dirk11-thirteen-invisible-six-cubic-compact-projection/gamma5-bezout-103.txt \
        ../../lean/RKCert/ReviewedNative/DIRKOrderElevenInvisibleSixCubicLiveFivePacked.lean
    python3 generate-packed.py pair \
        ../dirk11-thirteen-invisible-six-cubic-live-global/pair-bezout-103.txt \
        ../../lean/RKCert/ReviewedNative/DIRKOrderElevenInvisibleSixCubicLivePairPacked.lean

Both Lean files elaborated with exit 0 on Lean 4.34.1, 4.35.0,
4.36.0 and 4.37.0-rc1. These are arithmetic receipts, not standalone
formalizations of the exact rational projections or rooted tableau
ingress. The latter scope is unchanged.
