# Checked rational Vandermonde moments

The [native module](../../RKCert/ReviewedNative/RationalVandermondeMoments.lean)
proves that any prescribed list of \(n\) rational moments is realized
on \(n\) distinct rational samples. It uses the inverse of the
transposed Vandermonde matrix, with nonvanishing determinant coming
from injectivity of the sample map. The proof checks the specified
moment equation for each \(k\in\mathrm{Fin}\,n\).

Two specializations give rational weights for the primitive moments
\(x^{k+1}/(k+1)\), and copy weights with prescribed zeroth and first
moments and zero at the remaining supplied degrees. They make no
claim about the signs of weights. Only degrees in \(\mathrm{Fin}\,n\)
are prescribed, including in small dimensions.

The [unchanged typed audit](../../AuditReviewedNativeRationalVandermondeMoments.lean)
checks the three moment formulas. The [raw audit output](typed-audit-output.txt)
report for each proof uses only propext, Classical.choice, and Quot.sound.

## Measurement and scope

The unchanged body and the separate no-output audit both exited zero
with Lean 4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The body used stock libraries only. The audit used its five exact
compiled fragments as the only project provider, and left project
inputs unchanged. The [portable acceptance record](acceptance.json)
records the exact source, object and output digests. No compiled object
is shipped. These measurements were not a cold package build.

This is a finite rational moment solve. It does not construct a full
Runge–Kutta donor array or tableau, verify its order, or establish a
nonnegative representation.

With the pinned dependencies already available, the sources and named
reports can be checked from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-rational-vandermonde-moments-20261125/checked-sources.sha256
    cd ai-generated/lean
    LEAN_NUM_THREADS=1 lake build +RKCert.ReviewedNative.RationalVandermondeMoments
    LEAN_NUM_THREADS=1 lake env lean -j1 -M3000 AuditReviewedNativeRationalVandermondeMoments.lean
