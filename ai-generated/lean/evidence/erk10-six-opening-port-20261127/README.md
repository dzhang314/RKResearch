# Exact reviewed rational early port

The native module has an actual six-row lower-triangular rational matrix
and exact order-five weight row. It proves the sixth tall fails as
1/800 rather than 1/720. Its seventh stage is literally that weight row
evaluated, and the theorem localThroughSix checks the normalized
derivative at that stage for every human-reviewed rooted tree through
size six, by induction from HasOrder 5. No native axiom is used.

Compile RKCert.ReviewedNative.ERK10SixOpeningLocalPort with the reviewed
libraries and run this Audit. Tested on Lean/Mathlib 4.36.0; the separate
Core cross-diagonal module was replayed on all four releases. This audit
does not formalize the complete fourteen-stage conditional obstruction.
