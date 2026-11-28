# Native late Jacobi coefficient certificate

**DIRKOrderElevenInvisibleSixAlphaOneLateJacobiReplay**
checks the integer-scaled four-by-four Gram minor (determinant 18),
all four orthogonality moments, and all six Jacobi-factor coefficients.
It is Mathlib-independent and uses ordinary kernel reduction only.

All three statements are axiom-free on Lean 4.34.1, 4.35.0,
4.36.0 and 4.37.0-rc1. The separate mathematical proof uses
these checks inside an actual rooted-order late-clock argument;
this certificate does not by itself formalize that rooted ingress.
