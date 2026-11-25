# Ordered-field polynomial arguments

Three new modules and two named audits were verified with the pinned Lean and Mathlib 4.36.0. The pure polynomial arguments require only an ordered field.

- `OrderedOriginSignedSquares` derives two primitive-square identities from three local moments and a degree-six space of global moments. In particular the last chronological clock is positive, and if the first is positive then `(1-u)(u-w) < 0`.
- `CubicEndAlgebra` turns the two reflected end equations into strict cutoff bounds by one explicit sum-of-squares identity.
- `CubicAnchoredCutoff` earns those equations from the literal two moments at each end and proves eventual positivity of the monic cubic and of its anchored primitive. The non-unit anchor is an explicit hypothesis.

These statements are scalar ingredients, not new stage lower bounds. No geometry producer or archived elimination certificate is imported. Separately, the SDIRK(11,8) folder contains a source-level exact certificate of five full-box guard signs, not a Lean result or a method construction.
