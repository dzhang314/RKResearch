# Core-Lean exact normalized center arithmetic

This independent source imports only Init. It checks the exact
denominator-cleared polynomial identities for the normalized five-word
readout of the first center and the two nontrivial null-vector ratios
needed to vary the second center. No numerical integration, ordering,
tolerance, or prime-field spot check is used.

The kernel checks every individual coefficient. The sparse lists
encode exponent vectors in radix 64 and carry a verified total-degree
bound below 64. The structural merge preserves all terms; the
final signed group sum requires each monomial coefficient to vanish.

These are the arithmetic identities *before* the physical tableau
adapter. This packet does not claim that the new center rows or full
eight-word action have passed Lean. The separate candidate proof map
describes the still-unverified lift through the actual paid donors.

Regenerate the file from the repository root:
  python3 ai-generated/research/erk10-fifteen-fixedq-29adic/generate-center-scalar.py --core /tmp/CenterCore.lean
Replay directly:
  lean ai-generated/lean/RKCert/ReviewedNative/ERK10FixedQ29AdicCenterCore.lean
