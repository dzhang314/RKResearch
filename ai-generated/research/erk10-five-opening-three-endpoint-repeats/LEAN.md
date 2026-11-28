# Portable final triple-endpoint scalar gates

The core-only
[ERK10TripleEndpointInteriorPairScalars.lean](../../lean/RKCert/ReviewedNative/ERK10TripleEndpointInteriorPairScalars.lean)
checks both outcomes in the last exact-grade-three chart:
the intervening pair row has zero weighted input in the
two scalar taps, and the next real-clock corrected cubic
forces equality with the first live singleton. Lean
4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 all passed with
only standard axioms. The literal word, rank and chronology
proof is mathematical.

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10TripleEndpointInteriorPairScalars.lean
    sha256sum -c ai-generated/research/erk10-five-opening-three-endpoint-repeats/lean-checked.sha256
