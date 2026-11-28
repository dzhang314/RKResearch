# Portable scalar receipt and replay

From repository root, check source hashes and run the
independent exact symbolic arithmetic:

    sha256sum -c ai-generated/research/erk10-fifteen-split-host-rank/sources.sha256
    cd ai-generated/research/erk10-fifteen-split-host-rank
    python3 -B audit.py | diff -u exact-audit.txt -

With any of the tested stock toolchains, from repository root:

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10SplitHostRankScalars.lean

The core-only theorem is
'RKResearch.Certified.ERK10SplitHostRankScalars.rootlessProjective'.
It proves the finite, projective modulo-seven root exclusions
for all six guard polynomials on both homogeneous coordinates.
The source prints its axioms. The exact symbolic replay,
the passage from primitive rational numerator/denominator
to a nonzero projective pair, the rank and causal arguments,
the scalar host gates and the rooted-tree bridge are mathematical,
not an end-to-end Lean proof of the split tableau chart.
