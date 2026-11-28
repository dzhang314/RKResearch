# Core Lean arithmetic for the two DIRK12 Radau pencil gcds

This is a portable companion to the [frozen exact pencil proof](../dirk12-fifteen-nonC2-visible-local-exclusion/README.md), not an end-to-end new stage theorem. It uses only Lean core. It checks the cleared shifted Jacobi moments, the possible prime divisors up through 31, preservation of the original degrees and top coefficients modulo 1009, and a linked Euclidean remainder proof for each of three pairs: the expanded degree-40 determinant pair, the expanded degree-60 determinant pair, and the consecutive Jacobi generators (degrees 5 and 6). Each trace checks all coefficient identities, strict drops, and the terminal nonzero constant. The two large proofs are sharded at each explicit quotient, using proof-producing reduction without a native axiom.

The Lean module consumes the expanded coefficient vectors. Their derivation from the actual integrated exterior matrices is checked by the independent exact Python/Node replays in the companion, not by this Lean module. The continued modular check at 1013 is also in that companion. The mathematical reduction from actual rooted equality to the Radau pencil uses the separately preserved native equality-frame and reverse-rank pieces and the mathematical arguments documented there. No unrestricted 15-stage exclusion follows.

    python3 -B generate-lean.py /tmp/DIRKOrderTwelveFifteenRadauPencilArithmetic.lean
    cmp /tmp/DIRKOrderTwelveFifteenRadauPencilArithmetic.lean \
        ../../lean/RKCert/ReviewedNative/DIRKOrderTwelveFifteenRadauPencilArithmetic.lean
    lean ../../lean/RKCert/ReviewedNative/DIRKOrderTwelveFifteenRadauPencilArithmetic.lean
    sha256sum -c sources.sha256
