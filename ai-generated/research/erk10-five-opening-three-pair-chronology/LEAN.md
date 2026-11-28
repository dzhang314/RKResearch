# Portable scalar checks for free chronology and blind rows

The core module
[ERK10ThreePairChronologyScalars.lean](../../lean/RKCert/ReviewedNative/ERK10ThreePairChronologyScalars.lean)
checks the free second-target determinant, null-kernel exit, opposite-pair
column difference, and ghost-blind two-tap elimination. No Mathlib is
imported. Its standard-axiom endpoints passed Lean 4.34.1, 4.35.0,
4.36.0 and 4.37.0-rc1. The rank and physical chronology reduction is
mathematical.

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10ThreePairChronologyScalars.lean
    sha256sum -c ai-generated/research/erk10-five-opening-three-pair-chronology/lean-checked.sha256
