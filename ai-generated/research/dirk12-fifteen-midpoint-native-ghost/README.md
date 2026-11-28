# Kernel-checked rational ghost block of the optimal fifteen-stage DIRK12 construction

The [standalone Lean module](../../lean/RKCert/ReviewedNative/DIRKOrderTwelveMidpointGhostCore.lean) checks the literal four-stage rational block used in the [real-algebraic order-twelve construction](../dirk12-fifteen-midpoint-real-upper/README.md). The block is normalized by the first nonzero-weight ordinary clock. The kernel checks the four distinct clocks, triangularity, all five positive scalar moments, the first primitive, both weighted transpose identities, and the common nonzero cubic barycentric coefficient.

These are precisely the rational arithmetic identities of this block. This module does **not** certify the full tableau or all rooted conditions. It uses Lean core only and passes on [4.34.1](lean-4.34.1.txt), [4.35.0](lean-4.35.0.txt), [4.36.0](lean-4.36.0.txt), and [4.37.0-rc1](lean-4.37.0-rc1.txt).
