# Scalar and physical gates for the sharp-prefix ERK11 branch

From `ai-generated/lean`:

    lean -j1 RKCert/Research/ERK11PureTailGate.lean

This core-only proof passed Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1.
The [mathematical argument](../../../research/ERK11-SHARP-PREFIX-PURE-TAIL.md)
excludes the pure-rank-six, nonendpoint final case and gives exact
necessary conditions in the remaining endpoint case. The bridge from
the reviewed tree predicate is a mathematical proof, not a native
Lean theorem here. The ordinary ERK11 interval is unchanged.
