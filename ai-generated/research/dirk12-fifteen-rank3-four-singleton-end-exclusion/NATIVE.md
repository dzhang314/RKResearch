# Portable fixed-grid determinant certificates

The exact mathematical source is split between this four-singleton packet and the [remaining three-singleton packet](../dirk12-fifteen-rank3-three-singleton-end-exclusion/README.md). The two Python checks reconstruct their polynomial matrices from the monomial antiderivative definitions; Python and the analytic proof remain independent of the Lean reduction.

The portable Lean files check explicit **fixed-coefficient** arithmetic, not a complete formal proof from rooted order. The generated files check their ordered-label coverage against all orders of the five split roots, check the asserted matrix dimensions, and kernel-check the nonzero determinants. The four-singleton file checks the two cut minors, the binary degree-three matrix, and two four-by-four quotient multiplication units, independently of the original Python degree-fifteen Macaulay check. The three-singleton file checks all six multiplication units after the separately checked quartic leading guard. There is no native-decision axiom. The source generator rebuilds both literal matrix files from the fixed formulas and makes the arithmetic boundary explicit.

Replay the original independent arithmetic from the research directories. From here, the compiler may be supplied by its absolute path:

    python3 -B check.py
    python3 -B ../dirk12-fifteen-rank3-three-singleton-end-exclusion/check.py
    bash replay-native.sh /path/to/lean

To reproduce the two generated Lean data files and compare them byte for byte:

    d=$(mktemp -d)
    python3 -B generate-lean.py "$d"
    for x in "$d"/*.lean; do
      cmp "$x" "../../lean/RKCert/ReviewedNative/$(basename "$x")"
    done

The reviewed source build order is:

    DIRKOrderTwelveFifteenSingletonUnitCore.lean
    DIRKOrderTwelveFifteenFourSingletonArithmetic.lean
    DIRKOrderTwelveFifteenThreeSingletonArithmetic.lean

Use the native compatibility logs for compiler-specific verification; the analytic stage implications remain the mathematical proofs in the two READMEs.

Both complete 120-grid checks built sequentially on Lean **4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1**. The generated main theorems report only propext on the stable compilers, and propext plus Classical.choice on the release candidate. The module imports Lean core only; no particular Mathlib pairing is required for this fixed arithmetic.
