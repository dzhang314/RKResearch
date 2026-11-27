# The final two shift-two weighted order-nine branches

From `ai-generated/lean`, use a Lean executable for the release to test:

    lean -j1 RKCert/Research/FiveSixGate.lean
    lean -j1 RKCert/Research/OneOffShiftTwoGate.lean

These core-only proofs checked on Lean 4.34.1, 4.35.0, 4.36.0, and
4.37.0-rc1. They formalize arithmetic and physical gate lemmas for the
[five-off/six-clean](../../../research/WEIGHTED-ORDER-NINE-FIVE-OFF-SIX-CLEAN.md)
and [single-off](../../../research/WEIGHTED-ORDER-NINE-SINGLE-OFF.md)
cases. The weighted rooted-tree reductions and census are mathematical
proofs, not part of the kernel certificate. Together with the earlier
branches they give the shift-two weighted lower bound of 13 over
characteristic-zero fields, without an ordering assumption. They do not
raise the ordinary ERK order-eleven floor.
