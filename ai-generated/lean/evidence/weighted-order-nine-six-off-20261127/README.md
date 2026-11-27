# Shift-two weighted ERK9: two six-off-clock cases

From `ai-generated/lean`, using the Lean toolchain to test:

    lean -j1 RKCert/Research/SixOffFiveGate.lean
    lean -j1 RKCert/Research/SixOffSixGate.lean

The core-only modules check the scalar gates, plus the terminal uniqueness
and off-aggregate contradiction in the five-clean-clock case. Both passed
4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The mathematical reductions from the
weighted tree equations are in the
[five-clean](../../../research/WEIGHTED-ORDER-NINE-SIX-OFF-FIVE-CLEAN.md)
and [six-clean](../../../research/WEIGHTED-ORDER-NINE-SIX-OFF-SIX-CLEAN.md)
notes. The unrestricted ordinary order-eleven stage bound is unchanged.
