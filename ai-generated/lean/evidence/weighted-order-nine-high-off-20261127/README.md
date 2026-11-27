# Weighted order-nine high-off scalar gates

This core-only file requires no Mathlib. To replay with an installed Lean
toolchain, from `ai-generated/lean` run:

    lean -j1 RKCert/Research/HighOffGate.lean

The certificate normalizes explicitly supplied integer polynomial identities
and checks their exact coefficients in Lean. It invokes neither an external
computer algebra system nor a native oracle when checking them. Run releases
sequentially to avoid peak memory from concurrent reductions. The logs record
passes on 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1.

The mathematical use of these gates is in the
[weighted off-clock note](../../../research/WEIGHTED-ORDER-NINE-HIGH-OFF.md).
The rooted-tree bridge is not part of this Lean certificate.
