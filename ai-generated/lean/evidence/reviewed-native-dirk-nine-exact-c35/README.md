# Exact-order follow-on for the ten-stage DIRK witness (c35)

This additive follow-on imports the separately checked DIRK order-nine
stage-minimum core. It proves that the same ten-stage tableau has
exactly classical order nine over the reals and real algebraic numbers,
by disproving the reviewed order-ten condition on the tall tree.

The proof uses the reviewed tall-tree matrix-power and factorial
theorems, the checked cache through order eight, one sparse stage action,
and one weighted quotient. Both polynomial limbs of the numerator
discrepancy are positive on the certified archived root bracket.

The full ZIP contains every core member byte-for-byte; the optional
delta ZIP contains only the members listed in exact-delta-allowlist.txt.
To replay the follow-on, use the predecessor core's pinned c35
dependencies and compile LobattoDIRK109Exact.lean after the core's
source build. Run AuditReviewedLobattoDIRK109.lean to exercise the two
exact witness types and both IsLeast endpoints. No push or human
source edit was made during the checks.
