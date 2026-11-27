# Nine strict stages attain exact order seven over F19

The literal nine-stage tableau in this directory has common diagonal **8** in F19 and can be reconstructed from normalized reciprocal diagonal **12**, helper spacing **14** (helper clocks 1,15,0) and six normalized active clocks **5,17,13,6,18,11**. The first three weights are zero and the six active weights are **3,13,15,3,13,11**. All 85 unordered rooted conditions through order seven hold in F19. The eighth bush has factorial-scaled value 12, so the order is exact.

Together with the independent eight-stage exclusion in the [F19 lower proof](../strict-sdirk7-eight-stage-face/README.md), this gives minimum **nine** over the prime field F19. The lower proof's native and mathematical/exhaustive components remain distinct. This finite tableau alone makes no assertion about lifting to Z/19², to Z[1/5040], to characteristic zero, or about other finite fields.

The construction is not a random matrix search. It uses the three-helper/six-tail linear chart, applying the two Laguerre annihilator tests to the first three reflected clocks and the necessary penultimate bridge to obtain a small shortlist. The generic fourth reflected clock is then 2u−1. The exact interpolation and tail primitive-action linear equations recover the remaining coefficients. At this solution the reflected clocks are 7,14,18,6,13,1, and the row bC B of the six-stage tail model is 3,15,17,13,12,7. No aspect of the chart is assumed by the final rooted check.

- SDIRKNineStageOrderSevenF19.lean verifies the literal matrix with the reviewed HasOrder predicate and proves exactness.
- Run python3 construct-nine-stage-f19.py to replay the small modular linear solve.
- Run python3 check-nine-stage-f19.py for verification independent of the construction.
