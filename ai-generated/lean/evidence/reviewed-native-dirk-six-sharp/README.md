# Sharp rational DIRK order six: five physical stages

The exact rational witness is on the Boole grid `(0,1/4,1/2,3/4,1)`, with weights
`(7,32,12,32,7)/90`. Its lower triangular matrix has unequal diagonals, including
zero at the first and last stages and 1/8 at the second: this is a DIRK witness,
not a strict SDIRK witness. The order-seven bush has factorial-scaled weight
`385/384`, so the method's order is exactly six. The witness specializes to
every characteristic-zero field. Combined with the separate existing native
`HasOrder.dirk_order_six_stages_field`, it proves that five is the minimum
number of stages over every such field.

## Proof and checker boundary

`FiniteScaledOrderCheck` is reusable. Given proofs that supplied sparse
functions are the actual matrix–vector and output actions, the theorem checks
the literal reviewed tree recursion on the integer (or other exact ring)
numerators of the tableau. If the coefficient map sends the two normalizing
factors to units, it recovers native `HasOrder` by homogeneity and cancellation.
No human-maintained definitions for trees, order, or matrices are replaced;
no legacy tableau or order bridge is imported.

`BooleDIRK56` clears stage and output denominators by 168 and 90 respectively,
pays all 65 ordered constructor trees through order six by kernel reduction,
and provides the public exact-order and minimum-stage theorems. The independent
`replay.py` derives the same matrix from the archived three-interior-node
quadrature solve, checks all 25 source coefficients and the five weights, and
checks the 37 classical unordered trees through order six. Its reported
order-seven failure is also verified in the Lean theorem.

The source-only delta includes a consumer and pinned-toolchain receipts. No
stability property or result about common diagonals is claimed beyond the
fact that the displayed diagonal is not constant.
