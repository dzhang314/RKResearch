# An exact eleven-stage order-ten DIRK tableau over F419

The eleven-stage lower bound for order-ten DIRK over fields is attained
over the field of 419 elements. The literal matrix and weights are in
[the independent complete replay](check-dirk10-zmod419.py); entries above
the listed lower-triangular rows are zero. Its four diagonal zeros are
physical stages 1,5,7,11. The physical second row has zero weight, and is
the only row with nonzero cubic stage defect. The weights and lifted
clock values, written as residue integers, are

- b = (357,0,76,25,2,154,52,37,321,220,14);
- c = (0,2,212,219,229,54,49,38,64,241,1).

The checker independently generates every recursively ordered attach
word through ten vertices, quotients sibling order by a recursive sorted
tree encoding, and tests the denominator-cleared Butcher identity for
all 1,205 resulting rooted trees, not just stars and tall trees. The
eleven-vertex star fails: its degree-ten moment is 224, instead of
1/11 = 381, and the cleared output is 369 instead of one. Thus the
order is exactly ten.

This is a finite-field endpoint, and no characteristic-zero lift follows from the finite tableau alone. A [separate exact real-algebraic construction](dirk-order10-eleven-real-algebraic.md) also attains the eleven-stage minimum over the reals. The explicit field minimum is 11 by the reviewed generic lower
bound, not by optimization or by reduction of the real method.

The same minimum is 11 over any nonzero commutative unital ring of characteristic 419: map the tableau along the canonical embedding of the prime field. The order identities and triangularity map along it, and the nonzero star defect remains nonzero. The [uniform ring lower bound](../../lean/RKCert/UniformDIRK.lean) also applies to these rings.

### Higher finite powers

The [exact lift script](check-dirk10-zmod419-lifts.py) and its [replay](dirk-order10-zmod419-lifts.log) extend the eleven-stage result to `Z/(419^k)` for each integer `1 ≤ k ≤ 11`. The script solves a linear correction at each power and directly rechecks all 1,205 original rooted conditions with exact integers. The first failed eleventh-order condition remains nonzero modulo 419, hence its cleared defect is a unit at each listed modulus. Thus the same exact minimum of 11 also holds over every nonzero commutative unital ring of those characteristics by base change. This is a finite list of exact verifications, not an infinite 419-adic lift or a native Lean proof of the higher-power witnesses.
