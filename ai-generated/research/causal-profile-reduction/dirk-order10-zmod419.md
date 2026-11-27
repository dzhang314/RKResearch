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

This is a finite-field endpoint. It does not change the characteristic-
zero or real 11–12 interval, and no lift follows from the finite tableau
alone. The explicit field minimum is 11 by the reviewed generic lower
bound, not by optimization or by reduction of the real method.

The same minimum is 11 over any nonzero commutative unital ring of characteristic 419: map the tableau along the canonical embedding of the prime field. The order identities and triangularity map along it, and the nonzero star defect remains nonzero. The [uniform ring lower bound](../../lean/RKCert/UniformDIRK.lean) also applies to these rings.
