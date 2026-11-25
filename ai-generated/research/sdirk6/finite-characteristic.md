# The six-stage exception in characteristic 163

Six stages are necessary for a common-diagonal Runge–Kutta method of order six over any nontrivial commutative coefficient ring. This uniform lower bound is sharp: the [literal tableau](F163.json) has a nonzero common diagonal of 46 over the field with 163 elements. Its order is exactly six. On the order-seven bushy tree, the factorial times the computed weight is 12 rather than 1.

The [Lean certificate](../../lean/RKCert/ReviewedNative/SDIRKSix163.lean) uses the reviewed tree order conditions and the kernel's finite checker. The [independent script](checkF163.py) checks the 37 unordered rooted trees of orders one through six with exact integer residues. The Lean checker covers their 65 ordered representatives.

In characteristic zero a common-diagonal method of order six needs at least seven stages. The [new lower bound](../../lean/RKCert/ReviewedNative/SDIRKSixFourConstantEndpoint.lean) extends seven to any commutative ring where the following product, viewed as a ring element, is nonnilpotent:

```text
3846112 × 198898968576 × 122267206287360000 × 6214370355160790146744320000
```

A nonunit common diagonal also gives seven, irrespective of the product. Over a field a nonzero image of the product is enough. This condition is sufficient, not a classification of the other possible exceptional characteristics. In particular the field of size 163 is a genuine exception, rather than a prime left over only because of a denominator in the proof.
