# The paid affine seventeen-stage ERK10 family and a pruning obstruction

The [half-port tableau](../erk10-seventeen-half-port/README.md)
is one corner of a two-parameter affine family. Let
\(\boldsymbol p_0=(0,-56/45,-1/9,-5/72,0,16/9,-8/5)\) be its
seven reverse taps in the order recorded in the construction.
The family varies them by
\[
 \boldsymbol p=\boldsymbol p_0+\lambda\,\boldsymbol e_0
                         +\mu(\boldsymbol e_1+\boldsymbol e_4).
\]
The full forward matrix is affine in \(\lambda,\mu\); its row-sum
clocks and output weights are unchanged. Every coefficient of
the affine matrix belongs to \(\mathbb Z[1/210]\).

The new integer replay verifies **all** 1,205 rooted conditions at
each of the 100 pairs \(0,\ldots,9\) by \(0,\ldots,9\).
After clearing a common coefficient denominator, a condition of
tree size \(n\) is an integer polynomial in \(\lambda,\mu\)
of degree at most \(n-1\) in either variable, since the matrix
occurs once per nonroot edge and the output is fixed.
The ten-point tensor grid therefore proves each integer
polynomial identity. The selected shape with root children
leaf and bush9 gives a cleared residual of \(-1/77760\)
at \((0,0),(1,0),(0,1)\). Since its stage formula is
\(\boldsymbol c\odot A\boldsymbol c^{\odot8}\), the residual
is affine and hence constant. This proves exact order ten
for every parameter pair in any nontrivial commutative
coefficient ring paying \(10!\).

## No terminal deletion by output-only reweighting within this family

For each of the 121 parameter pairs over \(\mathbb F_{11}\), the
matrix of ordinary rooted stage-profile rows through order nine
has rank 17 by exact row elimination. Thus, for that fixed
matrix \(A\), the output weights of an order-nine or stronger
method are uniquely determined. The last weight is
\(7/150=1\) in \(\mathbb F_{11}\).

In the original stage chronology no row reads the last row.
Deleting it and reweighting the first sixteen would therefore
produce, after padding by a final zero weight, a second
order-nine output for the very same \(A\).
Reduction modulo eleven proves this impossible over
\(\mathbb Z[1/210]\) for **all** parameter pairs, or over any
paid coefficient ring carrying a unital map to the prime
field \(\mathbb F_{11}\). This is not a lower bound for
other sixteen-stage tableaux, or a claim about all extension
fields of characteristic eleven.

In particular merely transferring the last weight to the
old clock-one endpoint already fails at size seven:
the difference between its high and old stage values on
\([{\rm bush6}]\) is \(-10/441\), independent of both
parameters. The two values are affine since
\(\boldsymbol\Phi_{[{\rm bush6}]}(A)=A\boldsymbol c^{\odot5}\).
The transferred weight introduces the unit cleared defect
\(+2/45\) in every paid ring.

The only inputs are the adjacent frozen seventeen-stage
packet and exact integer/rational arithmetic:

    python3 -B check_family.py
    sha256sum -c source-sha256.txt
