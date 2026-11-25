# Rational strict SDIRK at order five

The strongest verified bounds over the rationals are now five to six stages.
The [six-stage construction](order-five-six-stage-splice.md) improves on the
eight-stage tableau preserved below.
The lower bound follows from the [common-rational-diagonal tall-tree
obstruction](../strict-sdirk-rational-common-diagonal/PROOF.md). Whether a
five-stage rational tableau exists remains open.

## An eight-stage tableau

The following are the rows of the lower triangle of \(A\), in order.
The entries above the diagonal are zero.

| Row | Entries |
| --- | --- |
| 1 | \(1\) |
| 2 | \(-1,1\) |
| 3 | \(0,-1,1\) |
| 4 | \(-9/50,-31/50,0,1\) |
| 5 | \(-4/9,1/9,0,0,1\) |
| 6 | \(-1/2,1/2,0,0,0,1\) |
| 7 | \(7/2,-3/10,2/5,2,-18/5,-2,1\) |
| 8 | \(6,9,-1,-60/7,-45/7,5/2,-5/2,1\) |

The common diagonal is \(1\), and the output weights are
$$
\mathbf b=(0,0,1/48,125/336,27/56,5/96,5/96,1/48).
$$
The accompanying [exact checker](check-order-five.py) enumerates the
unordered rooted trees and verifies
\(t!\,\mathbf b\cdot\boldsymbol{\Phi}_t(A)=1\) for all 17 trees of
orders one through five. The order-six tall tree has weight \(-5/24\)
rather than \(1/720\), so the order is exactly five. In fact, all 20
trees of order six fail their order condition in this example. This
is a mathematical certificate, not a Lean or stability claim.

## At least four distinct sites carry quadrature weight

This restriction applies to any order-five RK tableau with rational
abscissae. The tableau need not be triangular, and its weights may be
signed or lie in any characteristic-zero field. At a repeated
abscissa, the relevant quantity is the sum of the weights at that site.

The bushy trees of orders one through five impose the five uniform
quadrature moments. Under the affine change from \([0,1]\) to
\([-1,1]\), the moments of the transformed nodes are those of
the uniform probability law on \([-1,1]\): the odd moments are zero
and the even moment of degree \(j\) is \(1/(j+1)\).
If at most three distinct rational sites carry nonzero aggregate
weight, they can be included in a set of three distinct rational
numbers. The monic cubic with these three roots must have zero
uniform mean, as must its product with \(x\), since both polynomials
vanish at every contributing site. These two equations give the form
$$
P(x)=x^3+a x^2-\tfrac35 x-\tfrac a3.
$$
Let \(r=n/d\) be any root in lowest terms with \(d>0\). The equation
\(3n^2=d^2\) is impossible for coprime \(n,d\): it would force
\(3\mid d\) and then \(3\mid n\). Thus the equation \(P(r)=0\) determines
\(a\), and the other two roots are the roots of
$$
\frac{P(x)}{x-r}=x^2+
\frac{4nd}{5(3n^2-d^2)}x+
\frac{3d^2-5n^2}{5(3n^2-d^2)}.
$$
Its discriminant is
$$
\frac{12(25n^4-22n^2d^2+5d^4)}{25(3n^2-d^2)^2}.
$$
The term in parentheses is \(2\) modulo \(3\) if \(3\nmid d\), and \(1\)
otherwise. Consequently the discriminant has an odd exponent of
\(3\) in its factorization as a rational number. A rational square
has an even exponent at every prime, so the two remaining roots
cannot both be rational. This is the contradiction.

Four sites suffice for the quadrature conditions alone: on \([0,1]\)
take \(0,1/3,4/5,1\) with weights \(5/48,27/56,125/336,1/24\).
The eight-stage tableau above uses the reflection of this quadrature.
