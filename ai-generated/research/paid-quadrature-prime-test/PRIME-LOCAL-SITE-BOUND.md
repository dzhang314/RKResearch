# A prime-local obstruction to smaller quadrature grids

Suppose a quadrature rule with rational nodes integrates all polynomials of degree at most \(p-1\) on \([0,1]\). Its weights may lie in any characteristic-zero field. Let \(\ell\le p\) be prime and suppose that the reduced denominator of every contributing node is prime to \(\ell\). Then the rule requires at least \(\ell\) distinct contributing nodes.

To prove this, group equal nodes and omit those whose grouped weight is zero. If there are \(N<\ell\) remaining nodes, define
\[
 P(x)\coloneqq x^{\ell-1-N}\prod_{i=1}^{N}(x-c_i).
\]
Every node has \(P(c_i)=0\), so exactness implies \(\int_0^1 P(x)\,dx=0\). The leading coefficient of \(P\) is \(1\). Its leading term contributes \(1/\ell\) to the integral, while the other terms have denominators prime to \(\ell\), both before and after integration. Thus the integral is not zero. This proof requires neither positivity nor rational weights.

In particular, seven of the nine orders from 12 to 20 in the [signed reverse construction](../erk-signed-reverse/SHORT-SYMMETRIC-GRIDS.md) already use the minimum possible scalar site count among grids whose denominators are prime to the largest prime at most \(p\). Orders 15 and 16 are the exceptions. The claim concerns the scalar rule and does not bound the number of stages of an arbitrary Runge–Kutta method.

## Two remaining orders on small symmetric grids

For orders 15 and 16 the rule must integrate through degree 14. Use the centered variable \(u=2x-1\); the exact mean of \(u^{2j}\) is \(1/(2j+1)\). Consider symmetric sets of 13 or 14 distinct sites in \([-2,2]\cap D^{-1}\mathbb Z\) for \(D=6,9,12\).

With 13 sites there are six pairs and the origin. The even test polynomial
\[
   u^2\prod_{i=1}^{6}\bigl(u^2-a_i^2/D^2\bigr)
\]
vanishes on all of them. With 14 sites there are seven pairs, and the corresponding even test is
\[
   \prod_{i=1}^{7}\bigl(u^2-a_i^2/D^2\bigr).
\]
In both cases the polynomial is monic of degree 14. For its mean to vanish, the coefficient of \(u^{12}\) must be zero modulo 13: multiply the mean by 13 and note that the denominator of every other moment is prime to 13. This requires \(\sum_i a_i^2\equiv0\pmod {13}\).

The [exact enumeration](check.py) checks every distinct positive numerator set. It verifies the remaining means using integer coefficients and the common moment denominator \(45045\).

| Denominator | 13 sites, tested / after congruence | 14 sites, tested / after congruence |
|---:|---:|---:|
| 6 | 924 / 90 | 792 / 60 |
| 9 | 18,564 / 1,496 | 31,824 / 2,513 |
| 12 | 134,596 / 10,639 | 346,104 / 26,863 |

None of the surviving means is zero. The test allows all weights and does not assume unit differences or that the grid contains an existing donor chart. Other denominators, nonsymmetric grids, and sites outside the interval are not covered.
