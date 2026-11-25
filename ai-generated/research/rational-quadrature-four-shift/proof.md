# Four shifted moments force 17 rational contributing sites at order 20

**Theorem.** Let \(K\) be a characteristic-zero field. Let a finite
quadrature rule with nodes \(x_i\in K\) and arbitrary weights \(b_i\in K\)
satisfy
\[
  \sum_i b_i x_i^k=\frac{1}{k+1}\qquad(0\le k<p).
\]
Group repeated nodes first and discard a site precisely when its
aggregate weight is zero. If each remaining site is in the image of
\(\mathbb{Q}\to K\), their number \(m\) satisfies
\[
  m\ \ge\ \min(17,p-3)\qquad(p\ge4).
\]
In particular \(m\ge16\) at order 19 and \(m\ge17\) at order 20.
No order on \(K\), positive weights, rational weights, or rationality
of any discarded site is required. These are support lower bounds,
not existence or minimum-stage claims.

**Runge–Kutta consequence.** The reviewed bushy-tree identities
(`HasOrder.hasQuadratureOrder`) give the displayed law at the actual
abscissae \(A\mathbf 1\). The same support bound follows, without a
triangularity or diagonal assumption. It does not alter the separate
unrestricted stage minima. The proof below is mathematical, with exact
arithmetic reproduction; no Lean certificate for this new bound is
claimed.

## 1. Four rational equations from the actual support

Suppose \(m\le16\) and \(m+4\le p\). Write the distinct contributing
sites as \(r_i/v_i\), with \(v_i>0\) and \(\gcd(r_i,v_i)=1\).
Use the integer nodal polynomial
\[
 P(X)=\prod_{i=1}^m(v_iX-r_i)=\sum_k a_kX^k,\qquad a_k=0
 \ \text{for }k>m.
\]
For \(j=0,1,2,3\), the order pays for \(X^jP(X)\). Its weighted
sum is zero: it vanishes at each contributing site, and the
remaining terms have zero *aggregate* weight. Expanding by
linearity gives the rational identities
\[
  \sum_{k=0}^m\frac{a_k}{k+j+1}=0. \tag{1}
\]
The sum first vanishes in \(K\); it is rational and descends by
injectivity of the rational cast. The weights have disappeared
before any modular reduction. Indeed \(m<\min(17,p-3)\) implies
the two assumptions of this contradiction, even if \(p>20\).

Let \(t\) count the odd \(v_i\), and \(u\) count the even \(r_i\)
among these \(t\) factors. Reflection \(x\mapsto1-x\) preserves
the paid moment law, since the rational integral of \((1-X)^k\)
over \([0,1]\) is \(1/(k+1)\). This is an identity of rational
moments, not an ordering on \(K\). Reflection replaces \(r_i\)
by \(v_i-r_i\), without changing the reduced denominator. It
exchanges \(u\) and \(t-u\) and preserves all assumptions. We can
therefore take \(0\le u\le t\le16\) and \(2u\ge t\).

Primitivity of each factor gives
\[
 P(X)\equiv X^u(X+1)^{t-u}\pmod 2,\qquad
 2^{D_{t,u}(k)}\mid a_k,\quad D_{t,u}(k)=\max(0,u-k,k-t). \tag{2}
\]
For the parity, factors with even denominator are the constant
\(1\) modulo 2. For the divisibility, each term in \(a_k\)
uses \(k\) leading terms. If \(k>t\), at least \(k-t\) are
even denominators. If \(k<u\), at least \(u-k\) of the even
numerator factors supply their constant terms. This also holds
for the zero coefficients above \(m\).

## 2. Exact small reduction modulo 8

Clear (1) with \(7L\), where \(L=\operatorname{lcm}(1,\ldots,20)
=232792560\). The only nonzero residues of \(7L/d\) modulo 8
are \(4,2,4,1,4\) at \(d=4,8,12,16,20\), respectively.
For \(j=0,1,2,3\) this gives
\[
 4a_{3-j}+2a_{7-j}+4a_{11-j}+a_{15-j}
       +4a_{19-j}\equiv0\pmod 8. \tag{3}
\]
In particular \(a_{15-j}\) is even, and
\(a_{15-j}+2a_{7-j}\equiv0\pmod 4\).
If \(D_{t,u}(15-j)\ge2\), the latter also requires \(a_{7-j}\)
even. Compute these parities by (2): at index \(k\) they are
\(\binom{t-u}{\,k-u\,}\bmod 2\), with out-of-range binomials zero.
Among the 81 oriented \((t,u)\), the necessary tests leave exactly:

| \(t\) | Surviving \(u\) |
|---:|:---|
| 0 | 0 |
| 1 | 1 |
| 2 | 1, 2 |
| 3 | 2, 3 |
| 8 | 8 |
| 9 | 8, 9 |
| 10 | 8, 9, 10 |
| 11 | 8, 9, 10, 11 |
| 16 | 8, 16 |

The following rows of (3) exclude 17 of those 18 cases. The selected
coefficient is odd by (2), with multiplier 4; every other summand
is \(0\bmod 8\) by the divisibility bound.

| Cases | Shift \(j\) | Selected index \(k\) |
|:---|---:|---:|
| \(t=0,1,2,3\) | \(3-t\) | \(t\) |
| \(t=8,9,10\), or \(t=11,\ u\ge9\) | \(11-t\) | \(t\) |
| \((t,u)=(11,8)\) | 1 | 10 |
| \((t,u)=(16,16)\) | 3 | 16 |

The [exact checker](verify-four-shift.py) reproduces the residue
multipliers, the complete finite parity reduction, and each individual
one-term obstruction using only integer arithmetic.

## 3. The balanced case modulo 4

Only \((t,u)=(16,8)\) remains. Then \(m=16\) and all denominators
are odd. Normalize each factor to be monic modulo 4. The eight even
roots are 0 or 2 modulo 4, and the eight odd roots are 1 or 3.
Products of two corrections vanish modulo 4. Hence the normalized
polynomial is
\[
 X^8(X-1)^8+2eX^7(X-1)^8+2oX^8(X-1)^7\pmod4
\]
for some \(e,o\) modulo 2. At degrees 12 and 14 the even-root
correction contributes zero: modulo 2, \(X^7(X-1)^8=X^{15}+X^7\).
The odd-root correction contributes \(2o\) at both degrees.
The base coefficients are \(70\) and \(28\), respectively, so
the degree-12 minus degree-14 coefficient is \(2\bmod4\).
But (3) at \(j=1,3\) forces both original coefficients to be zero
modulo 4: \(a_6,a_4\) are even by (2). Normalization by the odd
leading coefficient preserves their vanishing. This is the final
contradiction. The checker additionally multiplies all 81 factored
mod-4 multisets directly to verify this last difference. \(\square\)
