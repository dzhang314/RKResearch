# A cubic-profile zero pivot needs three later active clocks

**Local theorem (any field with the paid order-ten denominators).**
Let \(v\) be an actual grade-at-most-three stage column of an order-ten
DIRK, with scalar polynomial profile \(P(x)=a x+b x^2+c x^3\ne0\).
Suppose \(v\) is zero strictly before stage \(i\) and \(a_{ii}=0\).
There must be at least three distinct clock values among the
**individually nonzero output weights strictly after** \(i\).
Neither positivity nor distinct physical stages at different clocks is
assumed. A zero diagonal at the debut follows automatically if
\(v\in\ker(CA-AC-A^2)\).

**Proof.** If there were at most two such clock values, take a monic
quadratic \(H(x)=x^2+\ell x+h\) vanishing on them (use an arbitrary
additional linear factor if necessary). For every \(j\),
\(A C^j v\) vanishes through \(i\), including that row. Hence
\(b^\mathsf{T}H(C)C^k A C^j v=0\). This **literal rooted** test is
paid for \(j+k\le3\): the grade is at most \(3+j+1+k+2\le9\).
Writing \(I(x^m)=1/(m+1)\) and \(M_r=I(Hx^r)\), its scalar value is
\[
\sum_{d=1}^3 \frac{p_d M_{j+k+d+1}}{j+d+1}=0,
\qquad (p_1,p_2,p_3)=(a,b,c).
\]
For \(t=j+k=2,3\), use \(j=0,1,2\). Clearing rows by \(12,60,60\)
gives the same integer matrix
\[
  \begin{pmatrix}6&4&3\\20&15&12\\15&12&10\end{pmatrix}
\]
whose determinant is 1. It separately annihilates
\(aM_{t+2},bM_{t+3},cM_{t+4}\).
With at least two nonzero coefficients the resulting overlapping
pairs force three consecutive zero moments starting at 4 or 5.
If precisely one coefficient is nonzero, instead take \(j=0\),
\(t=0,1,2\): three consecutive moments vanish starting at 2, 3 or 4.

For each start \(e=2,3,4,5\), the vector of these three moments equals
\((1/(e+i+j+1))_{0\le i,j<3}(h,\ell,1)^\mathsf{T}\), which cannot
vanish. For direct certificates the last rows of the four inverse
matrices are respectively
\((630,-2100,1575)\), \((1680,-5040,3528)\),
\((3780,-10584,7056)\), and \((7560,-20160,12960)\).
The largest denominator is 10. This proves the result over any field
in which the order-ten conditions can hold.

**Application to the eleven-stage face, with dependencies explicit.**
Use the prior equality-branch information \(Ac=c^2/2\),
\(\dim E_3\ge5\), \(\dim F_5\le3\), and the Volterra inclusion
\(RE_3\subseteq F_5\). The first two dimension bounds in combination
with the inclusion give \(\dim(E_3\cap\ker R)\ge2\).
The constant vector is in this kernel by C(2). Subtract a constant
from an independent kernel vector to get a nonzero \(v\in E_3\) with
zero origin value. At C(2), the only extra grade-three direction
besides clock cubics is \(g=Ac^2-c^3/3\) (expand the grade-three trees).
The scalar profile of \(v\) has zero constant. It is not identically
zero: at the first nonzero clock \(u\), C(2) makes its diagonal \(u/2\),
so \(g_i=u^3/6\ne0\); every preceding \(g\) entry vanishes. Thus a
nonzero scalar multiple of \(g\) cannot be in \(\ker R\), by the diagonal
pivot there. By the local theorem, the first nonzero coordinate of
\(v\) is an interior zero diagonal, occurs no later than stage eight
(numbering 1–11), and leaves three distinct individually active clock
labels still to come. The [bridge test](zero-diagonal-volterra-bridges.md)
also forbids a marked start at that coordinate. This restricts the
chronology; it does not exclude an eleven-stage method.

**Lean scope.** [DIRKCubicZeroPivotMask.lean](../../lean/RKCert/ReviewedNative/DIRKCubicZeroPivotMask.lean)
checks the complete scalar contradiction `no_two_clock_mask`, assuming
the displayed paid moments and mixed tests, on Lean 4.34.1, 4.35.0,
4.36.0 and 4.37.0-rc1. The RK-to-tests implication and equality-profile
rank bookkeeping above are mathematical deductions, not new top-level
`HasOrder` theorems in that file.
