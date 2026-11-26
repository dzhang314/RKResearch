# A full paid Gram, rather than a sign test, at a single chronological exit

Here degree means tree size minus one, as in the existing paid Beta-surplus proof. Let \(F_j\) be the full actual pure defect span through degree \(j\), and \(E_j\) the actual tree span. Assume all needed integer casts are invertible and the model is separated at the final degree used. No inner product on coefficient-field stage vectors and no ordering of that field is needed.

## Setup: an actual one-head interval

Suppose for \(0\le i\le d\) an actual unit-increment interval has the form
\[
          F_{a+i}=U\oplus w\,\mathcal P_{<h+i}(\mathbf c),\qquad h\ge1.
]
Here \(U\) is invariant under the actual clock multiplier \(C\), and \(w\,\mathcal P_{<s}(\mathbf c)\) means span of \(w,Cw,\ldots,C^{s-1}w\). The notation denotes a direct sum with independent powers modulo \(U\). Suppose the next power at the endpoint is outside the last space. Equivalently there are at least \(h+d+1\) distinct effective clock blocks, where the clock projection of \(w\) is nonzero modulo \(U\). The standard one-head decomposition obtains these premises when all adjacent increments are one and all the clock flags, including the endpoint, remain noninvariant. This note uses the actual interval, not a hypothesized polynomial curve.

Take \(f\in F_e\) with \(e\le a,d\), and write \(D_f\) for componentwise multiplication by \(f\). By the rooted product rule, \(D_f F_a\subseteq F_{a+e}\). It follows that \(D_f U\subseteq U\): decompose any member of \(U\) by single-clock supports. The product from one such support is still supported there. A head polynomial for it must vanish at every other effective clock, numbering at least \(h+d\), whereas its degree is at most \(h+e-1\). It is therefore zero.

Choose a complement to \(U\) **separately on the joint blocks for the diagonals \(C,D_f\)**. No scalar injection of these pairs into the field is needed: their projectors are products of polynomial projectors in the two diagonals. We specify a chronological choice below. Replace \(w\) by its projection to that complement. Its powers represent the same head. Because the complement is stable under both diagonals,
\[
                         D_f w=P(\mathbf c)\odot w
]
for a polynomial of degree at most \(h+e-1\). In fact \(\deg P\le e\). For \(0\le t<h\), \(C^t w\in F_a\), so \(X^tP\) agrees at the effective clock labels with another polynomial of degree at most \(h+e-1\). Increasing \(t\) from 1 to \(h-1\), the previous degree bound keeps \(\deg(X^tP)\le h+e\), strictly below the number of effective labels. Each comparison is therefore a polynomial identity. At \(t=h-1\) it gives the asserted degree bound. In particular \(f_i=P(c_i)\) at every physical coordinate where the complementary \(w_i\ne0\).

## The same exit tests every paid scalar multiplier

In each joint clock/value block, choose physical pivot coordinates for its piece of \(U\) greedily in chronological order. Each other coordinate evaluation on \(U\) is a combination only of its earlier chosen pivots in that block. Our complement consists of vectors zero on the chosen pivots. Projection to it at a nonpivot \(i\) is the row functional \(\lambda_i\) that reads coordinate \(i\) minus the corresponding combination of earlier pivot coordinates. In particular it kills \(U\) and is supported at the same joint block, never after \(i\). This construction also works jointly for a finite family of diagonal multipliers, by using the simultaneous blocks.

For a scalar polynomial mask \(Q\), consider
\[
             z\coloneqq(QP)(\mathbf c)-Q(C)f .
\]
If \(P,Q\) are nonzero and the contrast is paid, separation implies \(z\notin U\): its nonzero nominal polynomial is \(QP\). Take the first physical index \(i\) at which the complementary projection of \(z\) is nonzero, and put \(\xi\coloneqq c_i\). Thus an actual \(u\in U\) agrees with \(z\) at every preceding index. On its joint block, \(z\) is constant, with value \(Q(\xi)(P(\xi)-f_i)\). If that value were zero, its projection there would be zero. Hence \(Q(\xi)\ne0\), \(P(\xi)\ne f_i\) and \(\lambda_i\mathbf1\ne0\). The mismatch forces \(w_i=0\). The chosen complementary head is zero at all pivot indices, so \(\lambda_i\) annihilates its entire clock-power chain and hence \(F_{a+d}\).

Now for **every** scalar polynomial \(R\) with
\[
                        e+\deg Q+\deg R+1\le a+d ,
]
strict chronology gives
\[
 \lambda_i A R(C)z=\lambda_i A R(C)u=0.
]
Indeed their arguments agree before \(i\), \(R(C)u\in U\), and \(AU\subseteq F_{a+1}\) is killed by \(\lambda_i\). The model of this same rooted expression is \(I(RQP)\). Its difference from that polynomial evaluated at the clocks is pure in the paid last flag. Since \(\lambda_i\) sees only the clock \(\xi\) and has nonzero sum,
\[
                         I_\xi(RQP)=0
]
for all such \(R\) at the **same** actual physical \(\xi\), with \(Q(\xi)\ne0\).

In particular take \(Q=X\). If \(a+d\ge 2e+2\), the full set \(\deg R\le e\) is paid. After dilation by the nonzero \(\xi\) these conditions are the weighted Hilbert Gram on \(P\), for weight \(X\), of size \(e+1\). It is nonsingular using factorials through \(2e+2\). Therefore **\(P=0\)**: \(f\) vanishes at the active complementary head. Furthermore \(f\in U\). Indeed its complementary projection is a head vector (since \(f\in F_a\)), and is zero on every joint block where the raw \(f\)-value is zero. But its head support lies entirely on such blocks. This closes by pure rank, not by signing a single scalar integral.

The lemma applies with \(e=2\) through a flat interval ending in degree at least six, and with \(e=3\) when the interval permits three multiplication degrees and ends at least at degree eight. It can also be used when a separately measured head-profile degree is less than \(e\): the admissible \(R\)-budget is governed by the *actual rooted cost* \(e\), not by the reduced scalar degree.
