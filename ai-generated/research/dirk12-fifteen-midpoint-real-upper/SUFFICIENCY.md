# Two complementary defect supports suffice for all order-twelve trees

Let \(A,\mathbf b,\mathbf c=A\mathbf1\) be a tableau over a field of characteristic zero or characteristic greater than 12. Let \(C\) be the ordinary clock operator, \(Y=1-C\) its reflected clock operator, and \(N=A^{\mathsf T}\). For a scalar polynomial \(P\) let \(\mathbf W(P)=\mathbf b\odot P(\mathbf y)\), where \(\mathbf y=\mathbf1-\mathbf c\). Let \(\mathcal H\) be the coordinate space of the actual ghosts (indices where \(b_i=0\)).

Assume the following exact low checks.

* The scalar quadrature is exact through degree 11.
* Nested forward spaces \(G_0,\ldots,G_5\) satisfy \(G_0=G_1=G_2=0\) and \(G_3,G_4,G_5\subset\mathcal H\). For \(0\le k\le4\), the true forward primitive defect \(A\mathbf c^k-\mathbf c^{k+1}/(k+1)\) is in \(G_{k+1}\). For \(0\le k\le4\), \(A G_k,C G_k\subseteq G_{k+1}\).
* Nested reverse spaces \(R_0,\ldots,R_5\) satisfy \(R_0=R_1=R_2=0\) and are zero on the ghosts. For \(0\le k\le4\), the true reverse primitive defect \(N\mathbf W(Y^k)-\mathbf W(Y^{k+1})/(k+1)\) belongs to \(R_{k+1}\). Also \(N R_k,Y R_k\subseteq R_{k+1}\) for \(k\le4\). Every \(R_k\) is orthogonal to all scalar vectors of degree at most \(11-k\).
* In the single grade-six bridge, \(A G_5\) and \(A\mathbf c^5-\mathbf c^6/6\) annihilate both \(R_5\) and \(\mathbf W(P_5)\) under the usual coordinate dot product.

Then **every rooted-tree condition through size 12 holds**. No scalar degree-twelve moment, condition on a next defect, or positivity is used.

## Proof

For \(j\le5\), use the forward sufficient flag \(V_j=G_j\). For \(6\le j\le11\) define
\[
             V_j=\operatorname{Ann}\bigl(R_{11-j}+\mathbf W(P_{11-j})\bigr),
\]
where \(P_k\) is the full scalar polynomial space of degree at most \(k\). The spaces \(V_j\) are nested: the only bridge is \(V_5\subset V_6\), which follows because \(V_6\) contains every ghost-coordinate vector. Each \(V_j\) annihilates the output weight: for low grades use ghost support, for high grades test against \(\mathbf W(1)=\mathbf b\).

The maps \(A,C\) raise the forward flag by at most one. For \(j\le4\) this is stipulated; for \(j=5\) use the bridge for \(A\) and preservation of ghost support for \(C\). For \(j\ge6\), test against the generators of \(V_{j+1}^{\perp}\). There are only \(\mathbf W(P_{10-j})\) and \(R_{10-j}\). The true reverse primitive rule sends each scalar test to a scalar test of degree at most \(11-j\) plus its paid reverse defect in \(R_{11-j}\). It also sends \(R_{10-j}\) into \(R_{11-j}\). The ordinary clock action \(C=1-Y\) has the same inclusion by the clock-lift premise. This proves the two adjoint inclusions.

The scalar forward primitive defect at input degree \(k\ge6\), \(k+1\le11\), lies in \(V_{k+1}\). For a test in \(R_{10-k}\), use the reverse inclusion and the two scalar orthogonalities, at degrees \(k\) and \(k+1\). For a scalar test \(\mathbf W(Y^l)\) with \(0\le l\le10-k\), use the true reverse primitive of \(Y^l\) and its defect in \(R_{l+1}\), which is orthogonal to \(\mathbf c^k\) because \(k\le10-l\). The two remaining scalar integrals agree:
\[
      \int_0^1\frac{(1-X)^{l+1}X^k}{l+1}\,dX
       =\int_0^1\frac{(1-X)^l X^{k+1}}{k+1}\,dX.
\]
This is just the zero integral of the derivative of \(X^{k+1}(1-X)^{l+1}/[(k+1)(l+1)]\). Both degrees are at most 11. Their quadratures are therefore identical.

Finally \(V_j\odot V_k\subseteq V_{j+k}\) whenever \(j+k\le11\). If a factor has grade at most two it is zero. Otherwise both grades are at least three and at least one is at most five. The product is then supported on ghosts, and \(V_{j+k}\) contains every such vector, since \(j+k\ge6\). This is the reason no high nonlinear defect matrices need to be checked.

Inducting over a non-plane rooted tree, the elementary stage vector minus its exact scalar power lies in the sufficient forward flag of its grade: handle a primitive by the scalar primitive defect and \(A V_j\) inclusion, then expand products, using scalar powers of \(C\) and the product inclusion. The output kills the flag and the scalar part has exact quadrature. This proves the full rooted-tree criterion (equivalently the hypotheses of the existing generic SufficientGradedFlags theorem after clearing the small integer denominators).

## Verification-friendly grade-six bridge

In a first-Legendre-root midpoint construction the nonterminal parts of the two grade-six bridge images may be checked to be multiples of \(Q_6(X)=X L_6'(X)\), with unrestricted ghost entries. It suffices that their actual output be zero. Indeed \(R_5\) is zero at the literal terminal and all ghosts and annihilates scalar degree six, so it annihilates these bridge vectors. For ordinary scalar \(P\) of degree at most five,
\[
                \int_0^1 Q_6(X)P(X)\,dX=P(1)
\]
by integration by parts and shifted Legendre orthogonality. The degree is at most 11, so actual scalar quadrature gives the same value. The actual terminal correction is determined by the zero output (the terminal has nonzero weight), and cancels the \(P(1)\) evaluation. This verifies the bridge without constructing \(V_7,\ldots,V_{11}\) or enumerating high trees.
