# A scalar barrier to the four-read eight-opening ERK10 splice

This excludes a specific exact reverse construction for width sixteen.
It is not a general stage lower bound, nor does it assume or assert
that every order-ten tableau has the reverse constraints below.
The argument is over a field in which \(10!\ne0\), so it applies
in characteristic zero and every prime characteristic above seven,
including all extension fields of such characteristics. It uses
no ordering. Its algebra is checked by the supplied exact replay,
not by Lean.

## Scope and normalization

An [eight-stage dense order-five prefix](../erk-continuous-five-eight/README.md)
has a literal pure endpoint at one. Scaling its clocks by a
nonzero alias clock \(\xi\) scales the size-six source subspace to
\(X(X-\xi)\mathcal P_3\), where \(\mathcal P_d\) means degree at most \(d\).
This suggests a nine-row raw reverse block, with its final reverse
row at \(\xi\) folded into that actual prefix endpoint. The total
physical count would be \(8+9-1=16\).

Here are the assumptions of the reverse chart. Its clocks are
\(x_0=1,x_1,\ldots,x_7,x_8=\xi\), in reverse causal order.
The eight nonorigin clocks \(x_1,\ldots,x_8\) are pairwise distinct,
are nonzero, and \(x_1,\ldots,x_7\ne1\). The final clock may equal
one; that is the only permitted repeated clock. All weights in
rows 0 through 7 are nonzero; the weight at the last raw row
is also nonzero if \(\xi\ne1\). Together with the old scalar
mass at zero, these masses have precision nine. All matrices
are strictly lower triangular in this reverse order.

Write \(\boldsymbol y=\boldsymbol 1-\boldsymbol x\),
\(\boldsymbol M_j=\boldsymbol w\odot\boldsymbol y^{\odot j}\) and use the
 raw weighted transpose \(K\).
Require the following four-read compression:
\[
 \begin{split}
 K\boldsymbol w&=\boldsymbol M_1,\qquad
 \boldsymbol U=K\boldsymbol M_1-\boldsymbol M_2/2,\\
 \boldsymbol G&=K\boldsymbol M_2-\boldsymbol M_3/3,\qquad
 \boldsymbol H=K\boldsymbol U,\\
 \boldsymbol G,\boldsymbol H&\in
       \operatorname{span}\{\boldsymbol U,\boldsymbol x\odot\boldsymbol U\}.
 \end{split}
\]
The cofactor \(\boldsymbol U\) pays \(X,\ldots,X^7\).
The terminal responses
\(\boldsymbol k=K\boldsymbol M_3-\boldsymbol M_4/4\) and
\(\boldsymbol R=K(\boldsymbol y\odot\boldsymbol U)\)
pay \(X(X-\xi)\mathcal P_3\). Using \(K(\boldsymbol x\odot\boldsymbol U)\)
instead of \(\boldsymbol R\) gives identical tests because their
sum is \(\boldsymbol H\), which already pays those tests.
These assumptions describe a specific coefficient construction.

At the reverse origin, all the displayed errors are zero. Since
\(U_1=-w_1y_1^2/2\ne0\), the eight active coordinates of
\(\boldsymbol U\) are all nonzero and proportional to the single
cofactor \(1/(x_i\prod_{j\ne i,\ 1\le j\le8}(x_i-x_j))\).
The terminal tests ignore the origin and the alias row. Their
remaining seven-site null space is proportional to that same
cofactor times an arbitrary quadratic. Hence \(k_i/U_i\) and
\(R_i/U_i\) are quadratic functions of the seven remaining
clock values.

On those live weighted rows set \(L_{ij}=K_{ij}w_j/w_i\).
Scale \(L\) and the ordinates by \(y_1^{-1}\), and scale the
normalized defect \(U_i/w_i\) by \(y_1^{-2}\). The resulting
first four nonorigin ordinates are \(1,q,r,s\), all distinct
and nonzero. Write their defects as
\(-1/2,-1/(2u),-1/(2v),-1/(2z)\) respectively, with
\(u,v,z\ne0\). This scaling neither changes a polynomial
degree test nor the compressed span.

## Three-row equation and its exceptional coefficient

The first row after the origin taps only ordinate zero. The
second nonorigin row's tap to ordinate one is \(q^2/2+d(q)\),
where \(d\) denotes the scaled normalized defect. These two
rows determine the affine ratios \(G_i/U_i,H_i/U_i\).
On the third off row at \(r\) the taps to \(1,q\) are
determined by \(L\boldsymbol y\) and \(L\boldsymbol y^{\odot2}\).
Substituting them into \(L\boldsymbol d\) gives \(N+Cv=0\), with
\[
 \begin{split}
 N&=q^4(r-1)u^2+
       q(q+2r+q^2-6qr+2q^2r)u+r-q,\\
 D_0&=q(3q-2r)u+2r-3,\qquad C=r^2(1-q)D_0.
 \end{split}
\]
No solution has \(C=0\). If \(3q-2r=0\), then
\(D_0=3(q-1)\ne0\). Otherwise \(D_0=0\) would give
\(u=(3-2r)/(q(3q-2r))\), where \(N\) is
\[
             -12r(q-1)^2(q-r)(r-1)/(3q-2r)^2\ne0 .
\]
Thus \(v=-N/C\) and \(N\ne0\).

## Fourth-row elimination

Interpolate \(d\) on the first four donors \(0,1,q,r\)
by \(d(Y)=aY+bY^2+cY^3\). To have an invertible four-read
moment matrix one needs \(c\ne0\). The actual interpolation gives
\[
  c=-\frac{(qu-1)(q^2u-1)^2}{2qu(q-1)N}.
\]

For the first four off rows all their earlier taps are on those
four donors. Suppose \(c\ne0\). Eliminate \(L\boldsymbol y^{\odot3}\)
using \(cL\boldsymbol y^{\odot3}
=L\boldsymbol d-aL\boldsymbol y-bL\boldsymbol y^{\odot2}\).
For \(L(\boldsymbol y\odot\boldsymbol d)\) also reduce \(Y^4\)
by the donor hull \(Y(Y-1)(Y-q)(Y-r)\). This expresses the two
terminal ratio tests, after dropping affine terms, as requiring
the following divided differences on \(1,q,r,s\) to vanish:
\[
 \begin{array}{ll}
 T_K(Y)=-cY^4/4-aY^2/2-bY^3/3,\\[2pt]
 T_R(Y)=[c^2qr-a(b+c(1+q+r))]Y^2/2\\
 \hphantom{T_R(Y)=}+
      [c(a-c(q+r+qr))-b(b+c(1+q+r))]Y^3/3.
 \end{array}
\]
Precisely the load values for \(T\) are
\(T(1),uT(q),vT(r),zT(s)\). Each divided difference has
form \(A+Bz\). Eliminating \(z\) yields the exact identity
\[
  A_K B_R-B_K A_R
     =-\frac{s^2(qu-1)^2(q^2u-1)^5}
              {32 q^2u^2(q-1)^2(q-s)(s-1)D_0 N^2}.
\]
All displayed denominators are nonzero by the preceding step,
distinctness, and the paid characteristic. It follows that
\(qu=1\) or \(q^2u=1\), contradicting \(c\ne0\).
All rational-function identities here are polynomial identities
after clearing the displayed denominators, whose scalar factors
are powers of two and three. Thus no extra characteristic
exception is hidden by symbolic reduction over \(\mathbb Q\).

## Both singular alternatives

If \(c=0\), the same pivot identity explicitly forces
\(u=1/q\) or \(u=1/q^2\). The corresponding third values are
\(v=1/r\) and \(v=1/r^2\).
Thus the first three off defects satisfy \(d=-Y/2\), or all
satisfy \(d=-Y^2/2\).

In the linear alternative the affine ratio \(H/U\), fixed by
the first two off rows, is \((Y-1)/2\) in scaled coordinates.
Reading \(\boldsymbol d=-\boldsymbol y/2\) on predecessors gives
\(Ld=-(Y^2/2+d)/2\). At each later nonzero ordinate the equality
\(Ld=d(Y-1)/2\) forces \(d=-Y/2\) again.

In the quadratic alternative the first two off rows yield
\(G/U=2Y/3\) and \(H/U=0\). If all predecessors have
\(d=-Y^2/2\), then \(Ld=-L(Y^2)/2=0\); the cubic action
is \(L(Y^2)=Y^3/3+2Yd/3\). For a nonzero ordinate this forces
\(d=-Y^2/2\) again. These inductions cover all rows with nonzero
ordinate. The possible final repeated clock one is irrelevant
in the test \(X-X^2\).

Returning to unscaled coordinates, the two possibilities
give, respectively, \(U_i=-(y_1/2)w_i(1-x_i)\)
or \(U_i=-w_i(1-x_i)^2/2\) on all nonorigin sites that
contribute to \(X-X^2\). Its weighted sum against \(\boldsymbol U\)
must be zero. By the scalar quadrature, it is instead
\(-y_1/24\) or \(-1/40\), both nonzero in any paid field.
This excludes the singular cases and closes the stated chart.

## Reproduce

    python3 -B audit.py
    sha256sum -c sha256.txt

The replay verifies the first-three equation, its exceptional
case, the two exact pivot roots, the four-row elimination and
the final scalar integrals. SymPy uses exact rational arithmetic.
This conclusion leaves open different reverse entrances,
more than two compression directions, or an eight-stage
prefix with smaller size-six residual space.
