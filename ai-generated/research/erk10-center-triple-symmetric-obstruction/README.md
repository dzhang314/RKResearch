# A rational obstruction in the centered triple ERK10 splice

This excludes a specific six-opening, ten-high-row construction over
\(\mathbb Q\), not all width-sixteen order-ten ERK methods. It does not
address asymmetric quadrature or different reverse defect balances.
This is an exact mathematical argument with an arithmetic replay, not
a Lean theorem.

## The chart

Use the six-row cubic opening decoder \(\Pi\) as in the
[order-nine triple method](../erk9-fourteen-rational-triple/README.md).
It is exact on rooted stage profiles through size four. Put
\(\rho_\tau(X)=|\tau|X^{|\tau|-1}/\tau!-\Pi\boldsymbol{\Phi}_\tau(A_{\rm old})\).
All these sources vanish at zero. The size-five sources span a
three-dimensional subspace of \(X\mathcal P_3\), where \(\mathcal P_d\)
is the space of polynomials of degree at most \(d\). No particular
choice of this subspace is required.

The ten raw reverse sites in causal order are
\[
  1,\quad A,\quad A,\quad T,\quad A,\quad B,\quad C,\quad D,\quad E,\quad F,
  \qquad A=2/3,\quad T=1/2.
\]
These capital letters are scalar labels. The nine distinct scalar
sites are these labels after deduplication, together with zero. They
are symmetric about \(1/2\), and each has a nonzero cardinal-integration
mass \(w_x\). Cardinal interpolation and symmetry of the odd nine-root
hull give scalar exactness through degree nine. The raw weights at
\(A\) split as \((3,-3,1)w_A\), and the old origin takes the mass at zero.

Use normalized reverse matrix \(L\); its physical weighted transpose
in reverse order is the high block \(M\). The forward cross block is
\((\mathcal E J-M\mathcal E)\Pi\), with \(\mathcal E\) evaluation at the
high clocks and \(J\) integration from zero. Set
\(\boldsymbol y=\boldsymbol 1-\boldsymbol x\), \(a=1-A=1/3\), and
\(t=1-T=3a/2\). Impose
\[
 \begin{split}
 L\boldsymbol 1&=\boldsymbol y,\qquad
 \boldsymbol u=L\boldsymbol y-\boldsymbol y^{\odot2}/2,\qquad
 \boldsymbol g=L\boldsymbol y^{\odot2}-\boldsymbol y^{\odot3}/3,\\
 \boldsymbol h&=L\boldsymbol u,\qquad
 \boldsymbol v=\boldsymbol g/2+\boldsymbol h,\qquad
 \boldsymbol k=L\boldsymbol y^{\odot3}-\boldsymbol y^{\odot4}/4,\qquad
 \boldsymbol r=L\boldsymbol v .
 \end{split}
\]
As in the order-nine base, the second raw occurrence of \(A\) taps the
first by \(a\). The vectors \(\boldsymbol u,\boldsymbol g,\boldsymbol h\)
are zero at singleton sites and have zero weighted aggregate at \(A\).
A bar denotes the per-site weighted average. The order-ten chart asks
\(\overline{k},\overline{r}\) to kill the five scalar tests
\(X,\ldots,X^5\) under the scalar weights. This is an assumption of
the chart, not a claim about arbitrary order-ten tableaux.

## Early scalar constraints

Put \(S=\{A,T,B,C,D,E,F\}\) and
\(\nu_x=1/(x\prod_{z\in S,\ z\ne x}(x-z))\).
The five tests force \(w_x\overline{k}(x)/\nu_x\) and
\(w_x\overline{r}(x)/\nu_x\) to be affine in \(x\) on \(S\):
each lies in the two-dimensional null space, and affine multiples
of the displayed cofactor span that space. Both defects vanish at
the raw origin \(1\).

The first grouped rows at \(A,T,B\) see only the donor ordinates
\(0,a,t\), including the effect of the split at \(A\). Interpolating
\(Y^3\) on those donors and paying the first three primitives gives
\[
   \overline{k}(x)=\kappa(1-x),\qquad
   \kappa(Y)=-Y^2(3Y^2-10aY+9a^2)/12 .
\]
The other two early values are \(\overline r(A)=-5a^4/36\) and
\(\overline r(T)=-a^2t^2/12\). Indeed \(v=-a^3/6\) at both first
occurrences of \(A\) and \(v=0\) at the third. The taps from \(T\)
to the first two copies sum to \(t^2/(2a)\), and the corresponding
sum from the third copy is \(23a/6\).

At centered site \(z=2x-1\), the quotient \(w_x/\nu_x\) is proportional,
by a constant independent of \(x\), to
\[
   \frac{1}{z-1}\,\mathcal I\left(\prod_{v\ne z}(Z-v)\right),
   \qquad
   \mathcal I(Z^j)=
   \begin{cases}1/(j+1)&j\text{ even},\\0&j\text{ odd}.\end{cases}
\]
The product runs over all the centered sites, giving an exact
collinearity equation for the first three cubic cofactor values.

If \(B=1/3\), let the other centered pairs be \(\pm u,\pm v\).
Collinearity requires
\[
       v^2=\frac{21u^2-11}{21(3u^2-1)} .
\]
If \(u\) is 7-integral, the numerator and \(3u^2-1\) are 7-adic
units, because \(3^{-1}=5\) is not a square modulo 7. The right
side has odd valuation \(-1\). If \(u\) is not 7-integral, both
leading terms dominate, and their quotient is a unit with
nonsquare residue \(5\). Neither case gives a rational square.

Otherwise call the signed centered coordinate of \(B\) \(u\);
the remaining four labels have centers \(-1/3,-u,v,-v\).
Collinearity is then \((3u+8)v^2=4-u\), so every rational mesh in
this subchart must have \(u=(4-8v^2)/(1+3v^2)\).

## A necessary terminal determinant

Let \(U(Y)=Y(Y-a)(Y-t)(Y-(1-B))\), \(I_k=\kappa+U/4\), and let
\(I_r\) be the cubic interpolant of \(\overline r\) at ordinates
\(0,a,t,1-B\). For \(f\in X\mathcal P_3\), define
\[
 \boldsymbol\Lambda(f)=\int_0^1 f(x)\int_0^{1-x}
            \bigl(-U(y),\,I_k(y),\,I_r(y)\bigr)\,dy\,dx .
\]
If each later row uses just those four starter sites, this is the
weighted triple of responses on \(f\) from
\(L\boldsymbol y^{\odot4}-\boldsymbol y^{\odot5}/5,\,
  L\boldsymbol k,\,L\boldsymbol r\).
Interpolating a donor load on the four sites reduces to the first
four reverse primitives plus a multiple of \(\overline k\), which
the five tests remove. Any difference of an actual profile from
its grouped version on the triple lies in the span of
\(\boldsymbol u,\boldsymbol v\); under \(L\) it pairs to zero on
these tests by the same balances. Scalar integration is exact at
the resulting degrees.

Through order ten there is at most one propagated source of size
five or more at any tree vertex. The high-edge source
correction is \(M\mathcal E\rho-\mathcal E J\rho\); further parents
or leaf siblings propagate it by a matrix action or a clock
multiplication. The transpose gives reverse words in \(L,Y\),
where \(Y\) denotes multiplication by \(\boldsymbol y\).
Sources of size six or more cancel: at length at most three
the words and the extra \(L\) in the edge correction yield
only balanced \(\boldsymbol u,\boldsymbol g,\boldsymbol h\)
or the five paid tests on \(\boldsymbol k,\boldsymbol r\).
For size-five sources, words \(Y^4,LY^3,L^3Y\) on
\(\boldsymbol 1\) give respectively the powers \(y^4\),
\(y^4/4+k\), and \(y^4/24+k/6+r\) componentwise. Comparing the
next reverse action and the primitive term removes the ideal
powers and the paid \(k,r\) moments, forcing all three actual
response moments above to annihilate the size-five sources.
These words are realized by four extra parents or leaf
siblings, with \(Y=1-X\) a linear combination. The response map
on four-dimensional \(X\mathcal P_3\) therefore has rank at most one.

The additional site \(C\) has no grouped free tap: four donor
moments determine its four taps. At \(D\) the lone extra tap
changes the triple by a multiple of
\[
 \boldsymbol\Delta(C)=
    (U(1-C),\ \overline k(C)-I_k(1-C),\
               \overline r(C)-I_r(1-C)).
\]
With \(f_4=X(X-D)(X-E)(X-F)\) and \(f_3=X(X-E)(X-F)\), the
rows at \(E,F\) disappear in both tests, and the first test also
removes the row at \(D\). The rank bound requires
\[
 \det(\boldsymbol\Lambda(f_4),\boldsymbol\Lambda(f_3),
                        \boldsymbol\Delta(C))=0 .
\]

## Exact replay

For each of the 12 choices of \((C,D)\), the remaining order of
\(E,F\) does not enter the determinant. Its numerator in \(v\)
has rational roots only among \(-1,0,1,\pm1/3\); these all cause
site collisions. The program checks the exact factorization
and, for each nonlinear factor, exhibits a prime not dividing
its leading coefficient at which it has no root. A rational
root would have denominator prime to that prime and would give
a residue root. This is not a bounded search over node heights.
The program also derives both early collinearity equations.
SymPy is used for exact polynomial arithmetic only.

    python3 -B audit.py
    sha256sum -c sha256.txt
