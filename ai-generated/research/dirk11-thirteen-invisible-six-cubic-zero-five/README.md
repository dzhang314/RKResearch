# Five initial ghosts excluded in the zero-multiplier cubic DIRK11/13 chart

**Result.** In the normalized invisible-six DIRK11/13 chart with cubic
\(U\), no ghost before the fourth reverse ordinary stage, and zero
reciprocal clean multiplier \(\tau\), the profile
\((\alpha,\beta,\gamma)=(0,1,5)\) is impossible. The same proof gives a
necessary zero fourth reverse ordinary diagonal and an exact
degree-24 ordinary-clock projection for all three surviving
\(\alpha=0,\tau=0\) cubic count profiles. No unrestricted numerical
bound changes: the real DIRK11 interval remains **13–14**.

The hypotheses are the actual signed normalized chart of the
[invisible-six paid](../dirk11-thirteen-invisible-six-paid/README.md),
[forward count](../dirk11-thirteen-invisible-six-prefix/README.md),
and [constant closure](../dirk11-thirteen-invisible-six-constant-exclusion/README.md)
packets: thirteen literal lower-triangular stages, true rooted order
eleven, \(C(2)\), genuine reflected \(D(1),D(2)\), grade-six
surplus, six zero-weight live cubic-dirty rows at distinct clocks,
and seven clean stages at distinct clocks, including the literal
endpoints. All five ordinary nonendpoint weights are live. Once
these signed shape and rank hypotheses hold, the proof applies
over every characteristic-zero field, without ordering or positivity.

## 1. A real cutoff in the genuine reverse rows

Write \(Y=\operatorname{diag}(1-c)\), \(N=A^{\mathsf T}\) in
literal reverse order, \(W(P)=bP(1-c)\), \(g\) for the forward cubic
defect, \(G\) for its genuine reflected counterpart, and \(I\) for
the zero-constant polynomial primitive. The three old regular
reverse clocks are the distinct nonzero roots \(v,u,w\) of
\(R_3(Y)=Y^3+c_2Y^2+c_1Y+c_0\). Write \(V=1-a\), \(B=1-b\)
for the fourth and fifth regular reverse clocks. Thus \(b,a\) are
the first and second nonorigin clean forward clocks. The symbol
\(b\) used as a clock is distinct from the weight vector.
The chronology starts \(T,v,u,w,V\), with no ghosts; then there
are \(\beta\) ghosts, row \(B\), then \(\gamma\) ghosts before \(O\).
There are six ghosts in total.

Scale the cubic ghost profile \(U\) to be monic, scaling the
forward defect too. The true grade-three column
\(\phi=U(c)-g\) is clean-supported. The reciprocal equation is
\(G\phi=\tau H_{\rm bary}\). When \(\tau=0\), the old three live
values of \(G\) force \(U\) to vanish at their forward clocks,
so \(U(X)=-R_3(1-X)\). Thus \(G\) vanishes at \(V,B,O\);
it also vanishes at the terminal \(T\), and is live on all six
ghosts. The dirty clocks cannot coincide with old clocks, because
each actual dirty value \(U(c_i)\) is nonzero. No other dirty/clean
collision is excluded.

At \(V\), \(NG\) and \(N(YG)\) vanish, since their actual paid
shapes are \(G\mathcal P_1\) and \(G\mathcal P_2\).
The first four ordinary moments at \(V\) are exact: the first
two by the reflected simplifying assumptions, and the next two
because their genuine defects are \(G\), \(G\) times an affine
polynomial, both zero at \(V\). For each old node \(r\) put
\(k(r)=G_r/b_r\); let \(t_r=N_{V,r}b_r/b_V\) be its normalized
actual ordinary tap. The moments of \(t_r k(r)\) against 1 and
\(r\) vanish. All three taps must be nonzero: two or fewer live
taps would force each \(t_rk(r)\) to vanish by interpolation,
and the remaining diagonal alone could not give both first and
second moments at \(V\ne0\). Thus \(t_r k(r)\) is a nonzero
common multiple of \(1/R_3'(r)\).

The first four exact moments determine \(t_r\) by the ordinary
Lagrange test \(Y(Y-V)R_3(Y)/(Y-r)\); the factor \(Y\) discards
the literal terminal. Its primitive at \(V\) is
\[
 -\frac{V^3}{60}\,D(r),\qquad
 D(Y)=10Y^2+(5V+10c_2)Y+3V^2+5Vc_2+10c_1.
\]
Consequently \(D(r)\ne0\) at each old site and
\(k(r)\) is a common nonzero multiple of \(r(r-V)/D(r)\).
No unknown diagonal or ghost clock is divided by.

## 2. An unordered affine mark forces the diagonal to vanish

Put \(P_0=YR_3(Y)\). Let \(m\) denote the quadratic representative
of \((Y-V)/D\) modulo \(R_3\), and \(P=Ym\). Up to the common
normalization of \(G\), \(P\) agrees with \(G/b\) at the old
three and vanishes at the terminal. At each old row, literal
chronology gives \(NW(P)=NG\) in that normalization. The true
cubic primitive \(W(IP)-NW(P)\) and \(NG\) both belong to
\(G\mathcal P_1\). Thus the cubic quotient \(IP/P\), reduced
modulo \(R_3\), is affine. All old denominators are live.

Here is the exact coefficient test. In \(K[Y]/R_3\) let \(M\)
be multiplication by \(D\), and set
\(m_*=\operatorname{adj}(M)(Y-V)\) in the basis \(1,Y,Y^2\).
Then \(m_*=(\det M)m\), and \(\det M\ne0\).
Form the three columns
\[
 m_*,\quad Y m_*\bmod R_3,\quad I(Y m_*)/Y\bmod R_3.
\]
The determinant is zero by the affine mark. Its universal
polynomial identity is
\[
 12\det=-V^2(\det M)
      (12V^3+15V^2c_2+20Vc_1+30c_0)^2.
\]
The replay checks the entire identity and the adjugate vector
before specializing. Therefore \(IP_0(V)=0\): it is \(V^2/60\)
times the last parenthesis. The fourth-power exact read at
\(V\), applied to \(P_0\), has only the diagonal contribution
\(A_{aa}P_0(V)\), because all old and terminal input values
vanish. As \(P_0(V)\ne0\), this gives \(A_{aa}=0\).

Ordinary degree-ten quadrature puts the five ordinary nonendpoint
clean forward clocks on the monic \(T_5=(J_5+\lambda J_4)/132\),
with
\[
 J_4=42X^4-84X^3+56X^2-14X+1,\qquad
 J_5=(2X-1)(66X^4-132X^3+84X^2-18X+1).
\]
Use \(\lambda=-J_5(a)/J_4(a)\), valid at the observed clean site,
and deflate at \(a,b\) to give the exact old forward cubic \(U\).
All clock points with \(IP_0(V)=0\) satisfy the quartic pair
relation
\[
 F(a,b)=\frac{J_5(b)J_4(a)-J_5(a)J_4(b)}{b-a}=0
\]
and the third-degree equation in \(b\) obtained by clearing
\(J_4(a)\) in \(60IP_0(V)/V^2=0\).
Their exact resultant in \(b\) has primitive factors \(J_4(a)^4\)
and an irreducible degree-24 factor in \(a\). The former is already
excluded by coprimality of the Jacobi polynomials. The explicit
linear cofactor of these two polynomials has a unit leading
coefficient in the whole degree-24 algebra modulo 101. Hence it
determines \(b\) over any candidate. This reconstruction is
independent of \(\beta,\gamma\).

## 3. The genuine forward five-zero cut

Write \(R_6^{\rm rev}\) for the monic hull of the six distinct
dirty reverse clocks. Since \(G\in E_7^\perp\), its moments of
degree 0 through 7 vanish. There are exactly nine distinct
numerical clocks on its support (the old triple and six ghosts).
The unique annihilator row on these nodes is their barycentric
row. Thus at an old site,
\[
 G_r\ \propto\ \frac1{R_3'(r)R_6^{\rm rev}(r)}.
\]
Likewise the clean barycentric row \(H_{\rm bary}\) is supported
on the six nonterminal clean clocks (the old triple and \(V,B,1\));
its values there are proportional to the reciprocals of the
derivative of their hull. At old sites,
\(H_{{\rm bary},r}/b_r=h(r)=rJ_4(r)\) after a common scaling.
Compare these two barycentric reads with Section 1 and cancel
only the live old values \(r,r-V\). It follows that
\[
 R_6^{\rm rev}(r)\ \propto\
     (r-1)(r-B)J_4(r)D(r)
\]
at all three old sites, with one common nonzero multiplier.
This gives the exact direction of \(R_6^{\rm rev}\) modulo \(R_3\).

Now take the actual grade-four forward column \(C\phi\).
On each of the five initial forward ghosts, \(A(C\phi)\) is
zero: all available ghost coordinates of \(\phi\) are zero,
and the only possible clean donor is the origin with clock zero.
The paid grade-five error is \(A(C\phi)-I(XU)(c)\in F_5=
g\mathcal P_2(c)\). Thus their five distinct clocks are roots of
\(I(XU)+UQ_2\) for one quadratic or lower \(Q_2\).
This polynomial is not zero: if \(U\mid I(XU)\), the quotient
has degree two and, because \(U(0)\ne0\), valuation two.
Its quadratic coefficient would have to be both \(1/2\) and
\(1/5\), from the constant and leading coefficients of \(U\).
Therefore the polynomial is a nonzero scalar times the monic
five-ghost hull. Multiply it by \(X-\xi\), with \(\xi\) the
sole other forward ghost clock, to get a scalar times the full
six-ghost hull. Modulo \(U\), this says
\[
 (X-\xi)I(XU)\ \propto\ R_6^{\rm rev}(1-X).
\]
There is no sign change for the degree-six reflection. With
\(X=1-Y\) in the old cubic quotient, the three columns
\[
 I(XU),\qquad X I(XU),\qquad
 (Y-1)(Y-B)J_4(Y)D(Y)
\]
are therefore dependent. No division by \(\xi\), a ghost
clock difference, or any coincident clean/ghost difference
was used. Their determinant is a unit in the whole degree-24
clock algebra modulo 101. This is the contradiction.

## 4. Reproduction and proof level

Run `python3 replay.py` with SymPy and the sibling
[constant closure arithmetic](../dirk11-thirteen-invisible-six-constant-exclusion/replay.py).
An isolated layout can supply `--arithmetic PATH`. Exact
rational arithmetic verifies the adjugate identity, resultant
and its factor inventory. Modulo 101, the determinant and all
clock reconstruction inversions are multiplied back to one.
The monic base clock algebra is finite free over
\(\mathbb Z_{(101)}\). Thus the tested unit lifts by the
multiplication determinant and its adjugate. No coefficient
of an unknown tableau, no weight, and no ghost clock is
assumed integral or reduced modulo 101. The arithmetic
gate here is distinct from the automatic Jacobi identities
obtained by comparing the pure forward/backward fourth and
sixth primitive reads.
