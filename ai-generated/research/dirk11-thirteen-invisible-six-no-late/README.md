# Nine remaining chronologies in the normalized invisible six-clock chart

Assume the normalized actual \(13\)-stage DIRK order-\(11\) census with
\(r=0,d=z_{\mathrm{count}}=6\), as in the
[late-ghost exclusion](../dirk11-thirteen-invisible-six-paid/README.md).
There are precisely six unweighted dirty stages with distinct numerical
dirty clocks, and seven distinct ordinary clean sites including the true
endpoints. The late-ghost exclusion starts the literal reverse array
with \(T,v,u,w\), four consecutive clean stages including the actual
terminal \(T\). The following narrows the remaining **no-late-ghost**
phase but does not exclude it over the reals.

In reverse chronology write
\[
 T,\ v,\ u,\ w,\ [\alpha\text{ ghosts}],\ a,\
 [\beta\text{ ghosts}],\ b,\ [\gamma\text{ ghosts}],\ O .
\]
Here \(v,u,w,a,b\) are the live non-endpoint clean clocks and \(O\) is
the physical origin. Every still-possible count has
\[
 \alpha\le2,\qquad \gamma\ge3,\qquad \alpha+\beta+\gamma=6.
\]
Thus exactly nine *not-yet-excluded count profiles* remain:
\[
 \begin{array}{c|l}
 \alpha&(\beta,\gamma)\\\hline
 0&(0,6),(1,5),(2,4),(3,3)\\
 1&(0,5),(1,4),(2,3)\\
 2&(0,4),(1,3)
 \end{array}
\]
This is a count of possibilities not eliminated by the two cuts, not a
claim that any profile is realizable. No numerical endpoint improves.

## 1. The first nonorigin forward clean needs three ghosts

Let \(g=Ac^2-c^3/3\) be the actual cubic defect and \(C=\operatorname{diag}(c)\).
The six dirty clocks are distinct and their cubic entries are live.
Hence \(g\mathcal P_1(c)\) and \(g\mathcal P_2(c)\) have dimensions 2 and
3. By the actual graded ranks these exhaust the true zero-profile
spaces \(F_4,F_5\), respectively. In particular \(Ag\in F_4\) and
\(A(Cg)\in F_5\) both vanish at every clean stage. At the first
nonorigin forward clean stage \(b\) the only possible donors are
the origin, the \(\gamma\) preceding dirty rows, and its own diagonal.

If \(\gamma\le2\), the two reads \(Ag,A(Cg)\) at \(b\) kill every
ghost tap: for two ghosts the two-by-two determinant is the product
of their nonzero \(g\) entries and their clock difference. For one
ghost only the first read is needed, and none needs no read. The
origin has zero clock and \(g=0\). The two paid first and second
positive-power ordinary reads at this clean stage now use only
its diagonal. At the nonzero forward clock \(x=c_b\), they would
force both \(A_{bb}=x/2\) and \(A_{bb}=x/3\). The first is the
actual \(C(2)\) equation and the second is the vanishing actual
cubic. Thus \(\gamma\ge3\). Numerical coincidences of a dirty
clock with \(x\) or with the origin do not affect the determinant.

## 2. At most two ghosts in the first open reverse gap

Use \(y=1-c,\ Y=\operatorname{diag}(y),\ N=A^{\mathsf T}\) in reverse,
\(W(F)=bF(y)\) and the genuine cubic reverse row \(G\) of the
[macro cut](../dirk11-thirteen-invisible-six-late-ghost/README.md).
In this signed census \(G_i\ne0\) on every dirty ghost and the
actual terminal-zero budgets are
\(U_0=E_6^\perp=\langle G,YG\rangle\) and
\(Z_5=E_5^\perp\cap\{T=0\}=\langle G,YG,Y^2G\rangle\).
For \(P=X(X-u)(X-v)\), put \(K=IP,\ J=I(XP)\). The two actual
primitive rows have the shapes
\[
 W(K)-NW(P)=p(Y)G,\quad W(J)-NW(XP)=q(Y)G,
 \qquad \deg p\le1,\quad \deg q\le2.
\]
This is the same paid grade as in the earlier work but does **not**
assume a common root for \(p,q\). On an unweighted ghost between
\(w\) and \(a\), the only possible nonzero \(W(P)\) and \(W(XP)\)
donor is \(w\), so \(q(y_i)=w p(y_i)\) by \(G_i\ne0\).
Thus three distinct ghosts in this gap would imply \(q=w p\)
identically. At each of \(u,v\), the inputs vanish on the entire
inclusive donor set, and \(b_u,b_v\ne0\). This implies
\(J(u)=wK(u),\ J(v)=wK(v)\). The exact determinant
\[
 J(v)K(u)-J(u)K(v)=u^3v^3(u-v)^3/120
\]
is nonzero. This excludes three ghosts in the gap, even if one
of the primitive values \(K(u),K(v)\) vanishes. Distinctness is
required only among dirty clocks and among the old ordinary
clocks, not across the two colors.

## 3. A smaller charged scalar system at the next event

The actual third ordinary \(w\) has \(G_w\ne0\), independently of
the next ghost choice. Otherwise \(NG,N(YG)\) also vanish there,
since \(NG=\Lambda(Y)G\) with affine \(\Lambda\)
(\(G\in E_7^\perp\)) and \(N(YG)=M_2(Y)G\) with quadratic
\(M_2\) (\(YG\in E_6^\perp\)). The only prior nonzero ordinary
donors \(v,u\) have live \(G\) and different clocks. The two
homogeneous reads kill both taps, so the paid first moment at
\(w\) forces \(A_{ww}=w/2\), giving \(G_w=b_ww^3/6\ne0\).
The proof that \(G_u\ne0\) uses only the paid \(NG\) and the single
prior nonzero ordinary donor \(v\), as in the macro cut.

For future elimination, the following are necessary small polynomial
systems; they are not claimed to certify existence or resolve the nine
profiles. Let \(k_s=G_s/b_s\) at live clean rows, and let
\(L_1,Q_2\) be the genuine affine and quadratic multipliers of
the degree-four and degree-five primitive reverse defects. The
weighted regular taps \(T_{s,r}=b_rN_{s,r}/b_s\) have paid scalar
moments, in ascending exponents \(1,2,3,4\),
\[
 s^2/2,\quad s^3/3+k_s,\quad s^4/4+L_1(s)k_s,\quad
 s^5/5+Q_2(s)k_s .
\]
There is no normalization by a ghost weight. At \(v\),
\(k_v=v^3/6\). The moments 1 and 2 uniquely determine the
two taps to \(v,u\) at \(u\), affinely in \(k_u\). Fit
the two affine rows \(L_1,\Lambda\) from their actual \(v,u\) values.
At \(w\), the first three moments solve the taps to \(v,u,w\)
affinely in \(k_w\). The genuine equation
\(\sum_r k_r T_{w,r}=\Lambda(w)k_w\) is a polynomial of degree at
most two in \(k_w\); no leading coefficient is inverted. After this
the three live samples \(v,u,w\) fit the two quadratic profiles
\(Q_2,M_2\).

* If the next event is a first ghost at \(x\), the normalized taps
  \(T_r=b_r N_{x,r}/G_x\) on \(v,u,w\) are fixed by moments
  \(0,1,L_1(x)\). Their fourth moment equals \(Q_2(x)\).
  The marked combination \(N(YG)-xNG\) cancels the actual diagonal
  and gives \(\sum_{r\in\{v,u,w\}}(r-x)k_rT_r=M_2(x)-x\Lambda(x)\).
  These are two polynomials of degree at most two in \(x\).
* If there is no ghost before \(a\), the four scalar moments uniquely
  determine the four regular taps on \(v,u,w,a\) affinely in \(k_a\).
  The two actual mark constraints
  \(\sum_r k_rT_{a,r}=\Lambda(a)k_a\) and
  \(\sum_r r k_rT_{a,r}=M_2(a)k_a\) give two polynomials of degree at
  most two in \(k_a\). There is no division by \(k_a\).

The terminal always has zero clock in these reverse reads and contributes
neither \(G\) nor any weighted positive power. Distinct nonzero regular
clocks are sufficient for every scalar Cramer division. This starts a
two-clock/weight-parameter elimination given the common ordinary
one-parameter Jacobi pencil; it is not a finite clock classification on
its own.

The Lean module checks the two-ghost forward gate, the cleared nodal
determinant, the degree-two root-count obstruction, and the third clean
liveness scalar gate. These are scalar adapters to the paper support
census, not an end-to-end Lean characterization of a tableau. All four
were checked with the repository's pinned Lean/Mathlib 4.36.0.

**Rational-clock special case.** Over any characteristic-zero field
\(K\) in which the signed skeleton holds, no invisible six-clock
candidate can have all contributing ordinary clocks in the canonical
image of \(\mathbb Q\to K\). Weights and discarded clock labels may be
arbitrary elements of \(K\); denominators divisible by 11 (or by any
other prime) are allowed for every rational clock and for any rational
weight. This is not reduction modulo 11 and is not a claim over fields
of positive characteristic or general rings. The signed skeleton has
at most seven contributing sites after grouping equal numerical
labels and dropping zero aggregate weights. The separately reviewed
[four-shift support bound](../rational-quadrature-four-shift/proof.md)
requires at least eight for ordinary order eleven. This support
obstruction is independent of the chronology, and does not exclude
the real-algebraic chart.
