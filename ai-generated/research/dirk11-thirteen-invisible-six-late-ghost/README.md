# A finite late-ghost chart in invisible six-clock DIRK11/13

Assume the same normalized actual-rooted-order-eleven signed
census as the [invisible five-clock proof](../dirk11-thirteen-invisible-five/README.md),
but take \(r=0,d=z=6\). Thus there are six unweighted physical
dirty stages at distinct labels, and seven ordinary clean
physical rows at distinct labels, including actual 0 and 1.
The direction proved here is **conditional**: if one of the
six ghosts is before the third live non-endpoint ordinary
row in reverse chronology, then the first three ordinary
labels are among the same twelve real degree-60 macro
triples as the prior one-active reduction, and the third
literal ordinary diagonal is zero. There is at most one
such late ghost. This does not exclude the chart with
a late ghost, or its complementary earliest clean suffix.
The unrestricted interval remains **13–14**.

## 1. Exact reverse ranks and the latest two regular stages

Use \(y=1-c,Y=\operatorname{diag}(y),N=A^{\mathsf T}\) in reverse
physical order. Write \(W(P)=bP(y)\) and
\(G=NW(X^2)-W(X^3/3)\) for the genuine cubic.
As in the local-label census, the true \(E_6,E_7\) are
\(\mathcal P_5(c)+g\mathcal P_3(c)+K e_T\) and
\(\mathcal P_5(c)+g\mathcal P_4(c)+K e_T\), respectively.
The \(g\)-weighted reads of nonzero \(G\) on the six ghosts
annihilate degrees zero through four. They cannot all be zero,
as then \(G\) would be supported on the six nonterminal
ordinary sites with all its degree-five reads zero, hence
zero (the terminal entry is zero). By Vandermonde they are
therefore nonzero at each of the six distinct ghost labels.

Consequently the true \(U_0=E_6^\perp\) is
\(\langle G,YG\rangle\), and \(Z=E_5^\perp\cap\{T=0\}\) is
\(\langle G,YG,Y^2G\rangle\), by actual grading, distinct
ghost clocks and the known ranks. In particular
\(NG\in U_0,\ G_4=L(Y)G\) with \(L\) affine, and
\(G_5=Q(Y)G\) with \(Q\) quadratic-or-lower. The \(G_j\)
are the true reflected monomial defects at the indicated
grade; there is no assumption about order of a transposed
tableau.

Let \(v,u\) be the successive first two live nonzero
non-endpoint ordinary labels in reverse. At any ghost
before \(v\) there is no active positive-power donor,
so \(G\) is zero there, impossible. At a ghost between
\(v\) and \(u\), the only possible nonzero weighted donor
is \(v\). Its true first moment has zero target, hence
zero tap on the only such donor and \(G=0\), again
impossible. Thus the first three literal physical rows
in reverse are the terminal, \(v\), \(u\).
At the latest ordinary \(v\), \(G_v=b_v v^3/6\ne0\).
Also \(G_u\ne0\): if zero then \((NG)_u=0\) by
\(NG\in\langle G,YG\rangle\). With a live earlier \(G_v\)
and zero terminal \(G\), this kills the sole \(v\) tap.
The first and second ordinary positive-power moments at
\(u\) would then require both half and third for its
own diagonal.

## 2. The ghost forces a literal zero pivot

Let a ghost at \(z\) occur before the third live ordinary
\(w\). It follows \(v,u\) by §1, so it has only \(v,u\) as
possible nonzero active donor labels. The first weighted
moment is zero at its ghost column. Reducing the third
and fourth powers on \(\{u,v\}\), with its live cubic
entry \(G_z\), gives
\[
 L(z)=u+v,\qquad Q(z)=u^2+uv+v^2.
\]
At \(v\), actual diagonal \(v/2\) gives
\(L(v)=3v/2\) and \(Q(v)=9v^2/5\).
If \(z=v\), its \(L\) value forces \(u=v/2\) and its \(Q\)
value becomes \(7v^2/4\ne9v^2/5\). If \(z=u\), the cubic
nodal test \(P=Y(Y-u)(Y-v)\) at \(u\) gives \(u=2v\),
yet the positive-degree-four reduction with \(YP\)
then has nonzero primitive \(I(YP)(u)=u^4(5v-3u)/60\).
This contradicts the stated \(Q(z)\). Thus \(z\) differs
from both \(u,v\). The affine \(L\) must be nonconstant
here: if it is constant with value \(u+v=3v/2\), then
\(u=v/2\), whereas its cubic nodal test at \(u\) forces
\(u=2v\). Therefore there is at most one such ghost
(all would have the same numerical root of
\(L(X)=u+v\), and ghost clocks are distinct).

The literal input \(W(P)\) is zero on the strict
prefix before \(w\). The genuine reverse Volterra row
\(\mathcal R^{\mathsf T}W(P)\), \(\mathcal R=CA-AC-A^2\),
lies in \(Z\) by the true grade \(3+7=10\) payment
against \(\mathcal R E_5\subset F_7\) and the zero
terminal column. It is zero at the physical \(v,u,z\),
where \(G\) is live at three distinct clocks, so
its quadratic multiplier is zero everywhere.
At the pivot \(w\), \(P(w)\ne0\) and its weight
is nonzero. This forces the literal \(A_{ww}=0\)
by the diagonal \(-A_{ww}^2\).

## 3. Exact cubic macro gate including its degeneracies

The actual primitive error \(NW(P)-W(IP)\) lies in \(U_0\)
and at the ghost \(z\) vanishes, hence is \(\rho(Y-z)G\)
for a scalar \(\rho\). Its old clean \(u,v\) entries give
\(-b_s I P(s)=\rho(s-z)G_s\). Here \(\rho\ne0\) because
the two primitive values cannot both vanish. Thus both
primitive values at \(u,v\) are nonzero.

At the explicit \(w\), \(NW(P)_w=0\) as well. If \(G_w=0\)
or \(w=z\) numerically, its ordinary primitive \(IP(w)\)
is zero. In either case the two consecutive paid scalar
reductions on the actual donors \(0,u,v\) give \(I(YP)(w)=0\):
when \(G_w=0\) all paid reflected defects vanish there,
and when \(w=z\) their multipliers equal the ghost's
values \(L(z)=u+v,\ Q(z)=u^2+uv+v^2\).
The two zero nodal primitives give the exact Radau
relations \(u+v=6w/5,\ uv=3w^2/10\), which imply \(J=0\)
for the polynomial below.

Otherwise \(G_w,IP(w)\) and \(w-z\) are all nonzero.
At each of \(u,v,w\) there are only the nonzero active
donor labels \(u,v\) in the actual inclusive read
(the \(w\) diagonal is zero and the ghost weight zero).
Reducing the fourth power on this donor set gives
\[
 (Q(s)-Q(z))G_s
   =-b_s\big[I(YP)(s)+(u+v)IP(s)\big],\qquad s=u,v,w.
\]
Divide by the primitive relation
\(-b_s IP(s)=\rho(s-z)G_s\). Since \(Q\) is quadratic,
\(I(YP)(s)/IP(s)\) must be affine across these three
labels. The explicit cleared determinant is
\[
 \begin{split}
 &(v-w) I(YP)(u)IP(v)IP(w)
 +(w-u)I(YP)(v)IP(u)IP(w)
 +(u-v) I(YP)(w)IP(u)IP(v) \\
 &\qquad=-u^3 v^3 w^2(u-v)(u-w)(v-w)J/1440,\qquad
 J=w(u^2-4uv+v^2)+uv(u+v).
 \end{split}
\]
The known distinct nonzero labels therefore give \(J=0\)
in every branch. The ordinary seven-label quadrature
with true endpoints gives their same Jacobi pencil;
the earlier [degree-60 replay](../dirk11-thirteen-one-active-macro/README.md)
applies verbatim, so among real arrays there are at
most twelve ordered triples \((u,v,w)\). Since any
Radau-degenerate case above would give
\(5(v/u)^2-14(v/u)+5=0\), coprimality with the irreducible
degree-60 factor also excludes that exceptional chart.
In particular \(G_w\ne0\) and \(w\ne z\) in the surviving
late-ghost candidates. This last coprimality uses only
the scalar degree-60 field obstruction, not reduction
of any unknown tableau.

The companion Lean module verifies the cleared
determinant and Radau implication. This is a finite
necessary macro reduction for the late-ghost subcase.
The ghost clock itself and the complementary no-late-
ghost chronology have not been eliminated.
