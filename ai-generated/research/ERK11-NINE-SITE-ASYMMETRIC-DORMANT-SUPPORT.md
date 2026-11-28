# A shorter dormant-support equation for the asymmetric nine-site chart

**Scope.** In the [asymmetric nine-site chart](ERK11-NINE-SITE-ASYMMETRIC-CENTER-ATLAS.md),
left extras are \(\{e,t\}\), right extras \(\{t,s\}\).
Thus the crossings are \(e,t\), the two actual active inner
clocks are \(h,s\), and \(z\) is the genuinely distinct dormant
clock, in any of physical 8–10. The following is a necessary
paid field identity, not an exclusion of the asymmetric chart.

Let \(q_0=\int X(1-X)H_6(X)\), with
\[
 H_6(X)=(X-a)(X-h)(X-d)(X-e)(X-t)(X-s).
\]
Degree-eight scalar Lagrange payment at the actual dormant
site gives its individual live weight
\[
               b_z=\frac{q_0}{z(1-z)H_6(z)}.
\]
No canceled or estimated pair weight is used. The actual
square-clock vectors \(V_L,V_R\) overlap only on rows 8–10.
The mixed grade-ten test
\((C-s)V_L\cdot(C-h)V_R\) cancels the two active rows and
at the dormant row its two square-clock profiles are their
literal models. Hence
\[
 I(s,h)=b_z(z-s)(z-h)V_a(z)V_b(z).
\]
Cancel only the actual nonzero clock differences and the
nonendpoint factors. Since
\(V_a(z)V_b(z)=z^2(1-z)^2(z-a)^2(z-d)^2\), the gate is
\[
             I(s,h)(z-e)(z-t)=q_0 z(1-z)(z-a)(z-d).
\]
It does not require an individual middle primitive to be
nonzero. Its scope is independent of which of \(h,s\)
comes first, and survives reflection of the actual weighted
transpose ledger.

## A low-degree row when the edge pins the dormant clock

Let \(\Delta,\Sigma,\Pi\) be the true signed shifted
two-free-site sums from the four-calibration hull, and
\(\Omega\) its live unshifted 3-by-3 Hankel determinant.
Then \(\Delta\ne0,\ \Delta(t+s)=\Sigma,\ \Delta ts=\Pi\)
and \(\Delta q_0=\Omega\). Define
\[
 p=I_2-hI_1,\quad q=hI_0-I_1,\quad Y=\Delta t .
\]
Since \(I(s,h)=p+qs\), the safely cleared gate is linear
in the scaled shared crossing label \(Y\):
\[
       (z-e)\bigl[pz\Delta+qz\Sigma-q\Pi-(p+qz)Y\bigr]
       -\Omega z(1-z)(z-a)(z-d)=0.
\]
The companion Lean file checks this arithmetic over a
commutative ring, as well as the prefactor identity before
field cancellation. It does not claim an arbitrary-ring
field-guard or mixed tableau theorem.

## Why this is not a second constraint in addition to crossover

A more general equivalence explains the repeated appearance of
this equation. Suppose the two crossing labels are \(u,v\), with
\(x,y\) the other active nonplateau labels. Put
\(g(X)=X(X-1)(X-a)(X-d)\), so \(g^2=V_a V_b\).
Let \(L(X)\) be the linear interpolant of \(g(u)/(u-z)\)
and \(g(v)/(v-z)\) at \(u,v\). The cleared divided crossover
with its true nine-site Lagrange observations is
\[
   (z-u)(z-v)\int (X-z)(X-x)(X-y)g(X)L(X).
\]
The polynomial \(g(X)-(X-z)L(X)\) vanishes at \(u,v\).
After dividing by \((X-u)(X-v)\), subtract its value
\(g(z)/((z-u)(z-v))\) at \(z\). The remaining polynomial
is \((X-z)R(X)\) for \(\deg R\le1\).
Upon integration against \((X-x)(X-y)g(X)\) this last term
vanishes by the true degree-nine and ten nodal moments.
The resulting cleared divided crossover is exactly
\[
                     (z-u)(z-v)I(x,y)+q_0 g(z).
\]
For exactly two crossings, their complementary \(x,y\) are
the actual inner labels, so this is precisely the dormant
support equation and must not be counted as an additional
independent constraint. It is an independent test relative to
a necessary system using neither masked support nor crossover.
