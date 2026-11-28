# No monomial reverse fit in the live cubic invisible-six DIRK11/13 chart

**Result.** In the normalized invisible-six, no-late-ghost
DIRK11/13 chart, suppose the forward ghost cubic \(U\) has
degree three, the reciprocal multiplier \(\tau\ne0\), and
\(\alpha=0\) (the fourth regular reverse stage occurs before
any ghost). Let \(m\) be the degree-at-most-two fit to
\(G/(bY)\) on the three old regular reverse clocks. Then
\(\deg m=2\) and \(m(0)\ne0\). In particular none of the
three pure-power fits \(G/b\propto Y,Y^2,Y^3\) is possible,
for any remaining values \(\gamma=3,4,5\).
The general quadratic fit with nonzero constant is not
excluded, and the unrestricted real DIRK11 interval remains
**13–14**.

Use the true rooted order and signed shape hypotheses of the
[paid](../dirk11-thirteen-invisible-six-paid/README.md),
[forward prefix](../dirk11-thirteen-invisible-six-prefix/README.md),
and [constant closure](../dirk11-thirteen-invisible-six-constant-exclusion/README.md)
packets, with the above \(\tau,\alpha,\deg U\) restrictions:
there are six unweighted physical dirty rows at distinct
clocks and seven distinct clean clocks including the literal
endpoints. The five ordinary nonendpoint clean weights are
live. The proof applies over every characteristic-zero field
once these normalized ranks hold; no field ordering or
positivity is needed. The separate \(\tau=0\) cubic chart is
treated in the [five-prefix](../dirk11-thirteen-invisible-six-cubic-zero-five/README.md)
and [two-gap](../dirk11-thirteen-invisible-six-cubic-zero-two/README.md)
packets.

Write \(C=\operatorname{diag}(c)\), \(Y=\operatorname{diag}(1-c)\),
\(N=A^{\mathsf T}\) in literal reverse order, \(W(P)=bP(1-c)\),
and \(I\) for the zero-constant primitive. The old three regular
reverse clocks are the roots of
\(R_3(Y)=Y^3+c_2Y^2+c_1Y+c_0\).
Write \(V=1-a\) and \(B=1-b\) for the fourth and fifth ordinary
reverse clocks, so the reverse order starts
\(T,v,u,w,V,[\beta],B,[\gamma],O\).
All old clocks and \(V,B\) are distinct, and are neither 0 nor 1.
Let \(G\) be the actual reflected cubic defect, \(g\) the forward
one, and \(\phi=U(c)-g\) the true clean-supported grade-three
column (a common scaling of \(g,U\) is harmless).

The nonzero multiplier identity \(G\phi=\tau H_{\rm bary}\)
gives both \(G,U(c)\) live on the six nonterminal clean clocks.
At regular nonendpoint rows
\(G_i/b_i=\kappa\,h(y_i)/U(1-y_i)\) for a common
\(\kappa\ne0\), with \(h(Y)=YJ_4(Y)\). Here and below the
weighted normalized fits are divided only at live clean rows,
never at an unweighted ghost. No special assumption is made
about \(U(1)\) at the true terminal.

## 1. Low interpolation degrees and an actual fourth-clean transfer

Rescale the common \(G\) normalization freely and let \(m\)
fit \(G/bY\) on the old triple. Put \(P=Ym\) and
\(P_1=Y(Ym\bmod R_3)\). The actual grade-four primitive
\(W(IP)-NW(P)\) and \(NG\) both lie in \(G\mathcal P_1\).
Since \(W(P)=G\) on all old inclusive donors (including
the terminal with both zero), \(r_0=IP/P\bmod R_3\)
is affine. Likewise \(r_1=IP_1/P\bmod R_3\) is the
quadratic old fit to the corresponding sum of primitive
error and \(N(YG)\) multipliers. All these fits have
live old denominators.

For \(m=x+yY\), if \(r_0=\ell_0+\ell_1Y\), compare
\(IP/Y=(\ell_0+\ell_1Y)m\) modulo \(R_3\). Both sides have
degree at most two; the coefficient equalities are ordinary.
If \(x,y\ne0\), they force \(\ell_0=0,\ell_1=1/2=1/3\),
impossible. Thus a low-degree \(m\) must be a monomial.
For degree two, scale \(m=Y^2+rY+s\). The determinant of
\(m,Ym,12I(Ym)/Y\) modulo \(R_3\) has exact expression
\[
 -2s^2r+3s^2c_2-src_1-3sc_0+r^2 c_0 .
\]
It vanishes by the same affine fit. If \(s=0\), then \(r=0\)
since \(c_0\ne0\) (old roots nonzero). It remains to exclude
\(m=1,Y,Y^2\) after scaling; equivalently \(G/b=Y^j\) on the
old triple for \(j=1,2,3\).

Let \(q=G_V/b_V\) in this normalization and \(d\) the literal
fourth ordinary diagonal. There are no ghosts before \(V\)
and its only possible new inclusive donor is itself.
The two **genuine** cubic marks give
\[
\begin{split}
 IP(V)-d(P(V)-q)&=r_0(V)q,\\
 IP_1(V)-d(P_1(V)-Vq)&=r_1(V)q .
\end{split}
\tag{1}
\]
For \(j=1,2\), \(P=Y^j,P_1=Y^{j+1}\); the fits are
\(r_0=Y/(j+1),r_1=Y^2/(j+2)\). Unless \(q=V^j\),
the two equations force incompatible diagonal values
\(V/(j+1),V/(j+2)\). Thus \(q=V^j\) on these two charts.

For \(j=3\), \(r_0=Y/4\),
\(P_1=-c_0Y-c_1Y^2-c_2Y^3\), and
\(r_1=Y^2/2+c_2Y/4+c_1/6\) after reduction modulo \(R_3\).
If \(q\ne V^3\), the first equation gives \(d=V/4\).
Use also the paid quartic primitive of \(P_0=YR_3(Y)\).
Its fit \(w_0=IP_0/P\bmod R_3\) is
\(-3Y^2/10-c_2Y/4-c_1/6\); all old taps from \(P_0\) are
zero. At \(V\) exact chronology gives
\(IP_0(V)-d P_0(V)=w_0(V)q\).
Together with the second equation of (1), at \(d=V/4\)
the two cleared equations are
\[
\begin{split}
 (3V^2+3c_2V+2c_1)q&=-3c_0V^2-c_1V^3,\\
 (-18V^2-15c_2V-10c_1)q&=-3V^5+5c_1V^3+15c_0V^2 .
\end{split}
\]
Adding five times the first to the second gives \(q=V^3\),
using \(V\ne0\), a contradiction to the assumed difference.
This treats every coefficient pivot of that mark, including
zero coefficients of either displayed equation. In all three
charts the same scaling \(G/b\propto Y^j\) therefore holds on
the complete old-plus-\(V\) clean prefix.

## 2. The pair of commutators forces a zero clock at the gap

Return to \(G\) with its actual cubic defect scale and write
\(\kappa_1 b_i y_i^j=G_i\) throughout the ordinary prefix.
Both this and its \(Y\)-multiple match at the literal terminal:
the power is positive and \(G_T=0\). For the true commutator
\(\mathcal R=CA-AC-A^2\) use the two rows
\[
 L=\mathcal R^{\mathsf T}(\kappa_1W(Y^j)-G),\qquad
 M=\mathcal R^{\mathsf T}(\kappa_1W(Y^{j+1})-YG).
\]
The first belongs to \(Z_5=G\mathcal P_2\) since \(j\le3\);
the second to \(Z_6=G\mathcal P_3+K H_{\rm bary}\) since
\(j+1\le4\). For the weighted terms these are the actual
\(3+7+1=11\) and \(4+6+1=11\) order budgets against
\(\mathcal R E_i\subset F_{i+2}\). For the \(G,YG\) terms
they follow by pairing \(G\in E_7^\perp\) with
\(\mathcal R E_5\subset E_7\) and \(Y\mathcal R E_4\subset E_7\).
Both rows vanish through \(V\) by the inclusive cut.
Thus \(L=0\) globally by at least three distinct live clean
zeros. For \(M=GQ+e H_{\rm bary}\), the four nonterminal
clean zeros through \(V\) and \(H_{\rm bary}/G=U(1-Y)/\tau\)
force the degree-at-most-three polynomial
\(Q+eU(1-Y)/\tau\) to vanish identically. Hence
\(M=-e g G/\tau\) globally.

At the first reverse-gap ghost \(z\), the only nonzero donor
in the difference defining \(L\) is its own diagonal,
and \(\mathcal R^{\mathsf T}\) has diagonal \(-d_z^2\).
Since \(G_z\ne0\) and \(L=0\), this yields \(d_z=0\).
The difference defining \(M\) is then zero at \(z\) too.
As \(g_zG_z\ne0\), also \(M=0\) globally. If there is a
physical second gap ghost \(w\), take the difference of the
two input columns with multiplier \(z\). It kills the first
ghost donor and all preceding ones, and its image is zero
since \(M-zL=0\). Hence \((w-z)G_w d_w^2=0\), so \(d_w=0\).
The unmarked \(L=0\) equation at \(w\) now reduces to
\((w-z)N_{w,z} G_z=0\): the two ghosts are physically
consecutive within the block, and the two diagonal taps
in \((N^2)_{w,z}\) are both zero. Thus \(N_{w,z}=0\).

For all \(j=1,2,3\), the true ordinary primitive row is
\[
 NW(Y^j)=W(Y^{j+1}/(j+1))+\sigma_j(Y)G,\qquad
 \deg \sigma_j\le1 ,
\]
where \(\sigma_1=0,\sigma_2=1\) and \(\sigma_3\) is the
actual affine fourth defect. On the old prefix, the
weighted match gives
\(NG/G=Y/(j+1)+\kappa_1\sigma_j(Y)\).
Both sides are affine and determined at distinct live
old sites, so the equality holds as a profile also at ghosts.
At the first gap ghost, and at the second if present, the
actual difference \(NG-\kappa_1 NW(Y^j)\) is zero:
the ghost block taps into these rows were just shown zero.
Their output weights are zero and \(G\) is live, so each
of those ghost clocks is exactly 0. This immediately
excludes \(\beta\ge2\) by their distinctness. It does not
exclude a single ghost numerically coincident with the
true reverse terminal, whose forward clock is \(1\).

## 3. One ghost remains: exact fixed-prefix polynomial obstruction

Here \(\beta=1,\gamma=5\) and the sole nonprefix forward
ghost has clock \(1\). Its carrier value \(U(1)\) is
therefore nonzero. Let \(S_6\) be the monic hull of the
six nonterminal clean forward clocks and \(R_6\) the
monic dirty forward hull. From
\(E_6=\mathcal P_5(c)+g\mathcal P_3(c)+Ke_T\),
the pure degree-five part of \(S_6(c)\) vanishes against
six distinct nonterminal clean sites. Comparing the ghosts
gives a polynomial identity \(S_6-UQ_3=\omega R_6\).
Here \(\omega\ne0\): otherwise \(U\mid S_6\), impossible
for a nonconstant cubic live at every simple root of the
split hull \(S_6\).

The genuine \(A(C\phi)\) cut at the five initial forward
ghosts is exactly as in the [five-prefix argument](../dirk11-thirteen-invisible-six-cubic-zero-five/README.md).
The cut uses \(U(0)\ne0\) and degree three, both valid
here. Thus \(I(XU)+UQ_2\) is a nonzero multiple of their
monic hull. Multiplying by \(X-1\) and reducing modulo
\(U\), the following collinearity is necessary:
\[
 (X-1) I(XU)\ \propto\ S_6(X)\pmod U . \tag{2}
\]

The old three plus \(V\) form the four-root monic
\(Q_4(Y)\) obtained by dividing the reflected ordinary
Jacobi pencil by \(Y-B\). It is defined by \(B\) alone
since \(J_4(B)\ne0\). At those four roots,
\(Y^{j-1} U(1-Y)\propto J_4(Y)\) by the common reciprocal
head and the just-proved pure-power match. This reconstructs,
up to nonzero scale, the reverse carrier as follows:
\[
\begin{array}{ll}
j=1& J_4-42Q_4,\\
j=2& [Q_4(0)J_4-Q_4]/Y,\\
j=3& [Q_4(0)^2J_4-
 Q_4\{Q_4(0)+(-14Q_4(0)-Q_4'(0))Y\}]/Y^2 .
\end{array}
\]
These are polynomial divisions at \(Y=0\), not numerical
inversions of a candidate ghost. The quotients follow from
the matching leading coefficient in the first case and
from the matching constant, then constant and linear
coefficients at zero in the other cases. \(Q_4(0)\ne0\)
because none of its four regular clean roots is zero.
Their cubic leaders are nonzero in any actual cubic chart.

The exact replay uses the integer-scaled
\(J_5(Y)J_4(B)-J_5(B)J_4(Y)\), deflates by \(Y-B\),
and constructs those three polynomials without rational
clock divisions. For each case take polynomial
pseudo-remainders of both columns of (2) modulo the
prescribed \(U\), and their three 2-by-2 minors. Their gcd
has only factors of the explicit product
\[
 B(B-1)J_4(B)\,Q_{4,\rm num}(0)\,
 \operatorname{lc}(U_{\rm num})\,
 U_{\rm num}(0)\,U_{\rm num}(1)\,U_{\rm num}(1-B).
\]
Every factor named in this product is live under the actual
hypotheses: \(B\) is an ordinary nonendpoint, \(J_4\) is
coprime to the Jacobi pencil, the four old/fourth roots
avoid zero, the carrier is cubic, \(U(0),U(b)\) are live
nonterminal clean reciprocals, and \(U(1)\) is live **at
the single physical ghost**, not from a terminal assumption.
These are the only removed factors. The live gcd is 1
in each of the three cases, proving a contradiction over
every characteristic-zero field without modular reduction.

Run `python3 replay.py` with SymPy for the exact
pseudo-remainder and dead-factor checks. The earlier forward
F6 proportionality by itself is not used as a contradiction:
the fixed-clock five-prefix condition (2) is the independent
test here.
