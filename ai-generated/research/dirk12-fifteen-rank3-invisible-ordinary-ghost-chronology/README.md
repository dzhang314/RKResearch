# DIRK12/15: literal ordinary fourth-ghost chronology and finite forward projections

Work in real ordinary fifteen-stage order-twelve \(C(2),f_5=3\), with truly invisible weighted forward cubic and exactly four distinct cubic-dirty physical ghosts, in the high-site quotient. This proof applies independently to the [nine-site early reverse return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md) and [ten-site earliest extra reflected zero](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md) chronologies. In either, the first two nonzero live clocks \(a,b\) in **ordinary forward physical order** are unique physical live rows; the literal ordinary origin is live and is the only live row at clock zero. At ten sites the nonterminal live labels are distinct. At nine sites the only repeated live label is the early reverse pair, which is near the ordinary physical end and cannot be the literal ordinary origin.

The real interval remains **15–16**. These restrictions are exact:

- If exactly three ghosts precede \(a\), let \(z\) be the later fourth ghost clock. The literal ordinary diagonals at \(a,b\) are zero and the fourth ghost diagonal is \(b-z\ne0\). The fourth ghost **cannot share the clock of either \(a\) or \(b\)**.
- Writing \(x=b/a\), one has
\[
 \frac za=\frac{x(5x-2)}{3(2x-1)},\qquad
 (2x-1)L_6'(ax)=x^3(2x^2-6x+5)L_6'(a).
\]
In particular a late ghost at numerical \(0\) gives \(b=2a/5\), and \(a\) is one of three exactly isolated real quintic roots.
- For \(z\ne0\) the amplitude of the late ghost is fixed by the early cubic mask. The mixed reverse ratio from the [nine-site](../dirk12-fifteen-rank3-invisible-nine-site-early-return/mixed-grade-six.md) or [ten-site](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md) chart then makes **all five** ordinary moment coefficients explicit, not just linearly dependent.
- If all four ghosts precede \(a\), it is impossible for their amplitudes to fit one scalar cubic vanishing at zero. Equivalently the matrix of ghost columns \(c,c^2,c^3,h\) is nonsingular. This is a separate controlled subchart of the no-late case, not its full exclusion.

## Actual grades and one ordinary cubic mask

Use \(C=\operatorname{diag}(\mathbf c)\), the true ordinary \(A\), and the genuine ordinary pure spaces \(F_j\). The four distinct ghost clocks imply
\[
               F_3=\langle\mathbf h\rangle,\quad
               F_4=\mathbf hP_1(\mathbf c),\quad
               F_5=\mathbf hP_2(\mathbf c).
\]
They vanish at every live row. The actual \(F_6\) live projection is one line, with nonterminal profile \(X L_6'(X)\), by the [rank-one terminal-profile calculation](../dirk12-fifteen-rank3-invisible-four-ghost-variable-grid/README.md). Crucially, if only three ghosts precede the first ordinary live nonzero clock \(a\), the [two-mode tap calculation](../dirk12-fifteen-rank3-invisible-four-ghost-variable-high-sites/README.md) proves \(L_6'(a)\ne0\): an unobserved ghost at the first \(a\)-row would otherwise force every ghost tap there to vanish. All four ghosts precede the next distinct ordinary live nonzero clock \(b\). The ordinary prefix in the late case is literally the origin, three ghosts, \(a\), the fourth ghost, then \(b\).

For the late case construct a **true numerical grade-three** state
\[
                      \mathbf V=S(\mathbf c)-e\mathbf h
\]
zero on the entire prefix strictly before \(a\), with \(S\in P_3,\ S(0)=0,\ S\ne0\). If all three earlier ghost clocks are nonzero, choose the unique cubic with \(S(0)=0\) matching their three nonzero amplitudes and use \(e=1\). If one earlier ghost is at clock zero, take the bare nonzero cubic \(S=X(X-d_1)(X-d_2)\), where \(d_1,d_2\) are the other two early ghost clocks, and \(e=0\). This explicitly handles a zero-clock ghost different from the live literal origin. The analogous cubic mask exists by hypothesis in the separated all-four-before-\(a\) subchart.

Let \(R=CA-AC-A^2\). The scalar identity \(XJ-JX=J^2\) gives \(R\mathbf V\in F_5\), where \(J\) is the ordinary scalar primitive based at zero. At \(a\), true lower triangularity gives \((R\mathbf V)_a=-A_{aa}^2S(a)\), since the earlier state is zero. It is also zero by genuine \(F_5\) invisibility. Whether \(S(a)=0\) or the actual diagonal is zero, the actual reads \(A\mathbf V,AC\mathbf V\) are both zero at \(a\). Their respective grade-four and grade-five defects vanish there as well, so \(JS(a)=J(XS)(a)=0\). The two power moments of the cubic with zero constant give
\[
                     S(X)=\kappa X(10X^2-12aX+3a^2),\qquad\kappa\ne0 .
\]
In particular \(S(a)=\kappa a^3\ne0\); thus \(A_{aa}=0\). The actual \(R\mathbf V\) vanishes on the three early ghost rows by chronology, so as an \(\mathbf hP_2\) word it is identically zero even on the fourth ghost. This does not require any ghost to have nonzero weight.

## Genuine grade-six commutators make the next live row explicit

Set \(\mathbf U=(C-aI)\mathbf V,\ \mathbf W=A\mathbf V\), both actual grade four. Both are zero through the \(a\)-row inclusively. Hence \(R\mathbf U,R\mathbf W\in F_6\) have zero numerical values at \(a\). Since \(a L_6'(a)\ne0\), both are zero on every live row, though they need not be zero at the late ghost. Write \(\beta=A_{bb}\), \(\delta=A_{g_*,g_*}\) for its actual ghost diagonal, \(q=A_{b,g_*}\), and
\[
 j=JS(b),\quad l=J^2S(b),\quad f=J(XS)(b)-a JS(b),\quad
 s=S(b),\quad M=b-z-\beta-\delta .
\]
The actual support of \(\mathbf U,\mathbf W\) before \(b\) is contained in the single fourth ghost. Their exact primitive reads at \(b\) (genuine grade five) are
\[
 qU_{g_*}+\beta(b-a)s=f,\qquad
 qW_{g_*}+\beta j=l .
\]
The physical row-to-row coefficient of \(R\) from the fourth ghost into \(b\) is \(Mq\), because that ghost is immediately before \(b\). The \(\beta^2\) of \(R_{bb}\) is the literal diagonal term. Thus the two genuine grade-six zeros at \(b\) are
\[
 MqU_{g_*}=\beta^2(b-a)s,\qquad MqW_{g_*}=\beta^2j .
\]
Cross-multiplying and using the two primitive reads eliminates all taps and gives
\[
      \beta^2(fj-l(b-a)s)=0,\qquad
      fj-l(b-a)s=-3\kappa^2 a b^4(a-b)^4/4\ne0 .
\]
Consequently \(\beta=0\). Since \(l=\kappa b^3(b-a)^2/2\ne0\), \(qW_{g_*}=l\) and the second commutator read gives \(M=0\), so \(\delta=b-z\). Neither implication divides by a zero coefficient or relies on the sign of a row weight.

At the late ghost, \(R\mathbf V=0\) and \(\mathbf W=A\mathbf V\) directly give
\[
                 (z-a-\delta)W_{g_*}=\delta(z-a)V_{g_*}.
\]
Indeed the only earlier nonzero \(\mathbf V\) is at \(a\), and \(\mathbf W\) is zero through that row. Multiply by \(q\) and substitute the actual primitive reads to get
\((z-a-\delta)l=\delta f\).
With \(\delta=b-z\), this is
\[
                         (6b-3a)z=b(5b-2a).
\]
The coefficient \(2b-a\) cannot be zero since then \(b(5b-2a)=a^2/4\ne0\). If \(z=b\), the ghost relation has \(\delta=0\), forcing \((b-a)l=0\), impossible. If \(z=a\), then \(U_{g_*}=0\) and the read \(qU_{g_*}=f\) gives \(f=0\), but the same ghost relation now gives \(-\delta l=0\) with \(\delta=b-a\ne0\), again impossible. Thus both overlaps are excluded, including the early zero-clock mask alternative.

## A true grade-six scalar condition, and the late numerical zero

The genuine \(A C^2\mathbf V-(J(X^2S))(\mathbf c)\in F_6\) has value \(-J(X^2S)(a)=-\kappa a^6/60\) at the first live row. At \(b\) its actual primitive read, before subtracting the scalar, is
\[
                    (A C^2\mathbf V)_b=a^2 j+(z+a)f .
\]
In fact \(\beta=0\), the only earlier support of \(\mathbf V\) is at \(a,z\), and \((z-a)qV_{g_*}=f\); this uses the actual row, not scalar order beyond its grade. Compare the two values on the genuine live \(F_6\) line \(X L_6'\). With \(x=b/a\) and the ratio for \(z/a\) above, the exact coefficient identity simplifies to
\[
                 (2x-1)L_6'(ax)=x^3(2x^2-6x+5)L_6'(a).
\]
For fixed nonzero \(a\) this is a degree-six polynomial equation in \(x\) with the always invalid root \(x=1\), so there are at most five distinct admissible clock ratios. Both \(\kappa,a\) are nonzero. In particular \(L_6'(b)\ne0\) because \(x\ne0\) and \(2x^2-6x+5>0\) on the reals. This genuinely uses grade six; it is not a prescription that \(A\) has ordinary scalar stage order six at either row.

If the late ghost has \(z=0\), the clock relation fixes \(x=2/5\), and the last equation is \(625 L_6'(2a/5)+584 L_6'(a)=0\). The exact scalar polynomial after removing a nonzero constant is
\[
             129888a^5-330000a^4+312000a^3-136800a^2+27800a-2015 .
\]
The exact Sturm replay counts three real roots, one in each open rational interval
\((1579/10000,1580/10000)\), \((7132/10000,7133/10000)\), and \((9321/10000,9322/10000)\). None is a root of \(L_6'\) by the exact polynomial gcd. This is a finite projection of the first two ordinary clocks, not an assertion that any of the three roots extends to a tableau or that the late-zero chart is fully excluded.

## Late amplitude and explicit coupling to the mixed reverse bridge

Write the unique affine genuine primitive correction as
\[
                      \mathbf W=(JS)(\mathbf c)+\mathbf h\,Q(\mathbf c).
\]
It is recovered on the first three distinct ghosts by
\(Q(d_i)=-(JS)(d_i)/h_i\), since \(\mathbf W\) was zero there. In particular it is checked independently of any reverse mass. Put \(m=f/l=(4b-3a)/b\). The actual two read equations \(q(z-a)V_{g_*}=f,\ qW_{g_*}=l\) give
\[
 h_{g_*}\,[e(z-a)+mQ(z)] = (z-a)S(z)-m(JS)(z).
\]
For \(z\ne0\) this fixes the literal late ghost amplitude, with a nonzero coefficient: the right side is exactly
\[
 \kappa a^4\frac{5x^2(x-1)^3(5x-3)(5x-2)}{54(2x-1)^4},
\]
which cannot vanish. Indeed \(x\ne0,1,1/2\), and \(x=3/5\) or \(2/5\) would make \(z=a\) or \(0\), respectively. If \(z=0\) here, all three early ghosts are nonzero clocks, so \(e=1\); the same equation rather gives the exact necessary \(Q(0)=-2a/7\), leaving the amplitude to other tests.

Now fix a candidate physical scalar grid satisfying one of the two reverse chronologies. The exact mixed ghost feeds from that chronology determine \(\chi=\alpha/\gamma\) and force \(\gamma\ne0\). **No degree-twelve scalar exactness is assumed**: their formula uses the actual unpaid \(\varepsilon_{12}=\sum_i b_i c_i^{12}-1/13\). Set
\[
             T_\chi(X)=\chi L_5'(X)+L_7'(X),\qquad
             K_\chi=T_\chi(b)-L_6'(b)T_\chi(a)/L_6'(a).
\]
With \(\ell_{g_*}=1/(h_{g_*}D_3(z))\), \(D_3\) the monic hull of the first three ghost clocks, ordinary causality \(A_{a,g_*}=0\) and the actual later read give
\[
   q=b\gamma\ell_{g_*}K_\chi,\qquad
   \gamma=\frac{l\,h_{g_*}D_3(z)}{bK_\chi W_{g_*}} .
\]
Here \(W_{g_*}=(JS)(z)+h_{g_*}Q(z)\ne0\) and \(K_\chi\ne0\), because \(qW_{g_*}=l\ne0\) is an actual grade-five primitive read. The remaining coefficients of the ordinary \((\mu,\nu,\alpha,\gamma,\eta)\) bridge are explicit:
\[
\begin{split}
 \nu\,a L_6'(a) &= \sum_{i\in{\rm first\ three\ ghosts}} A_{ai} c_i^2 h_i,\\
 \mu&=-\nu z-\gamma T_\chi(a)/L_6'(a),\qquad \alpha=\chi\gamma,\\
 10\kappa\eta-e\nu&=-\kappa a^5/[60 L_6'(a)] .
\end{split}
\]
The first equation is the genuine \(AC^2\mathbf h\) read. The nonzero-clock taps \(A_{ai}\) are their literal Lagrange integrals on the earlier distinct numerical sites (degree at most three), because \(A_{aa}=0\) and scalar grade five is exact. If one early ghost is at zero, its tap need not be separated from the live origin for this equation since its multiplier \(c_i^2 h_i=0\). The last equation is the exact grade-six scalar error of \(AC^2\mathbf V\) at \(a\) and its actual zero numerical value. Thus for fixed scalar-grid and admissible ghost geometry there are no undetermined linear mode coefficients; substitute these values in the remaining moment equations. This is a projection and necessary test, not a full real root elimination for all scalar nodes.

## Independent no-late cubic-fit obstruction

If all four ghosts occur before \(a\), and a nonzero \(S\in XP_2\) matches their four amplitudes, the same grade-three \(\mathbf V=S(\mathbf c)-\mathbf h\) is zero through all ghosts. The grade-five commutator at \(a\) makes its scalar shape and \(A_{aa}=0\) as before, with no assumption on \(L_6'(a)\). At \(b\) there is now no intervening late ghost: both \((C-aI)\mathbf V\) and \(A\mathbf V\) are numerically zero before \(b\). Their genuine grade-five exact reads give \(f=\beta(b-a)s,\ l=\beta j\). The same nonzero determinant \(fj-l(b-a)s\) contradicts these equations. This proves the claimed no-late subchart exclusion without requiring a genuine sixth scalar exactness assumption.

## Verification scope

The exact scalar replay independently checks the primitive determinant, clock and amplitude factors, and the late-zero Sturm projection. The companion Lean scalar module checks algebraic elimination of the second diagonal and the primitive determinant; the literal stage-space and chronological arguments remain analytic, with no full native order-twelve exclusion claimed.

    python3 -B verify.py
    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenOrdinaryGhostChronology
    lake env lean AuditDIRKOrderTwelveFifteenOrdinaryGhostChronology.lean

The typed consumer and source passed Lean/Mathlib 4.36.0 with only the standard axioms. No additional Mathlib-version pairing is claimed here.
