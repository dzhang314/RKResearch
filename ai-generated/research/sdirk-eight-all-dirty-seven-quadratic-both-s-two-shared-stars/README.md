# Both singleton endpoints, both shared doubled labels, star/star

Let a strict ten-stage SDIRK method over a characteristic-zero field have ordinary order at least eight, all ten literal quadratic defects nonzero, and exactly seven distinct clocks. Suppose both physical endpoint labels are singleton S, and both actual first-three prefixes are **S,D,D stars using the same two doubled labels**. This chart is impossible. Neither order of the two actual D labels in either star is assumed. One shared D label, an arithmetic prefix, or a prefix with a later singleton is outside this packet.

The [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) supplies four S labels, three D labels, the true quadratic singleton graph \(R\), and
\[
U(w,g)=L_4(w)-g(A_2(w)+Bg).
\]
Here \(A_2\) is quadratic at most and \(B\ne0\). The full distinct physical pairs make both residuals at each D distinct, and the actual reflected prefix uses the same graph with the true nonzero scale. The separate [one-extra-S census](../sdirk-eight-all-dirty-seven-quadratic-both-s-sss-arithmetic/README.md) already excludes three S at either end, but that result is not needed for this narrower star-star contradiction.

## A forced symmetric pair, even paid quadratic, and small field

Use \(y=x-1,\ H=2(m-1),\ m=1/(2\gamma)\), so the original first and last labels are \(0,H\), with reflected coordinate \(y'=H-y\). A true forward star requires the sum of the two known D labels to be \(2\); a true reverse star requires their original sum to be \(2H-2\). Since they are the same two labels, \(H=2,m=2\). In centered coordinate \(w=y-1=x-2\) the endpoints are \(-1,1\) and the two D labels are \(d,-d\), where \(d\ne0\), \(d^2\ne1\). Both original forward reads have defect \(r=(2-d^2)/2\ne0\), and both normalized reverse reads have the same \(r\), by their own literal star formulas. Let \(\lambda\) convert normalized reverse defects to original defects. Both literal copies of a D label have distinct actual defects \(r,\lambda r\), so \(\lambda\ne0,1\).

At either D, genuine Vieta gives \(A_2(\pm d)=-B r(1+\lambda)\), forcing \(A_2\) even. At the two S endpoints, the first row defect is \(1/2\), and the terminal one is \(\lambda/2\). Since \(L_4,A_2\) are even and \(\lambda\ne1\), these are distinct roots of the **same** quadratic in \(g\) supplied by \(U\) at \(w=\pm1\). Hence
\[
 L_4(1)=-B\lambda/4,\quad A_2(1)=-B(1+\lambda)/2,\quad
 L_4(d)=-B\lambda r^2=(2-d^2)^2 L_4(1).
\]
With \(L_4(w)=w^4-\tfrac{24}{7}w^2+\tfrac{48}{35}\), \(L_4(1)=-37/35\), the last relation is exactly \(4(d^2-1)(18d^2-49)=0\) after clearing. Thus \(d^2=49/18\) and \(r=-13/36\).

The true quintic \(\mathcal Q=L_3-F_*L_4\), proportional to the actual \(P R\) with \(P\) the D cubic, is odd: its antipodal D roots and \(L_4(d)\ne0\) eliminate the intercept of affine \(F_*\). With \(L_3=w^3-12w/5\), its slope is paid at \(d\), giving the exact factorization
\[
 \mathcal Q=\frac{w(18w^2-49)(203w^2+204)}{6253}.
\]
If the last D label were \(0\), the graph \(R\) would be even and \(R(-1)=R(1)=1/2\) would force \(\lambda=1\), already impossible. So its actual third D \(e\) satisfies the irreducible quadratic \(203e^2+204=0\), and the remaining graph roots are \(0,-e\). In the exact field \(\mathbb Q(e)\),
\[
 R(w)=\frac{w(w+e)}{2(1-e)},\quad \lambda=\frac{1+e}{1-e},
 \qquad B=-4L_4(1)/\lambda .
\]
The unique even \(A_2\) is specified by its above values at \(w^2=1,49/18\); no other hidden weights or roots are needed. This derivation is valid over arbitrary characteristic-zero fields. The negative value of \(e^2\) is not used as a sign argument.

## Actual fourth reads, not a numerical prefix search

The two shared D labels have both physical copies consumed by the two ends, and the physical endpoints are distinct singleton sites. The forward fourth row therefore belongs either to one of the two yet-unused S labels or to the third doubled label \(e\). The possible S labels are roots of the exact quadratic
\[
 J_S=\bigl[L_4-R(A_2+B R)\bigr]/(w^2-1).
\]
The actual recursion at row four uses the [pure physical fourth test](../sdirk-eight-all-dirty-seven-clock/README.md#literal-fourth-reads-including-singular-pivots). The interpolant through the three actual forward residual values is \(T_2(x)=(-x^2+4x-2)/2\) with \(x=w+2\), for either order of its two D rows. The actual second-defect ratio is \(\kappa=2-d^2=-13/18\), also the same in both orders. Substituting into the true scalar fourth read gives
\[
 \left(\tfrac{59}{39}w+\tfrac{37}{13}\right)g_4
    =\tfrac16 w^3-\tfrac12 w^2-w+\tfrac13.
\]
For an unused S substitute \(g_4=R(w)\) and take the exact gcd in \(w\) of this row with \(J_S\). For the actual D label \(w=e\), take the exact gcd in \(g_4\) of the affine row and \(U(e,g_4)\). Both gcds are one in the abstract \(\mathbb Q(e)\), so neither option can occur over any extension. Nothing is divided by a potentially zero affine fourth coefficient. The reverse phase is used through actual consumed pairs, not through a permutation of rows.

Run `python check_two_shared_stars.py` with SymPy 1.14. The candidate Lean scalar companion checks the symmetric evenness and Vieta factor gate only; the full rooted condition and fourth read proof are mathematical with exact replay. The general stage interval is unchanged.

The publication audit independently replayed the corresponding exact arithmetic; the new Lean companions here are draft scalar lemmas, not claimed kernel-checked in this release.
