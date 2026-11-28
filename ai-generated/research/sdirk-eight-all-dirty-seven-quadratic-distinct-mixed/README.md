# Both doubled endpoints force two literal arithmetic D,S,S openings

Assume an all-dirty strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field with exactly seven distinct physical clocks. Type D denotes a doubled clock, S a singleton. If both physical endpoints are doubled, then **both actual opening triples must have type D,S,S, with a true nonzero-tap arithmetic third row in each orientation**. In particular the four interior physical rows are all D. This is a chronology requirement, not a ten-stage exclusion or a change to the general 10–11 stage interval. All signed weights and all characteristic-zero fields are allowed.

Indeed the graph is genuinely quadratic by the [affine classification](../sdirk-eight-all-dirty-seven-affine-final/README.md) and its constant predecessor. The endpoint labels cannot be [shared](../sdirk-eight-all-dirty-seven-quadratic-no-shared-end/README.md). There is [no D,D,D at either end](../sdirk-eight-all-dirty-seven-quadratic-midpoint-vs-arithmetic/README.md), and [the endpoints cannot each have exactly one later D](../sdirk-eight-all-dirty-seven-quadratic-distinct-one-extra-d/README.md). The present packet excludes one with exactly one later D opposite D,S,S. Hence both are D,S,S, with their star options excluded by the [two singleton-pair star proof](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md). The unresolved both-D chart is therefore distinct endpoints and true arithmetic/arithmetic D,S,S. Other endpoint types and more than seven labels are not covered.

## Actual geometry, overlap and row reuse

Orient forward the prefix with exactly one later D, and reverse the D,S,S prefix by genuine weighted mirror. Normalize its common diagonal to one, let \(\ell=1/\gamma=2m,\ h=m-1\ne0,\ t=x-m\). The three D labels are \(-h,h,d\), and the [odd projection](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md) gives \(Q/B=L_3-\mu t L_4\), \(\mu\ne0\). Write \(R=rW\) with \(W\) monic:
- even: \(d=0,\ W=t^2-S,\ S=(21m^2h^2-15m^4)/(35h^2-21m^2)\), allowing Hermite \(S=0\) or \(S=h^2\);
- split: \(d\ne0,\ W=t(t+d),\ d\ne\pm h,\ \Theta(h,d)=35h^2d^2-21m^2(h^2+d^2)+15m^4=0\).
The denominator \(35h^2-21m^2\) is nonzero by \(\mu=(h^2-3m^2/5)/L_4(h)\ne0\). No division by \(W\) at a D label is used.

The actual forward extra D label is either \(h\) (opposite endpoint reused) or \(d\) (third label). If its own offset from the first clock is \(y\), its literal phase is one of A2, A3, S as in the [distinct one-extra-D pair table](../sdirk-eight-all-dirty-seven-quadratic-distinct-one-extra-d/README.md). Thus its known residue \(g_D\), the forward singleton coordinate \(s_f\) and normalized residue \(g_f\) are determined. The opposite star order shares the same literal pair data, and no \(u=2\) arithmetic exclusion from shared labels is used. Their actual graph value fixes \(r=g_f/W(s_f)\). Let \(\lambda\ne0\) convert normalized reverse residues to original. Write \(C=A_2+B R\).

In reuse, the two observed residuals at \(h\) are \(g_D,\lambda/2\); their product gives \(\beta=B\lambda=-2L_4(h)/g_D\). They must be distinct. The first forward residue at \(-h\) is \(1/2\), so \(A_2(-h)=2L_4(h)-B/2\). Together with \(A_2(h)=-B(g_D+\lambda/2)\) and \(C(s_f)=L_4(s_f)/g_f\), these determine three quadratic values at distinct clocks.

In the third-label case there is no boundary overlap. The one observed residue at each D label is \(1/2,\lambda/2,g_D\) at \(-h,h,d\). Its actual quartic equation gives \(A_2(t)=L_4(t)/g-Bg\) at that label, so this gives three values linearly in the unknown \(B\), with no degeneracy assumption about that affine fit.

## Reverse star: exact axis and six finite branches

Two distinct reverse star S clocks have equal residue. In original centered coordinates their axis is \(c=h-1\), so \(W=(t-c)^2-S\). In the even case that forces \(h=1,m=2,d=0,S=156/49\). In the split case, \(d=2-2h\) and substituting in \(\Theta\) gives the irreducible
\[
       50h^4-262h^3+377h^2+60h-69=0,\qquad S=(h-1)^2 .
\]
These shapes force \(S\ne0\) here by exact field check, not an assumption skipping Hermite options. Retain all choices of reuse or third label and all genuine phases. Six actual branches survive their initial distinct-label and nonzero-residue tests.

Let \(v\) be the reverse star gap and \(X=(v-1)^2\). The two true reverse S coordinates are \(t=c\pm\sqrt X\), their normalized residue \(\tau=(2-X)/2\), and \(\mu_*=\lambda\tau=r(X-S)\) is known from their fixed \(R\) value. All square-root language represents the algebraic pair equation \((t-c)^2-X=0\), with no sign choice.

In reuse let \(M=\mu_* C\). Its three known values at \(-h,h,s_f\) are
\[
 M(-h)=2\mu_* L_4(h)-\beta\tau/2+\beta r\tau W(-h),\quad
 M(h)=-\beta(\tau g_D+\mu_*/2)+\beta r\tau W(h),\quad
 M(s_f)=\mu_*L_4(s_f)/g_f.
\]
The two actual S equations are \(L_4-M=0\) at the pair; reduce modulo \((t-c)^2-X\). Their exact gcds in \(X\) are units after actual nonzero guards.

In the third-label case use \(P_*=\tau\mu_* C\) and scalar \(B_*=\mu_*B\). The three paid D values of \(P_*\) are affine in \(B_*\):
\[
 \begin{split}
 P_*(-h)&=2\tau\mu_*L_4(h)+B_*\tau[rW(-h)-1/2],\\
 P_*(h)&=2\tau^2 L_4(h)+B_*[\tau rW(h)-\mu_*/2],\\
 P_*(d)&=\tau\mu_* L_4(d)/g_D+B_*\tau[rW(d)-g_D].
 \end{split}
\]
The forward singleton buys the fourth value \(\tau\mu_*L_4(s_f)/g_f\), and the two reverse singleton equations reduce \(\tau L_4-P_*\) at the actual pair. Add the corrected [normalized quadratic trace](../sdirk-eight-all-dirty-seven-quadratic-five-d-prefix/README.md), \(2\sum1/g_i=\ell\sum b_i/g_i\), written \(c_{\rm tr}/r+\mathcal T(A_2)=0\). Multiplying by \(\tau\mu_*\) gives
\[
 \tau\mu_* c_{\rm tr}/r+\mathcal T(P_*)-B_*\tau r\mathcal T(W)=0 .
\]
This is an extra affine row. The exact gcd of the augmented minors is a unit after the required \(X\)-guards. They discard only literal nonzero values \(\tau\), \(X\), \(X-1\), \(X-S\), known S/D clock differences, and on reuse the necessary residual difference of the overlapped D pair. No affine rank coefficient is divided out.

## Reverse arithmetic: a cubic ratio and specialization-safe resultants

For the true reverse arithmetic gap \(v\), put \(s_2=h-v,s_3=h-2v\) for its original S labels, and
\[
 \kappa=1+2v-v^2,\quad D=-2+v+4v^2-v^3,\quad
 \widehat q=D-v(v-2)(3v-2).
\]
The actual reverse residues are \(\kappa/2,\kappa\widehat q/(2D)\). For \(W(t)=t^2+b t+c_0\) the exact ratio after cancelling only the actual nonzero \(v\kappa\) is
\[
 \mathcal R=D(2h+b-3v)-(v-2)(3v-2)W(s_2)=0.
\]
Here the leading quartic terms in \(v\) cancel. Also \(\mu_*=\kappa\lambda=2rW(s_2)\) is known.

In reuse let \(\widehat C=\kappa\lambda C\). Its known three values at \(-h,h,s_f\) are exactly the \(M\)-formulas in the star section with \(\tau\) replaced by \(\kappa\) and with the new \(\mu_*=\kappa\lambda\). Evaluate the two reverse S equations
\[
            2L_4(s_2)-\widehat C(s_2)=0,\qquad
            2D L_4(s_3)-\widehat q\widehat C(s_3)=0 .
\]
These are exact genuine scalar equations, not calculated by fitting a tableau.

In the third-label case let \(P_*=\kappa\mu_* C\), \(B_*=\mu_*B\). The same three paid D rows displayed for the star apply with \(\tau\) replaced by \(\kappa\), since \(\mu_*=\kappa\lambda\). The three actual singleton equations are
\[
 P_*(s_f)=\kappa\mu_*L_4(s_f)/g_f,\quad
 P_*(s_2)=2\kappa L_4(s_2),\quad
 \widehat q P_*(s_3)=2D\kappa L_4(s_3).
\]
All augmented minors of the two-column affine system in \(B_*\) must vanish, including when their coefficients of \(B_*\) are all zero. This outer projection already suffices; no trace or fourth mask is required for the arithmetic case.

In every literal phase the exact computation clears only denominators supported by the nonzero stage guards. With the ratio and each singleton equation or augmented minor, take integer resultants in \(v\). For split data eliminate \(d\) using \(\Theta(h,d)\) **separately** for each resultant and only then take the univariate gcd in \(h\). For even data project directly to \(h\). This does not assume any specialized leading coefficient nonzero, including at a Hermite graph. The projected gcds after true \(h\)-guards are all units. The exact degree triples or pairs in the nine genuine cases are:
- even reuse A2: \(27,63\); even reuse S: \(18,54\); even third A3: \(96,69,93\); even third S: \(78,57,75\);
- split reuse A2: \(70,108\); split reuse S: \(52,90\); split third A2: \(210,164,198\); split third A3: \(206,180,194\); split third S: \(158,112,146\).

The other cases fail a literal S-label guard identically (e.g. a forward reuse A3 has its S clock at the center, which is D if even and a graph-zero clock if split). No additional rank or order-of-clock hypothesis is used.

## Replay and scope

Run `python check_distinct_mixed_star.py` and `python check_distinct_mixed_arithmetic.py` with SymPy 1.14 and python-flint 0.8. Both import the sibling `scalar_geometry.py`. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticDistinctMixed.lean) stages the general quadratic reverse ratio identity only; exact traces and eliminations are paper statements and replay code, not a new stock or end-to-end native theorem. No finite-characteristic transfer is used.
