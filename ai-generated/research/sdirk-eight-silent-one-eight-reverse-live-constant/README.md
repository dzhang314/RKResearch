# Constant nine-site reverse numerator: deflation, quartic exclusion, and a mixed quintic gate

Consider strict ten-stage SDIRK8 over a characteristic-zero field, with physical stage one the sole nonzero quadratic-defect row and ordinarily weight zero. Exactly eight physical rows have nonzero ordinary weights, at distinct clocks. The remaining ordinarily silent row \(\zeta\ne1\) has actual reverse read \(w_\zeta\ne0\), at a clock \(z\) distinct from all eight ordinary clocks. The first silent stage may share a clock, since \(w_1=0\). For **constant nonzero nine-site reverse numerator \(T\)**, this packet gives a deflated Bézout identity and an exact two-parameter regular reduction. It excludes the whole \(\deg S\le4\) subchart, and separately excludes the conditional pure quintic \(S\propto L_5\). Mixed quintics and the nonconstant \(T\) charts remain open here. No real ordering is used; the unrestricted **10–11** interval stays unchanged.

## 1. Deflate only the actual extra reverse clock

Use the [actual reverse identities](../sdirk-eight-silent-one-six-detected/README.md) and [saturated support](../sdirk-eight-silent-one-seven-distinct-anchors/README.md). The terminal and penultimate are ordinary, \(x=c_{10}=1-\gamma\), \(c=c_9=x-\gamma u\), \(u\ne0\), \(k=1+2u-u^2\). Here \(k\ne0\): otherwise the scalar zero sum of the actual reverse row \(\boldsymbol w\), supported only at clock \(x\), would contain only \(w_{10}=-\gamma^2b_{10}\ne0\). The actual row \(\boldsymbol h^{\mathsf T}B=\boldsymbol wP_1(C)\), with \(P_1\) nonzero affine, forces \(P_1(z)=0\) since \(b_\zeta=0,w_\zeta\ne0\). Thus \(P_1(X)=\mu(X-z)\) with \(\mu\ne0\).

Let \(D\) be the monic nodal polynomial of the eight ordinary clocks and \(D_9=(X-z)D\). Interpolate
\[
 T(c_i)=D_9'(c_i)w_i,\qquad S(c_i)=D_9'(c_i)w_i h_i
\]
on the nine distinct reverse sites, using their individual contributions. The six scalar reverse moments and three mixed reverse moments imply \(\deg T\le2,\deg S\le5\). Suppose \(T\) is constant; it is nonzero from the terminal. Then \(h=S/T\) is an actual polynomial profile at **all nine** sites, including \(\zeta\). At ordinary sites
\[
 D'(c_i)b_i h_i=\mu T,
\]
since \(D_9'(c_i)=(c_i-z)D'(c_i)\). In particular every ordinary \(h_i\ne0\); there is no such conclusion for the ordinarily silent amplitude, and the derivation did not assign it a virtual ordinary value.

Write \(I(X^j)=1/(j+1)\), \(W_F(X)=I_Y((F(X)-F(Y))/(X-Y))\). Scalar precision is only through degree seven. This suffices for \(I(X^j S)=0\) for \(0\le j\le2\), by the paid \(b\)-moments of \(\boldsymbol h\). Let \(L_j\) be shifted Legendre polynomials, \(L_3=20X^3-30X^2+12X-1\), \(L_4=70X^4-140X^3+90X^2-20X+1\), and \(L_5=252X^5-630X^4+560X^3-210X^2+30X-1\). These three span the indicated kernel in degree at most five; this uses rational nonzero moment norms, not positivity in the coefficient field. If \(\deg S\le4\), precision seven gives the additional \(j=3\) vanishing, so \(S\propto L_4\). It is nonzero by the deflated ordinary identity. **For a quintic, the integrated moments at \(j=3,4\) do not follow from scalar precision seven.**

Precision seven yields \(W_D(c_i)=b_iD'(c_i)\) at every ordinary clock, since the actual cardinal numerator has degree seven. Hence
\[
 S W_D-D W_S=\mu T^2 . \tag{1}
\]
Both sides agree at all eight ordinary clocks. For the degree check, express the left side by integrating
\[
 \frac{D(X)-D(Y)}{X-Y}S(Y)-\frac{S(X)-S(Y)}{X-Y}D(Y).
\]
The first term has total degree in its divided difference at most seven, and its \(Y\)-exponents \(0,1,2\) integrate to zero against \(S\), so its integrated degree is at most four. The second term's \(X\)-degree is at most four. If \(S\propto L_4\), the integrated degree is at most three, using only the justified \(j=3\) vanishing. This proves (1) without any precision above seven.

For implementation use any common scaling \(H\) of \(S\), such as the physical-clock polynomial giving \(h_i/\gamma^3\). For \(H\) monic of degree \(d\), (1) forces \(\gcd(H,W_H)=1\), and
\[
 D=H U_{8-d}+\lambda V,\qquad
 V=W_H^{-1}\pmod H,\quad \deg V<d,\quad U_{8-d}\text{ monic},             \tag{2}
\]
with an unknown scalar \(\lambda\); its sign absorbs the sign in (1). Alternatively, at \(n\) distinct known ordinary pegs, take their nodal polynomial \(E\) and set \(D=ER\), \(R\) monic of degree \(8-n\). For a quintic the four nonconstant coefficients, \(X^1,\ldots,X^4\), of \(HW_{ER}-ER W_H\) are homogeneous linear equations in the coefficient vector of \(R\). With five pegs this gives a necessary \(4\times4\) zero determinant. With six pegs use all \(3\times3\) minors of its four-by-three matrix. This is a division-free alternative to (2), not using any inverse of a clock evaluation.

## 2. Two literal anchors and the guarded mixed-quintic chart

Use actual normalized literal clocks \(A_0,B_0\), literal normalized amplitudes \(H_a,H_b\), and actual fourth \(s=c_4/\gamma\). Their physical clocks are \(\gamma A_0,\gamma B_0,\gamma s\). Both front amplitudes are known and nonzero from the two exact literal front phases, regardless of whether one is ordinarily silent. The fourth amplitude is the actual three-predecessor polynomial \(H_4(s)\). The recurrence
\[
 5L_5+4L_3=9(2X-1)L_4
\]
puts \(H\) in the form \(L_4(\alpha+\beta X)+\eta L_3\). The first two evaluation rows on \(L_3,L_4,L_5\) have rank two: if proportional with both quartic values nonzero, the recurrence would force equality of the distinct physical clocks; if one quartic value vanishes, the other would have to vanish too, since \(L_3,L_4\) have no common root. The two literal quartic values have exact polynomial gcd one in \(\gamma\) over \(\mathbb Q(t)\), \(2t^2=1\), for both front phases. The replay checks this gcd.

If the two front quartic values \(A_4=L_4(\gamma A_0),B_4=L_4(\gamma B_0)\) are nonzero, let \(p_0\) be the affine polynomial in normalized clock \(Y\) interpolating \(H_a/A_4,H_b/B_4\), and \(p_1\) interpolate \(L_3(\gamma A_0)/A_4,L_3(\gamma B_0)/B_4\). The profile at normalized clock \(Y\) is
\[
 H(\gamma Y)=L_4(\gamma Y)p_0(Y)
       +\eta\big(L_3(\gamma Y)-L_4(\gamma Y)p_1(Y)\big).
\]
At actual fourth, \(H(\gamma s)=H_4(s)\). Clear the one known denominator \((B_0-A_0)A_4B_4\), obtaining \(\eta V(\gamma,s)=P(\gamma,s)\). The padded factors \(s-A_0,s-B_0\) divide both polynomials exactly and are excluded by actual distinct sites. The reduced \(P,V\) have \(s\)-degree three. If \(V\ne0\), their ratio determines \(\eta\), leaving exactly the two parameters \(\gamma,s\) for the regular profile. If \(V=0\), retain \(P=0\) and a free shape parameter \(\eta\); the exact \(s\)-resultant has \(\gamma\)-degree 57, and after removing only \(\gamma^{12}A_4^3B_4^3\) its degree is 21 in each front phase. This is a finite *diagonal* projection of this exceptional chart, not an exclusion or claim that its fourth-clock fiber is always finite.

If one front quartic is zero, that clock is fixed at a Gauss root, and its nonzero \(L_3\) fixes \(\eta\). The other literal clock fixes the affine part at one point. The actual fourth fixes its slope if its own quartic value is nonzero. If fourth is also quartic-zero, retain the actual fourth equation and the slope separately. Neither early Gauss chart is removed by the degree-21 resultant. The zero quintic-leading and pure-\(L_5\) cases are handled separately below; general mixed quintics remain.

For any such profile the actual rear identities give the same homogeneous scalar tail equations as in the [constant-profile reverse chronology](../sdirk-eight-silent-one-seven-distinct-constant-nonliteral/README.md), evaluated on \(H\) instead of \(L_4\). With eight ordinarily active, the third rear clock \(d=c_8\) is \(x-\gamma(2-u)\) or \(x-2\gamma u\) (star or arithmetic). If the literal silent is physical 2, 3, or 4, its known \(z\) must also satisfy \((x-z)H(c)=k(c-z)H(x)\). For a nonliteral silent at stages 5–7, the same equation solves for \(z\): the coefficient \(kH(x)-H(c)\) cannot vanish, since the right-hand side after moving the \(z\) terms would then be \(kH(x)(c-x)\ne0\). If physical eight is ordinarily silent, its actual reverse read gives \(2(z-x)=\gamma k(u-2)\), and the cleared gap is
\[
 (u-2)H(c)-(2u+k(u-2))H(x)=0 .
\]
Physical fifth is a missing ordinary root unless it is the actual ordinarily silent row; when silent its clock is the above \(z\), not a missing ordinary root. These equations, the five/six-peg condition, and the actual fifth test below are necessary without presuming the mixed shape solved.

There is a second useful parameter check. If \(H=aL_3+bL_4+c_5L_5\) with \(c_5\ne0\), define scalar errors \(\epsilon_j=I(X^j)-\sum_i b_i c_i^j\). The paid \(j=3,4\) ordinary defect reads and precision seven give
\[
 \begin{split}
 252c_5\epsilon_8&=a/140,\\
 252c_5\epsilon_9+(70b-630c_5)\epsilon_8&=a/70+b/630 .
 \end{split}
\]
These use the exact \(L_3\) moments at three and four and \(L_4\) moment at four, checked by the replay. In particular \(H\propto L_5\) is equivalent here to **genuine ordinary scalar precision through degree nine**, not a consequence of order eight.

## 3. Full quartic exclusion and conditional pure quintic control

For \(H\propto L_d\) with \(d=4\) or \(5\), the two actual literal reads give a monic degree-\(d\) diagonal equation. Its actual fourth equation is \(H_a L_d(\gamma s)-L_d(\gamma A_0)H_4(s)=0\). Cancel only its literal padded roots \(s-A_0,s-B_0\). The quotient has degree \(d-2\). The three literal gap equations use actual reversed star, ordinary arithmetic, or the ordinarily silent eighth just described. Remove only \(u(u-1)(u-2)\), \(u^2\), or \(u\), respectively; these are exact pads at forbidden true rear collisions. The full gap degrees are \(2,5,4\) for \(L_4\) and \(2,6,5\) for \(L_5\). The degree-two star bound follows from cancellation of the highest opposite-clock terms before the cubic pad. Reduced diagonals, fourth polynomials, and gap polynomials retain all of these degrees.

There are six prospective pegs (actual \(2,3,4,8,9,10\)); omit the one ordinarily silent among them, if present. Thus at least five literal **ordinary** pegs are known. For \(L_5\), use the five-row determinant from (2): the columns are \(H(v),vH(v),v^2H(v),V(v),v^3H(v)\) at each peg \(v\), with all five-row minors when there are six pegs. For \(L_4\) and six ordinary pegs, use the corresponding six-row augmented determinant with extra \(v^3H(v)\) among the coefficient columns and \(v^4H(v)\) last. For \(L_4\) and only five ordinary pegs, the five-by-five coefficient matrix in (2) has unit determinant in the full reduced algebra. Cramer's rule reconstructs \(D\); its missing cubic is \(D/E\), including the actual ordinarily active fifth.

The extra constraint for this cubic is the determinant on actual rows **2–5** of the four columns \(\boldsymbol h,C\boldsymbol h,A\boldsymbol h,\boldsymbol\tau_4\), \(\boldsymbol\tau_4=A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\). The saturated \(F_4\) has dimension four and contains the first coordinate axis (all of \(W_3\) vanishes individually there). Thus its restriction to physical rows other than first has rank at most three. This is an actual four-row determinant, not a claim that the pure-four restriction to ordinary axes has rank two. It holds if a literal in those four rows is the physically silent \(\zeta\). At actual fifth \(Y=c_5/\gamma\) its earlier known non-first clocks \(A_0,B_0,s\) are distinct, and the three taps to them are solved from the moments
\[
 Y-1-2H_f,\quad Y^2/2-Y-2H_f,\quad Y^3/3-Y^2-4H_f/3,
\]
where \(H_f\) is its normalized cubic amplitude. The strict tap to physical first is already \(2H_f\). These uniquely determine the actual fifth \(A\boldsymbol h\) and \(\boldsymbol\tau_4\) reads. The prospective fifth determinant is necessary in the normalized missing cubic. The rest of the gate uses the actual affine tail read at \(z\) for silent physical 2, 3, or 4; when five is ordinary it is not combined with any silent weight.

At \((1129,t=203)\), all 18 combinations of literal front, literal rear, and actual ordinarily silent placement pass: when eighth is ordinary, test physical \(2,3,4\) separately and physical \(5,6,7\) together (all six pegs ordinary); when eighth is silent it has the separate literal rear equation. For each literal front star there are two full reduced diagonal components and for each arithmetic front one. In all, 27 full components pass per polynomial profile. The finite quotients use complete monic diagonal, fourth, and gap bases. All inversions in the replay are checked as units or reproduce fixed rational exact coprimalities. A determinant span generating a unit on every reduced component cannot vanish at a characteristic-zero point of these finite algebras: a maximal ideal of the finite integral local model over the chosen residue would otherwise persist. No reduced collision, vanishing weight, or reduced branch is dropped. The result for \(L_4\) applies unconditionally within \(\deg S\le4\); the \(L_5\) check is only for the actual pure-quintic profile, equivalently the extra precision condition above.

## Replay and native scope

Install sympy==1.14.0 and python-flint==0.9.0; run **python3 check_eight_reverse_live_constant.py** with the declared sibling research folders. The replay verifies the exact front rank-loss projection, the rational Legendre constants, all quartic components, and the conditional pure-quintic controls. The [native Lean file](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveReverseLiveDeflation.lean) formalizes the nodewise deflation, actual silent-eighth read, quintic moment arithmetic, and cleared front-rank recurrence on Lean/Mathlib 4.36.0. Saturation, interpolation degree bounds, and finite arithmetic replays are source-level.
