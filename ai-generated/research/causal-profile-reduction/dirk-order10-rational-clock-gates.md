# Rational clock cuts for the eleven-stage DIRK10 endpoint

The exact real method does not give a rational method. This note reduces the **single numerical dirty clock** branch over \(\mathbb Q\) to a split clock problem, excludes all constant and shared terminal polynomials and the pole at one, and rules out the surviving variable-pole chart up to primitive height \(10^9\) on the ratio of the first two exterior clocks. It does not prove or disprove the unrestricted rational eleven-stage endpoint. Multiple numerical dirty clocks are not covered.

The six-node Lobatto ordinary aggregate is impossible over \(\mathbb Q\). Its four interior labels are the roots of
\[
 \Phi(X)=1-14X+56X^2-84X^3+42X^4.
\]
All four have nonzero Lobatto weight, whereas \(\Phi\) has no rational root: modulo 11 it has neither an affine root nor a root at projective infinity. Use a primitive numerator/denominator pair for this reduction. This is not an assertion that all possible rational quadratures are Lobatto.

## 1. A uniform rational cut for prescribed terminal poles

Use the valid low-grade parts of the [one-clock band](dirk-order10-one-physical-dirty-clock.md), not its withdrawn degree-five donor test. Write \(c=A1\), \(C=\operatorname{diag}(c)\), \(\beta=b^\top\),
\[
 g=Ac^2-c^3/3,\quad h=(A-\xi/2)g,\quad H=X\Phi,\qquad
 e_T=H(c)+\delta g+L(c)h,\quad \deg L\le1.
\]
Here \(T\) is the physical terminal row, and every nonzero entry of \(g\) is at the same numerical clock \(\xi\). When the nonzero \(g\)-values are not constant, the actual clock-indicator argument of the band gives the Lobatto ordinary aggregate; this uses no degree-five donor step. Thus this is impossible over \(\mathbb Q\).

In the constant case let \(a,b,u\) be the **first three distinct nonzero nonterminal exterior clocks** (exterior means \(g=0\)). There are at least three by the clock count in that band. The genuine paired cut, using only degrees at most four, makes the primitive \(J=I P\) a common nonzero multiple \(\lambda h\) there, where \(I\) is anchored integration and
\[
 P=X(X-a)(X-b),\qquad u(4ab-a^2-b^2)=ab(a+b).
\]
In particular \(a,b,u\) are distinct and nonzero; put \(s=a+b,\ t=s/u,\ p_0=ab\). Then \(s,t\ne0\) and \((6-t)p_0=s^2\), so \(t\ne6\). At \(t=2\) the clocks \(a,b\) would agree; at \(t=3\) their difference would have negative square. At \(t=3/2\) one of \(a,b\) equals \(u\), since the quadratic \(X^2-sX+p_0\) evaluates to zero at \(u\). These implications are checked in Lean for rational clocks without a sign assumption on the clocks.

The choice \(L=0\) would make all nonzero nonterminal exterior clocks roots of \(H\), impossible over \(\mathbb Q\). For \(L\ne0\), put \(M=-L/\lambda=e+fX\) and \(D=(X-u)P\). The actual terminal identity at \(a,b,u\) yields \(H=MJ\) there, and both sides vanish at zero. Thus
\[
 H=(r+zX)D+MJ.
 \tag{1}
\]
The five positive-degree coefficients, **including the quadratic coefficient**, give
\[
\begin{split}
 E(s,t)&=420s^4-1008s^3+1008s^2-504s+108\\
       &\quad+(-168s^2+252s-108)t+(33-28s)t^2-3t^3=0,\\
 5s^3(2t-3)e&=12 A_0(s,t),\qquad
 5s^4(2t-3)f=-6 B_0(s,t),
\end{split}
\]
where the literal polynomials \(A_0,B_0\) are in the [exact replay](check-dirk10-rational-clock-gates.py) and the [native scalar proof](../../lean/RKCert/ReviewedNative/DIRKOrderTenRationalPoleScalars.lean).

The conditions for a pole at zero, a pole at one, and a constant polynomial are respectively \(A_0=0,\ 2sA_0-B_0=0,\ B_0=0\). The standard-kernel Lean certificate proves explicit integer Bézout identities in \(s,t\): the left side in each row is a polynomial combination of \(E\) and the indicated second equation.

| Second equation | Bézout polynomial up to a nonzero scalar | Modulus ruling out every rational root of \(R\) |
| --- | --- | --- |
| \(A_0=0\) | \((t-6)(t-2)R_8(t)\) | 23 |
| \(2sA_0-B_0=0\) | \((t-6)^2(t-3)R_{11a}(t)\) | 11 |
| \(B_0=0\) | \((t-6)^2(t-3)R_{11b}(t)\) | 11 |

Every residue test includes the projective infinity point; each is applied only to a rational scalar, not to unknown tableau coefficients. The listed linear factors have already been ruled out by the split-clock guards. The Python replay independently checks full Sylvester determinants, rather than using the Lean Bézout witnesses. Since the only rational zero of \(H\) is zero, this also excludes every shared \(H/L\) pole over \(\mathbb Q\).

For the residual affine nonshared pole away from zero and one, any active dirty support forces the [Lobatto aggregate by the paid terminal debit](dirk-order10-one-dirty-terminal-debit.md), so it is impossible over \(\mathbb Q\). With only invisible dirties the [regular saturated census](dirk-order10-invisible-constant-three-heads.md) applies. There is exactly one invisible cubic row, and the nine nonterminal exterior rows have distinct clocks (possibly including a nonterminal copy of one); all eight nonzero exterior rows are active with \(h\ne0\). The layout begins \((0,\xi,a,b,u,y,w,\ldots,1)\). In particular, this reduction has not assumed the absence of a second physical row at clock one.

## 2. Necessary front and split suffix

On those nine exterior rows the actual \(G=\beta(1-C)^2A-\beta(1-C)^3/3\) is live. The regular atlas gives \(E_5^\perp=\langle G,GC\rangle\) and \(\beta h\) proportional to \(CG\). The terminal-out annihilator of \(E_4\) is \(\langle G,GC,GC^2\rangle\): \(E_4\) has rank seven and does not contain \(e_T\), by multiplying its exterior profile \(Q(c)+\theta h\) by \(M(c)\). A resulting polynomial of degree at most five cannot vanish at nine distinct labels unless it is zero. Evaluation at the nonshared pole first kills \(\theta\), then the invisible cubic row kills any remaining \(g\) coefficient.

Let \(\mathcal R=CA-AC-A^2\). The forward cut
\(V=P(c)-P(\xi)g/\gamma\), \(\gamma=\xi^3/6\),
has \(\mathcal R V=0\) and first live row 5; hence \(d_5=0\). Choose a nonzero actual reverse row \(W_3=\beta Q_3(C)+\alpha G\), with \(Q_3(1)=0\) and \(\deg Q_3\le3\), cancelling rows 8,9,10 and therefore also the terminal. This is possible by dimension four; \(Q_3\ne0\) since the three killed exterior coordinates are G-live. Its \(\mathcal R\) product annihilates \(E_4\) by the paid grades \(3+2+4\). It is terminal-out and has the same three exterior zeros, forcing \(W_3\mathcal R=0\) in the preceding three-dimensional annihilator. The [crossed pivot and gap-two theorems](dirk-order10-three-stage-overlap.md) pin its first reverse live coordinate to row 7, give \(d_7=0\), and give a nonzero \(d=d_6\), two live hops and distinct \(u,y,w\).

On the exterior \(AV=J-H/M=-(r+zC)D/M\). The overlap yields \(k=1-(y-u)/d\ne0,1\), with \(V_4=(C-u)V+kAV\) zero through row 6; its scalar profile is \(P_4=D+kJ\). Writing \(R=r+zX\), its exterior numerator over \(M\) is \(D(M-kR)\). The affine \(M-kR\) is not identically zero: otherwise \(V_4\) would be supported only at the terminal (the invisible row is in its strict zero prefix), which \(e_T\notin E_4\) and the nonzero grade-four profile exclude. Thus it has the single root \(y\) and \(y_D=kz-f\ne0\). Now \(A V_4\) vanishes through row 7. Its exterior numerator is degree at most six and vanishes at \(0,a,b,u,y,w\). Interpolation on the nine labels gives
\[
 M I P_4-\sigma(X-w)D(M-kR)=\Lambda H,\quad \deg\Lambda\le1.
\]
Reduction at the pole of \(M\), using \(R D=H\ne0\) there, gives
\(I P_4-\sigma(X-w)P_4=\lambda' H\) for a scalar \(\lambda'\). If \(\sigma=0\), the linear coefficient and \(H'(0)=1\) would give \(\lambda'=0\) and \(P_4=0\), impossible.

The independent basis \(D,XD,J,XJ\) and literal primitive identity
\[
 I J=B XD+N J+E_0 XJ,\qquad
 B=\frac{t}{10(3-2t)},\ N=\frac{s}{5(3-2t)},\
 E_0=\frac{3-4t}{5(3-2t)}
\]
then give, with \(S=1+(k-1)E_0\), \(L_k=k(k-1)B-S\),
\[
\begin{gathered}
 y_N=e-rk,\quad y_D=zk-f,\quad
 w_N=r L_k,\quad w_D=zS-(k-1)B f,\\
 y=y_N/y_D,\quad w=w_N/w_D,\qquad
 K=y_D[-u+(k-1)N]+(rk-e)L_k=0.
 \tag{2}
\end{gathered}
\]
In fact \(w_D=\sigma y_D\ne0\). For example the four coefficient equations are
\(\lambda' r=\sigma w,\ \lambda' z=(k-1)B-\sigma,\
 \lambda'e=-u+(k-1)N+\sigma wk,\ \lambda'f=S-\sigma k\).
They give (2) without dividing by \(z\), \(r+z\), or the slope of any auxiliary interpolation.

**Early unit heads are impossible over \(\mathbb Q\).** If \(a=1\) (or \(b=1\) by interchange), \(b^3 E(1+b,4-b-1/b)\) is \((b+1)^2\) times a degree-five polynomial with no affine or projective root modulo 13. If \(u=1\), \(E(t,t)=(3t-2)(4t-3)(5t-3)(7t-6)\); the rational split condition \((t-2)/(t-6)\) square discards all but \(t=2/3\).

At \(t=2/3\), \(E(s,2/3)=28(3s-2)^3(5s-2)/9\). At \(s=2/5\), \(K=-4(125k^3-100k^2-87k+1314)/225\), whose cubic has no affine or infinite root modulo 13. At \(s=2/3\), \(K=-12(k-6)(k-3)^2/25\); \(k=6\) kills \(y_D\), while \(k=3\) gives \(y=w=1\), contradicting literal distinctness. Thus the published front's horizontal parameter \(t=2/3\) is impossible over \(\mathbb Q\) even if an extra unit row is allowed.

If \(y=1\), \(k=(e+f)/(r+z)\) (the denominator is nonzero by \(M(1)\ne0\)). If \(w=1\), the same four coefficient equations give
\[
 (k-1)B(rk+f)=(r+z)S,\qquad
 (r+z)(1-u)=(k-1)[B(e+f)-(r+z)(N+E_0)].
\]
Here \(r+z\ne0\) by \(k\ne1\) and \(r,B,\sigma\ne0\). The bracket is nonzero since \(u=1\) was just excluded. Substitute the solved \(k\) in (2) for \(y=1\), or in the first quadratic for \(w=1\). After clearing the displayed denominators and reducing in \(s\) modulo \(E\), the verified Sylvester determinants have possible rational zeros only
\[
 t\in\{0,2,3,6,3/2,3/5,3/4,2/3\}.
\]
The two residual factors for \(y=1\) have degrees 7 and 12 and no roots modulo 11; for \(w=1\) they are quadratic and have no roots modulo 17. The excluded values \(3/5,3/4\) give nonsquare discriminant ratios \(7/27,5/21\). This disposes of the two early unit-head cases over the rationals, not over arbitrary real extensions. The replay checks the *full* cleared elimination identities via Sylvester matrices and a degree-bounded exact interpolation; no symbolic factorization is taken as an oracle.

**Actual reflected quartic and the split test.** Since \(w\ne1\), the reverse column cutoff from the same overlap applies without a degenerate scalar profile. Set
\(W_4=W_3(C-w)+k'W_3A\), \(k'=(w-y)/d-1\).
It vanishes beyond row 5. Its degree-four profile
\(Q=(X-w)Q_3+k'I^*Q_3\), where \(I^*\) is integration to one, is anchored at one and nonzero: if it were zero, differentiating gives
\((X-w)Q'_3+(1-k')Q_3=0\), making \(Q_3\) a single power of \(X-w\), impossible at one. The actual remainder is in \(\langle G,GC\rangle\) by the paid reverse primitive rule.

For every anchored \(P_0\) of degree at most four satisfying \(P_0(a)/h_a=P_0(b)/h_b\), subtract the matching multiples of \(h,g\) to get an actual column zero through row 4. Its \(A\)-pairing with \(W_4\) vanishes by \(d_5=0\); its pairing through \(C-u\) vanishes by the single overlap clock \(u\). Thus the two paid scalar functionals \(\int Q I P_0\) and \(\int Q(X-u)P_0\) are multiples of the single ratio functional. The first multiplier cannot vanish, by the nonsingular four-moment form for \(X^2(1-X)\). On powers \(1\le j\le4\) those ratio reads are a common nonzero multiple of
\[
 ((s^2-3p_0)/p_0^2,\ s/p_0,\ 3,\ 2s)_j.
\]
The \(X^2\) read fixes the ratio of the second multiplier to the first as \(5-6/t\); the \(X\) read then fixes the remaining first moment. Up to nonzero scale, the first four moments \(\int X^jQ,\ j=1,2,3,4\), are
\[
 ((6-3t)(6-t)(3-t),\ 2s(6-t)(3-t),\ 3s^2(6-t),\ 12s^3).
\]
The fixed shifted Beta inverse in the checker gives \(Q\) in the basis \((1-X)X^j,\ 0\le j\le3\).

On rows 6 through 10, the true vanishing \(W_4=0\) and \(\beta h\) proportional to \(CG\) give
\[
 M Q+\Phi\ell=0
\]
at each of those five distinct nonzero labels, for an affine \(\ell\). It is determined by interpolation of \(-MQ/\Phi\) at \(y,w\). This numerator polynomial cannot be identically zero: since \(M\) and \(\Phi\) are coprime, \(Q\) would be proportional to \(\Phi\), but \(Q(1)=0\) and \(\Phi(1)=1\). Consequently its quotient by \((X-y)(X-w)\) has degree three and must split into the last three nonterminal exterior clocks. This conclusion permits a later physical unit head distinct from the first five exterior clocks; no implicit uniqueness at one was used.

## 3. A nonintegral-place obstruction

Let \(q>7\) be a prime, and work in the local ring \(\mathbb Z_{(q)}\) of rational numbers integral at \(q\). Suppose \((s,t)\) from the regular chart is not integral. The only terms of \(E(s,t)\) able to be strictly largest by denominator valuation are \(420s^4\) and \(-3t^3\): if \(m_s=\max(0,-v_q(s)),m_t=\max(0,-v_q(t))\), every other monomial has weighted degree strictly less than \(\max(4m_s,3m_t)\). Their valuations must tie, giving
\[
 v_q(s)=-3m,\quad v_q(t)=-4m,\quad v_q(u)=m>0,\qquad
 T=t u^4=s u^3\in\mathbb Z_{(q)}^\times .
\]
The early equation, after multiplication by \(u^{12}\), has initial terms
\(420T^4-(3+28u+168u^2+1008u^3)T^3\). Thus
\[
 T\equiv 1/140+u/15+2u^2/5+12u^3/5\bmod u^4.
\]
Coefficient comparison in (1) gives \(r=t(t-6)/s^3,\ f=168-4z\), and
\[
 z=\frac{2t(756s^3+336s^2t-2016s^2+56st^2-609st+1638s+
                 6t^3-81t^2+351t-486)}{5s^4(2t-3)}.
\]
Using the displayed \(T\) expansion, this is \(168-35280u^3\bmod u^4\): the numerator of its normalized series through degree three is \(6+56u+336u^2+756u^3\) over \(5T\). Also \(r/u\equiv140,\ e/u\equiv336\bmod q\), and \(B\equiv-1/20,\ E_0\equiv2/5,\ N/u\equiv-1/10\bmod u^4\). In particular \(K/u\) is integral with unit leading coefficient and reduces to
\[
 -7(k+3)(k^2+4k+12).
\]
Therefore \(k\) is integral.

If \(\bar k\ne-3\), both front denominators are units and \(y,w\) reduce to zero. Normalize \(Q\) by dividing by its first moment, so its reduction is
\[
 Q_0=(1-X)(300-2100X+4200X^2-2520X^3).
\]
The interpolant has integral coefficients: the divided difference of a rational function with unit denominators at \(y,w\) is integral even when \(y-w\) is not a unit (clear the denominator and factor the polynomial difference). Its reduction is the linear Taylor term of \(-\bar f X Q_0/\Phi\) at zero, so \(\bar\ell_0=0,\bar\ell_1=-\bar f Q_0(0)\), where \(\bar f=-504\ne0\). The quotient by the two monic front factors therefore has reduction proportional to
\[
 \frac{Q_0(0)\Phi-Q_0}{X}
    =60(168X^3-308X^2+175X-30).
 \tag{3}
\]

If \(\bar k=-3\), then \(k+3\in u^3\mathbb Z_{(q)}\): modulo \(u^3\), \(y_D=168(k+3)\) and \(L_k=-(k+3)(k+4)/20\), so \(K/u\) is \((k+3)\) times an element reducing to \(-63\), hence a unit multiplier. Write \(k=-3+\kappa u^3\). Reduce \(K/u^4\) to get
\(-63\kappa-(3/5)(-35280)=0\), hence \(\bar\kappa=336\). The actual denominators satisfy
\[
 y_D/u^3\equiv21168,\quad w_D/u^3\equiv7056,\quad
 y_N/u\equiv756,\quad w_N/u^4\equiv-2352\bmod q .
\]
They imply \(y u^2\equiv1/28,\ w/u\equiv-1/3\); \(y\) has a pole, \(w\) reduces to zero. The leading coefficients of \(Q_0,\Phi,M\) now give
\(\bar\ell_0=0,\ \bar\ell_1=-60\bar f\) by interpolation: divide the large interpolation value at \(y\) by \(y\), and use the integral value at \(w\). Use the front factors \((1-X/y)(X-w)\) instead of two monic factors. Division by \(X-w\) is integral; division by \(1-X/y\) is integral coefficient by coefficient, starting with its constant coefficient one. Thus the quotient is integral and reduces to a nonzero multiple of
\[
 Q_0-60\Phi=-60(28X^3-49X^2+26X-4).
 \tag{4}
\]
Both (3) and (4) have unit leading coefficient at every \(q>7\). A split rational quotient must therefore reduce to a completely split cubic in the indicated case, permitting repeated roots. If neither cubic splits modulo \(q\), all \((s,t)\) in this chart are integral at \(q\) without any good-reduction assumption on the other clocks. Examples verified in the replay are \(11,13,17,19,29,31,37,41\).

As a global valuation constraint, if \(a/b\) has a nonzero valuation at \(q>7\), then \(t=4-a/b-b/a\) has negative valuation and that valuation is a multiple of four. Such a prime may occur in the numerator or denominator of the primitive ratio only if at least one of (3), (4) splits. Independently \(5t-3\) is a rational fourth power up to a signed factor supported on \(2,3,5,7\): if its \(q>7\) valuation is negative, use the preceding cancellation; if positive, put \(S'=5s-3,\ T'=5t-3\) in \(125E\) to get
\[
 84 S'^4+T'(-168S'^2-28S'T'+84S'-3T'^2+54T'-27)=0 .
\]
Then \(S'\equiv0\) and the factor in parentheses is a unit, so \(v_q(T')=4v_q(S')\). These give arithmetic filters, not a rational point classification.

## 4. An integral residue cut at 11

By (3) and (4), \(s,t\) must be 11-integral in the regular chart. Reduce the early equation and the projectively cleared necessary split condition \((t-2)(t-6)\) square. There are seven remaining pairs:
\[
 (0,2),(0,6),(6,0),(7,8),(8,8),(9,0),(9,6)\quad\text{in }\mathbb F_{11}^2 .
\]
At \((7,8)\) every defining front denominator is a unit and \(K\) has unit leading coefficient and unique residue root \(k=9\). This gives \(y=9,w=1\) modulo 11, with distinct \(y,w\) and no \(\Phi\) pole. The monic suffix reduction is \((X+4)(X^2+5X+3)\), not split. Therefore \((7,8)\) is impossible even if an unknown clock or tableau coefficient were allowed bad reduction; the suffix roots are forced integral by their monic polynomial. Two more boundary pairs are excluded by allowing the needed rescaling rather than requiring regular reduction:

* At \((6,0)\), let \(\kappa=tk\). The coefficients of \(tK(\kappa/t)\) are integral, and its residue is
  \[
   (\bar z_0\kappa-168)(-s+s\kappa/15)
    +(\bar r_0\kappa-\bar e)(\kappa^2/30-\kappa/5),
  \]
  where \(r_0=r/t,z_0=z/t\) are integral at this pair; the three reduced values are \(r_0=7,z_0=7,e=10\). Its leading coefficient is a unit and it has no affine root in \(\mathbb F_{11}\). Thus \(\kappa\) cannot be rational, even if \(k\) itself has a pole.
* At \((9,6)\), put \(\epsilon=t-6\) and \(s_0=12/5\). Smoothness and the exact first-order expansions give \(s=s_0+(93/448)\epsilon\bmod\epsilon^2\). Here \(r\) is divisible by \(\epsilon\), and the limits of \(z,e,f\) are \(84,336/5,-168\). The limiting \(K\) is \(-56(k+2)/5\); its cubic coefficient is \((-25/864)\epsilon\bmod\epsilon^2\) and its quadratic coefficient is divisible by \(\epsilon\). If \(k\) is integral, the simple root gives \(k=-2-\epsilon/12\bmod\epsilon^2\); the exact cleared leading terms of \(y_D,w_D,L_k\) divided by \(\epsilon\) are \(28/9,14/9,-1/90\), all units. Therefore \(y\) has a pole and \(w\) reduces to zero. If \(k\) is not integral, the cubic and linear terms must tie, so \(\epsilon k^2\) is a unit. Then \(r k\) is in the maximal ideal, \(rL_k\) is integral, and \(y_D,w_D\) have the same negative valuation as \(k\); both \(y,w\) reduce to zero. Normalize \(Q\) by its fourth moment (the other three reduce to zero). In the pole branch use the affine intercept \(-M(0)Q(0)\) and slope from infinity as in (4); in the integral branch take the linear Taylor term at zero as in (3). The respective suffix reductions are proportional to \((X+2)(X^2-X-5)\) and \((X-2)(X^2-5X+1)\), each with a nonsplit quadratic modulo 11. The first-order coefficients are separately replayed in the exact dual-number ring.

This gives the remaining necessary residues \((0,2),(0,6),(8,8),(9,0)\). These four are **not** excluded. A finite-field nonexistence test restricted to distinct integral geometry does not obstruct every rational solution. No inference about \(\mathbb Q\) is made from the separate modulo-419 tableau or its finite lifts.

## 5. An exhaustive rational height cut

Write \(a/b=m/n\) in primitive form, \(n>0\). Up to inversion, \(|m|<n\): equality would mean \(a=b\) or \(a+b=0\). The local necessary conditions bound both numerator and denominator to integers of the form \(d x^4\), with \(d\) supported on \(2,3,5,7\); none of the eight explicitly excluded infinity primes divides either. Moreover
\[
  5t-3=\frac{17mn-5m^2-5n^2}{mn}.
\]
Any prime \(q>7\) dividing \(mn\) does not divide the displayed numerator, by primitivity and \(q\nmid5\). Hence this nonzero numerator, after stripping the small primes, must have absolute value a fourth power. The zero numerator would give the already impossible \(t=3/5\).

The independent finite replay enumerates every such numerator and denominator up to \(10^9\). The list has 5,898 positive integers and 1,104,666 primitive signed ratios in the chosen half of the box. Only 19 pass the shifted fourth-power test. For each of those, the replay applies the early equation \(E\) modulo all primes from 11 through 149 at which \(mn\) is a unit. At those primes \(t\) is integral and the earlier leading-term valuation argument forces \(s\) integral, so finite field enumeration loses no rational solution. Only \(m/n=1/3\) remains. It gives \(t=2/3\), whose two exact front cases are already excluded. Therefore **any rational tableau on this branch must satisfy \(\max(|m|,n)>10^9\)**, not just use non-small tableau entries. This is a bounded arithmetic statement, not a conclusion about the existence of a higher-height point.

## Verification and remaining work

The Lean scalar module checks the full coefficient combination, guarded split parameters, three integer Bézout identities, rational projective reduction, and the fixed front checks. These are standard-kernel checks on the pinned Lean/Mathlib build. The independent Python verifier also checks the early-unit eliminants and the finite residue arithmetic at the nonintegral and integral places. The actual flagged-tableau reductions and the local-ring proof above are mathematical, not advertised as a full native \(\mathtt{HasOrder}\) theorem. An eleven-stage rational construction, an obstruction for all four remaining mod-11 branches, and all multi-dirty rational cases remain open.

The [fourth-power coset follow-up](dirk-order10-rational-local-and-coset-cuts.md) narrows the remaining rational possibilities to one coset up to inversion. Its necessary clock equations split locally at every place, but no rational tableau or global obstruction follows.
