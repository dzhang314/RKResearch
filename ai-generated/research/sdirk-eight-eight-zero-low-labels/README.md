# Exactly eight physical zeros require at least seven zero clock labels

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight, with common nonzero diagonal \(\gamma\). Put \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), and suppose exactly eight physical residuals are zero. The count is on physical rows, even when weights or clocks coincide.

**Characteristic-zero result.** The two off-zero stages must be individually silent, at two different clocks, and must be physical rows 1 and 2. The other eight rows have at least **seven distinct literal clock labels**. If the reflected second ratio is zero, they have exactly seven labels with one duplicated terminal clock. If it is nonzero, seven or eight labels remain open. This is a strict count restriction, not an exclusion of every ten-stage tableau.

## 1. Literal placements and exact profile gates

Use the [paid census](../sdirk-eight-seven-eight-zero-census/README.md) and [multi-clock row-two gate](../sdirk-eight-seven-eight-off-silent/README.md). The placement and weight deductions in this paragraph hold over a field of characteristic zero or greater than seven:

* At two distinct off clocks \(GE_1\) gives the full two-dimensional \(F_3\), clean on the zero rows. The literal first and second rows are off-zero. The two paid pure moments in \(g,cg\) separate these two clocks, so both weights vanish.
* At one off clock, that clock is \(c_1=\gamma\). The literal twin obstruction gives \(c_2\ne\gamma\), so \(g_2=0\), and the first-three identity with zero forward second ratio gives \(g_3=0\). One must retain the independent grade-three lift here. If the two nonzero residuals differ, the moments in \(g,g^2\) make both weights zero. If they are equal, either both weights are zero or they are both live and cancel. In the latter case the terminal row is the other off-zero row by the pure reverse quadratic identity, and \(\gamma=c_{10}=1-\gamma\) gives \(\gamma=1/2\).

The [one-clock silent closure](../sdirk-eight-silent-two-distinct/README.md) excludes equal and unequal one-clock silent cases over characteristic zero; the [active one-clock reduction and closure](../sdirk-eight-half-repeated/README.md) exclude the live cancellation pair. We therefore work with two distinct silent initial off rows.

Normalize \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), and \(U=\ker\operatorname{diag}(\mathbf g)\). The two off clocks are \(1,1+u\). The literal first zero \(a=x_3\) satisfies \(a=1+2u,\ Q(u)=4u^3-12u^2+3u+2=0\), since the initial star phase would retain the nonzero second defect. The actual supported quadratic profiles are \(P_0=2T-1-T^2/2\) and \(P_{\rm off}=(T-1)(T-1-u)\). Use the same [first-new clock gates](../sdirk-eight-seven-zero-two-clock-active/README.md#1-actual-chronology-and-two-supported-quadratic-profiles) as for the constant-residual two-clock chart: they use just the two supported profiles, \(r_2=2\), and two off-clock values to make \(F_3\) clean. The first new zero \(b\ne a\) satisfies \(b^2-(2u+4)b+1+2u=0\). The profile
\[
 P_0(a)P_{\rm off}-P_{\rm off}(a)P_0
\]
is nonzero at \(b\); its \(M\)-reads with the two quadratic inputs prove that \(F_4|_U\) has rank two, detected at those two physical occurrences. Coprimality of \(P_0,P_{\rm off}\) makes every degree-at-most-three scalar polynomial a supported trace by multiplying each by affine polynomials. The [third-new clock gate](../sdirk-eight-seven-zero-two-clock-active/README.md#2-the-third-new-clock-satisfies-a-quadratic) therefore gives \(C_3(c;D)=0\) for the first \(c\) different from \(a,b\). All of these statements allow repetitions preceding the first new occurrence. The replays check the nonzero second-clock read and the full primitive pivot, rather than assuming the first three *physical* zero clocks differ.

## 2. A paid rear nonvanishing and exact multiplicities

The off projections of \(W_2,W_3\) are zero by rank since \(r_2=r_3=2\). Thus \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T(CA-AC-A^2)/2\) and \(\boldsymbol\eta^\mathsf T=\mathbf z^\mathsf T(A'-I)\) are supported on \(U\), where \(C=\operatorname{diag}(\mathbf c)\). Write \(s=x_{10}=D-1,\ t=x_9=s-v,\ r=x_8\) and \(\kappa=1+2v-v^2\). The literal last two weights are nonzero at different clocks.

If \(\kappa\ne0\), then **\(z_8\ne0\)** in every possible physical rear phase, over any paid field. A silent eighth has a nonzero pure coordinate by the literal ghost gate. A live star keeps \(\kappa\). For live arithmetic use the corrected quadratic \(\Pi\) from the [arithmetic sextic argument](../sdirk-eight-seven-zero-pure-distinct/README.md#2-rear-cardinal-rows-and-the-arithmetic-compatibility-sextic), whose actual inputs vanish at all three rear physical rows. Its pure primitive error lies in the linearly affine \(\mathbf z^\mathsf T\)-space \(\langle\mathbf z^\mathsf T,\mathbf z^\mathsf T C'\rangle\), \(C'=\operatorname{diag}(\mathbf x)\), since \(z_{10},z_9\) are nonzero at distinct clocks. The arithmetic affine identity, written before dividing by the third ratio \(\kappa_3\), is
\[
 \kappa\,J\Pi(1+2v)=
       \kappa_3\bigl[2J\Pi(1+v)-\kappa J\Pi(1)\bigr].
\]
It remains valid when \(z_8=\kappa_3=0\): the literal eighth is live, and its zero pure-coordinate discrepancy forces the left primitive to vanish there. Thus the same sextic \(T_6(v)=0\) holds even at a putative zero third ratio. The literal \(H(v)\kappa_3=-\kappa Q(v)\) would also give \(Q(v)=0\). This is impossible in a paid field, since
\[
 T_6=(2v^3-5v^2-11v-6) Q-3R,\qquad
 (-2268v-895)Q+(324v^2-740v-309)R=64,\quad R=28v^2-9v-6.
\]
The proof uses only the actual suffix inputs and never applies an aggregate formula to a duplicated rear clock.

In the \(\kappa\ne0\) branch all three actual rear pure coordinates are nonzero, at distinct clocks. At six or fewer labels the six scalar moments of \(\mathbf z\) force zero aggregates, so \(s,t,r\) each require a duplicate. This leaves **at most five** labels. In the \(\kappa=0\) branch the pure row \(\mathbf z\) is supported at \(s\), so \(s\) is duplicated. Row 8 is live by the ghost gate, and the two strict rear taps give nonzero \(\eta_8,\eta_9\). Thus at five or fewer labels the five moments of \(\boldsymbol\eta\) similarly force duplicates at \(t,r\), distinct from \(s\).

In these low-label branches, four or fewer labels would give exactly four live Gauss clocks by ordinary moment rank, even if some literal weights are zero. The three rear clocks would be a directed Gauss triple, either \(x,y,2y-x\) or \(x,y,4x-y\) after reflection. Both are impossible in characteristic zero, by the two exact Legendre divided-difference resultants in the replay. At exactly five labels the three tail labels are all doubled once, with no other duplicates.

## 3. All five-label ordinary projections

At five labels, every actual clock on the ordinary support lies in the zero set of a monic degree-five nodal polynomial. Its product with \(1,T,T^2\) has zero \(I_D\)-mean, where \(I_D(T^j)=D^j/(j+1)\). No nonzero ordinary aggregate at each nodal label is required.

For zero rear ratio in either phase, \(v^2-2v-1=0\). For a nonzero ratio, a ghost has \(H(v)=0\) and arith has \(T_6(v)=0\). The phase clocks are \(s=D-1,t=s-v,r=s-w\), \(w=2v\) or \(2-v\). The exact fields of these finite-gap branches have primitive \(u+b+2v\), of degrees 12, 18 and 36, with verified inverse coordinates. When \(a,b\) are disjoint from the three rear labels, all five nodes are known and the three ordinary means have constant gcd in \(D\). One overlap pins \(D\), and the ordinary Hankel determinant for the last unknown label is nonzero in every such field. The exact gap differences exclude two overlaps.

For a nonzero-ratio live star the gap remains free. Put \(m=D-2,\ \delta=v-1\), so \(t,r=m\mp\delta\). With no overlap, the node polynomial is \((T-a)(T-b)(T-s)[(T-m)^2-\delta^2]\); the ordinary equations are linear in \(\delta^2\). The two-column minors have constant guarded gcd in \(D\). With one overlap at \(s\), \(D\) is fixed; the unknown extra label \(x\) and \(\delta^2\) give an exact three-by-three linear system in \(x,\delta^2,x\delta^2\), violating its product relation. With one overlap at \(t\) or \(r\), the other reflected pair node is explicit and the last-label moment minors have constant guarded gcd in \(D\). With two overlaps the diagonal is fixed and the ordinary determinant for the two unknown labels is nonzero, including if the overlapping labels are the symmetric pair. The only factors stripped from these gcds correspond to \(D=0\) or forbidden equalities among the assumed distinct known labels.

## 4. Six labels at zero rear ratio

At six labels only \(\kappa=0\) remains. Use the two ordinary equations of the monic degree-six nodal polynomial, without the physical \(\eta\)-tap ratio; the latter need not be an aggregate ratio if another rear label is doubled. If \(a,b\) avoid all of \(s,t,r\), the five known mask \(P_5\) is fixed in \(D,v\). Put \(m_i=I_D(T^i P_5)\). The last label \(x\) requires \(m_1=xm_0,\ m_2=xm_1\), hence \(m_0m_2-m_1^2=0\). The exact guarded polynomial has degree ten. The first new \(c\) must be one of \(s,t,r,x\). At the rear choices, the exact \(C_3\) evaluations are coprime to the guarded polynomial; at \(x\) the denominator-free quadratic gate is \(c_2m_1^2+c_1m_1m_0+c_0m_0^2=0\) for \(C_3(T)=c_2T^2+c_1T+c_0\), again with constant gcd. This also handles an ordinary pivot zero, since any such actual last label gives \(m_0=m_1=m_2=0\).

One overlap instead fixes \(D\), and the two ordinary equations recover a monic quadratic for the remaining two nodes at a nonzero exact pivot. The third-forward gate is nonzero at both possible known labels and has constant gcd with the recovered quadratic. Both overlaps are impossible by the same exact finite gap check. This closes six labels without assuming which physical positions carry the extra duplicate.

## 5. Replay and scope

With SymPy 1.14 and python-flint 0.8, run `python check_low_finite.py MODE` for `MODE=zero-star,zero-arith,ghost,arith`, `python check_low_star.py`, and `python check_six_labels.py MODE` for `MODE=zero-star,zero-arith`. These are exact characteristic-zero polynomial checks, not a finite-grid inference. The native `RKCert.Research.SDIRKEightEightZeroLowLabels` checks the paid rear Bézout and cleared ordinary quadratic gate; `proof-audit.lean` audits those scalar theorem types. Only the explicitly paid literal deductions have positive-characteristic scope; the five/six-label complete exclusion is characteristic zero.
