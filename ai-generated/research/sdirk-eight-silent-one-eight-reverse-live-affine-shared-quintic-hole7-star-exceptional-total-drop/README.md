# Exceptional star front, actual seventh hole: total sixth-clock drop excluded

Use the [corrected actual ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) over a characteristic-zero field. The nine distinct nonfirst clocks include an actual ordinary hole \(r\) at **physical seven**, with zero actual amplitude and continued quartic value \(H(r)\ne0\). The star front has true noncubic fifth amplitude \(h_5\ne H_4(y)\), \(s=c_4/\gamma,\ y=c_5/\gamma=(3s-1)/2\). This packet excludes the branch \(L_1=0\) of the true sixth-clock equation. No assumption on rear phase or actual ordinarily silent stage \(\zeta\) is used.

The [actual nonhole-sixth calculation](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole7-star-cubic-closed/H7-CUBIC-PLACEMENTS.md) uses \(v=c_6/\gamma,\ h_6=H(c_6)\), not hole six. With \(D(Y)=d_2Y^2+d_1Y+d_0,\ \ell_L(Y)=\ell_0+\ell_1Y\), write
\[
 U=\ell_L(y)+\tfrac43 D(s)(5-s),\quad V=d_2(s+y)+d_1,\quad
 L_1=D(s)(8-64\eta)-(9-8\eta)\ell_1 .
\]
Here \(D(s)\ne0\) is a true fourth pivot, \(\eta U=V\) is the actual fifth gate, and \(H(\gamma Y)=H_4(Y)+E_3(Y)(\eta+\lambda(Y-y))\) with \(\lambda\ne0\) (genuine quartic), \(\eta\ne0\), \(E_3(Y)=(Y^2-4Y+2)(Y-s)\). The actual sixth gate is
\[
 (9-8\eta)(d_2-\lambda U)+L_1(\eta+\lambda(v-y))=0.
\]
If \(L_1=0\), \(9-8\eta\ne0\): its vanishing would give \(L_1=-64D(s)\ne0\). Therefore \(\lambda U=d_2\). The pair \(\eta U=V,\ \lambda U=d_2\), with \(\gcd_{\mathbb Q[\gamma]}(d_1,d_2)=1\), then gives \(U,d_2\ne0\). Indeed \(U=0\) would imply \(V=d_2=0\), hence \(d_1=0\), and \(\lambda\ne0\) rules out \(d_2=0\) after \(U\ne0\). This treats both original rank-loss equations rather than choosing a sixth clock.

## Entire fixed-profile diagonal

In physical clock \(X\), let \(C_3=8\gamma^3H_4(X/\gamma)\), \(E_3^*=(X^2-4\gamma X+2\gamma^2)(X-\gamma s)\). The actual quartic scaled by \(8\gamma^4U\) is now
\[
 H_*=\gamma U C_3+8E_3^*\big(d_2 X+\gamma(d_1+d_2 s)\big).
\]
In fact \(U(\eta+\lambda(Y-y))=d_2(Y+s)+d_1\), using both actual identities. No amplitude at \(r\) has been silently replaced by the continued value. Its paid corrected moments \(m_j=I(X^jH_*)\), \(j=0,1,2,3\), satisfy \(m_j=m_0 r^j\), and \(m_0\ne0\) by actual ordinary nonagreement. Therefore
\[
 m_0m_2-m_1^2=m_0m_3-m_1m_2=m_1m_3-m_2^2=0 .
\]
The true homogeneous equation \(U L_1=0\) is \((8U-64V)D(s)-(9U-8V)\ell_1=0\). Its exact bidegree in \(s,\gamma\) is \((5,8)\), each paid minor has \((6,16)\), and their separate \(s\)-resultants with the homogeneous equation all have degree 128 in **the single variable** \(\gamma\). Their common monic gcd is \(\Pi_{\rm mon}^4d_{2,\rm mon}^{10}\), where \(\Pi=\ell_1/2=1400\gamma^4-840\gamma^3+180\gamma^2-20\gamma+1\). Actual \(d_2\ne0\) so the complete \(\Pi\) factor is retained. No gcd is taken over a bivariate locus.

On \(\Pi=0\) the actual equation \(L_1=0\) with \(D(s)\ne0\) gives \(\eta=1/8\), hence \(U-8V=0\). Over the exact field \(\mathbb Q[\gamma]/(\Pi)\), its common \(s\)-gcd with the three full degree-six minors is one. This rational number-field arithmetic excludes the entire last factor, without an assumption of good reduction, or a missing leading-coefficient case. Thus no total-drop candidate exists for any allowed \(\zeta=2,3,4,5,6,8\).

Replay `python3 check_total_drop.py` with `python-flint==0.9.0`. No sibling code or network is needed. The [native Lean/Mathlib 4.36 source](../../lean/RKCert/ReviewedNative/SDIRK8HoleSevenExceptionalTotalDrop.lean) verifies the scaled profile implication, the two necessary units and the forced \(\eta\) law; its [axiom transcript](lean-4.36.0-replay.txt) is included. Rooted-tree extraction and exact resultants are source-level proofs. The nonzero-sixth-slope exceptional case is distinct and the unrestricted stage bound remains **10–11**.
