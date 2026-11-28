# Closing equality of the Gauss hole and reverse root

This is the [detected seven-distinct active chart](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) at the strict SDIRK8 ten-stage floor over a characteristic-zero field. Only the individually weight-zero first stage has nonzero quadratic residual. The affine \(Q\) shares its root \(r\) with \(L_4\): the active Gauss-hole stage at \(r\) has zero cubic defect, and the six ordinary active sites have nonzero \(h=\lambda p_0\), where \(p_0=L_4/(X-r)\) and \(\lambda\ne0\). Assume \(k\ne0\) and **the root of the reverse affine \(P_1\) is \(r\) itself**. The [literal-root packet](../sdirk-eight-silent-one-seven-distinct-literal-reverse/README.md) covers \(r\) at either actual silent literal front. This packet covers a nonliteral \(r\) with at most one active literal front. A reverse root at a **different clock from \(r\)** remains separate.

## Physical occupancy and actual pure slope

Write \(\boldsymbol h=N\boldsymbol g,\ \boldsymbol w=\boldsymbol b^{\mathsf T}M\), with \(N=A-\gamma I\), \(M=CA-AC-A^2\). The actual equation is \(\boldsymbol h^{\mathsf T}B=\boldsymbol wP_1(C)\). At every inactive clock other than \(r\), the individual reverse weight is zero. The six ordinary active clocks have nonzero \(w\); there must be a nonzero reverse aggregate at \(r\) by the six vanishing moments. The reverse interpolant \(D'(c_i)w_i\), using the seven aggregate sites, is a nonzero constant.

The paid \(wh\) moments interpolate the reverse-weighted \(h\) by a cubic, agreeing with \(\lambda p_0\) on the six ordinary sites. Likewise the paid \(wv\) moments interpolate the weighted pure-four \(v\) by a quartic agreeing with \(\ell_v\lambda p_0\) on those sites, for \(v=Ah,\tau_4\). Thus the weighted virtual defect at \(r\) is \(\lambda p_0(r)\ne0\), and the virtual pure reads there use the active affine slopes. As the active hole has actual \(h=v=0\), at least one physically silent stage with nonzero reverse weight shares \(r\). If both literal fronts are silent, these are the two physically silent zero rows, so a nonliteral \(r\) is impossible. Otherwise exactly one literal front is active, its companion is silent outside \(r\) and has \(w=0\), and just one nonliteral physically silent stage contributes at \(r\). Its actual \(v=\ell_v(r)h\) follows by canceling its own nonzero \(w\) in the **difference** of the virtual readings. Its individual \(h\) need not equal the virtual \(h\).

## Complete literal tail census

Let \(x=1-\gamma,\ c=x-\gamma u,\ k=1+2u-u^2\). For active eight, its actual star or arithmetic clock is \(d=x-\gamma(2-u)\) or \(d=x-2\gamma u\). Put \(H=-2+u+4u^2-u^3,\ T=4u^3-12u^2+3u+2\). At each of these sites *if ordinary*, \(w_i/b_i\) is proportional to \(p_0(c_i)/(c_i-r)\). An actual hole is **not** assigned this ratio.

When all active tail sites are ordinary, the ninth condition is the exact \(u\)-padded quotient of \(p_0(c)(x-r)-k p_0(x)(c-r)\). The companion eighth numerator in star is analogous with \(d\); subtract the exact zero-gap and repeated-tail padding as in the [literal pole proof](../sdirk-eight-silent-one-seven-distinct-literal-pole/README.md). In arithmetic its numerator is \(H p_0(d)(x-r)+kT p_0(x)(d-r)\). If eighth is silent, its individual nonzero \(w_8\) forces its actual clock \(r\) and \(2(x-r)+\gamma k(u-2)=0\). The two literal equations have an exact resultant in \(u\).

If ninth or active eighth is itself the hole, substitute its known gap \(u=(x-r)/\gamma,\ 2-(x-r)/\gamma\), or \((x-r)/(2\gamma)\), using the *other* tail comparison or the silent eighth geometry. The small projected polynomial is the homogenized substitution, with no division in its computation. If terminal is the hole, \(\gamma=1-r\). Both \(c,d\) are then ordinary when active, so compare eighth with ninth instead of using terminal's undefined ratio. If eighth is silent its actual clock is \(r=x\); the geometry and \(k\ne0\) force \(u=2\).

| Placement | Star active eight | Arithmetic active eight | Silent eight |
|---|---:|---:|---:|
| No active tail hole, diagonal polynomial | 6 | 21 | 11 |
| Ninth hole, diagonal polynomial | 6 | 8 | 3 |
| Eighth hole, diagonal polynomial | 5 | 5 | not applicable |
| Terminal hole, gap polynomial | 3 | 5 | 1 |

These exact degrees are before squarefree decomposition. The diagonal projection removes only factors at \(\gamma=0,\ x=r,\ p_0(x)=0\) in branches where terminal is ordinary. Removed gap padding is only at literal coincidences. The exact leading splits keep every nonzero degree branch for the ninth polynomial when the active tail has no hole.

## Literal fourth and fifth cuts

Let \(a\) be the active literal normalized clock, \(h_a\ne0\) its actual defect. For ordinary rows use \(Q=p_0(\gamma a)\), \(P(Y)=h_a p_0(\gamma Y)\), so the normalized ordinary \(h=P/Q\).

* If fourth is the physically silent stage, its actual \(s=r/\gamma\) and \(H_4(s)\) supply the second pure-four slope anchor. This uses only the just-proved actual slope identity, not equality of its amplitude to the virtual one.
* Otherwise fourth is active, and is ordinary: if it were the hole, its actual \(H_4=0\) would require its actual \(Ah=0\), excluded by their exact literal gcd. Its necessary fourth equation is \(\Phi=(QH_4-P)/(Y-a)=0\), with the earlier active exact padded factor removed. The entire quadratic \(\Phi\) is retained before testing fifth.
* If fifth is physically silent, \(y=r/\gamma\) and its actual \(h_5\) is unknown. At that clock each literal pure read is \(H_4(s)V_0(y)+V_1(y)h_5=0\) after clearing the fourth slope, with \(V_1(y)=H_4(s)(D_v(s)-\ell_v(a))-X_v(s)(y-a)\). Here fourth is ordinary and \(H_4(s)\ne0\). The inconsistency determinant \(T_0 A_1-A_0 T_1\) of the two reads is a unit. Neither fifth slope is divided.
* Otherwise fifth is active. If ordinary, put \(h=P/Q\) in the two literal reads. Both exact padded factors \(y-a\) and, when fourth is active, \(y-s\) may be removed. The degree-\((3,3)\) or degree-\((2,2)\) padded resultant is a unit. If fifth is the actual Gauss hole (possible only when no active tail already occupies \(r\)), instead put its actual \(h=0\) in the original two strict reads and test \(T_0=A_0=0\) at \(r/\gamma\). The two values generate the unit ideal.

## Verification

Use `python3 check_gauss_reverse_root.py` in the repository sibling proof tree with `sympy==1.14.0` and `python-flint==0.9.0`. Its entry point loads the archived silent-two/three arithmetic, the finite six-clock anchored/reverse/shared companion folders, the seven-distinct anchors, coprime and one-front-zero folders, and in particular the new [literal-pole helper](../sdirk-eight-silent-one-seven-distinct-literal-pole/README.md). It runs all 44 exact tail/front modes.

The projected diagonal and gap polynomials are computed over the rational Gauss quartic quotient; exact coefficients own the case splits. At each check the prime is \((1129,t-203)\) or (for three entire arithmetic modes) \((1151,t-24)\), \(2t^2=1\). Every Gauss quartic residue, every irreducible diagonal component and every relevant gap gcd factor is retained; no reduced chronological collision is dropped. Normalization happens only after leading coefficients are checked as units, and the required residuals generate the unit ideal in the finite algebra. This proves the characteristic-zero exclusions by the same local lift as the literal-pole proof, without any assumption of reduction of an actual tableau.

The [native Lean file](../../lean/RKCert/ReviewedNative/SDIRK8GaussSilentSlope.lean) independently kernel-checks the actual Gauss silent slope and the division-free literal silent-fifth elimination on Lean/Mathlib 4.36.0. The saturation and finite arithmetic are source-level. No improvement of the unrestricted **10–11** interval is claimed.
