# Disjoint two-later-singleton prefixes: the actual scale system is never rank zero

Assume strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, all ten literal quadratic defects nonzero, exactly seven distinct clock labels, and both endpoints singleton. Each true first-three prefix uses one later S and one later D, and its observed D is **not** the D of the other prefix. Their possible phases are A2 (D physically second), A3 (D physically third), or star in either physical order. This packet closes the simultaneous zero-rank case of the two actual affine scale rows, not the nonzero-rank cases.

## Two quadratics with four physical singleton reads

Normalize to common diagonal one, \(y=x-1\), endpoints \(0,H\) and reflected coordinate \(H-y\), with \(m=(H+2)/2\). Let \(u,v\) be the normalized observed D offsets in their actual orientations, so original D labels are \(p=u\), \(q=H-v\). Let \(s,t\) be the additional forward and reverse singleton labels in original coordinates. All six labels \(0,H,p,q,s,t\) are distinct. In the orientation's own axis the S offset as a function of D offset \(z\) is \(2z,z/2,2-z\) for A2,A3,star. The [true tap formulas and guards](../sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-rank/README.md#physical-coordinates-and-all-nine-types) supply the normalized later singleton defects \(f_s,\rho_t\) and require ordinary nonzero tap/physical clock guards. Both actual star orders have the same paid pair data by their respective literal formulas. The genuine weighted mirror lets us restrict to A2A2,A2A3,A2S,A3A3,A3S,SS without assuming a tableau symmetry.

Use the true quadratic singleton graph \(R\), \(\lambda\ne0\) the actual reverse-to-original residual scale, and the true quadratic \(K=\lambda(A_2+B R)\). All four S are consumed and paid:
\[
\begin{array}{c|ll}
 y & R(y) & K(y)\\\hline
 0 & 1/2 & 2\lambda L_4(0)\\
 s & f_s & \lambda L_4(s)/f_s\\
 H & \lambda/2 &2 L_4(H)\\
 t & \lambda\rho_t & L_4(t)/\rho_t.
\end{array}
\]
The \(K\) entries use the actual singleton identity \(L_4=R(A_2+B R)\) and do not require any unused D residual. The four reads of each quadratic give one affine equation in \(\lambda\) by interpolation from \(0,s,H\). At simultaneous rank zero both coefficients of \(\lambda\) vanish, hence both constant parts vanish as well.

The two zero coefficients for \(R\) are equivalent to
\[
 f_s=\frac{(H-s)(t-s)}{2Ht},\qquad
 \rho_t=\frac{t(t-s)}{2H(H-s)} .
\]
All denominators shown are actual nonzero. The first yields
\[
 a=H-s-2Hf_s\ne0,\qquad t=s(H-s)/a,
\]
since \(s(H-s)\ne0\). The second fixes the reverse tap \(\rho_t=f_s t^2/(H-s)^2\). Thus \(t\), and hence the literal reverse D offset \(v\), are rational in the two remaining clock parameters \(H,u\). This is a rank-zero implication, not an assumption on the general clock atlas.

The \(\lambda\)-coefficient quadratic for \(K\) has two known roots \(H,t\) and at \(0\) equals \(2L_4(0)\). The constant coefficient quadratic has roots \(0,s\) and value \(2L_4(H)=2L_4(0)\) at \(H\). These descriptions also hold when \(L_4(0)=0\), since no division by this value is made. Their remaining reads at \(s\) and \(t\), by the paid \(R\) relations, give
\[
 L_4(s)=4 f_s^2 L_4(0),\qquad L_4(t)=4\rho_t^2 L_4(0).
\]
The two exact Legendre equations and the actual paid reverse tap identity above comprise the rank-zero clock system.

## Exact fields and the graph pivot

Use \(t=s(H-s)/a\), and set the true \(v\) to \((H-t)/2,2(H-t),2-(H-t)\) in the respective rear phases. Clear only audited nonzero denominators and true guard factors. Project the first Legendre equation against each other row in \(H\), and take the gcd of their two exact \(u\) projections. The exact profiles are:

| Phase | Guarded projected degrees | Irreducible \(u\) factors |
| --- | --- | --- |
| A2A2 | 61,131 | degrees 5 and 16 once; degree 3 five times |
| A2A3 | 61,33 | degree 3 once |
| A2S | 61,33 | degree 3 once |
| A3A3 | 13,8 | degrees 2,4 once |
| A3S | 13,8 | degrees 2,4 once |
| SS | 13,8 | degrees 2,4 once |

Of the 11 projected fields, five have linear joint \(H\)-gcd entirely on the true forbidden coincidence \(H=s\), and two have unit joint \(H\)-gcd. The four remaining fields (A2A2 degree 16, and A3A3, A3S, SS degree 4) each have a single exact \(H\) in the abstract irreducible field.

In each of these fields fit the **true** affine \(F_*\) through the paid \(L_3/L_4\) at both observed distinct D labels \(p,q\); \(L_4\) is nonzero at them by consecutive coprimality. Form the exact cubic
\[
 M_3=(L_3-F_*L_4)/[(y-p)(y-q)]=\sum_{i=0}^3 m_i y^i.
\]
The genuine [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) implies \(M_3=(\ell_0+\ell_1 y)R(y)\) in every characteristic-zero candidate, independent of any field ordering or splitting. This exact quotient identity holds even if \(R\) has a common root with a D. With paid \(R=1/2+r_1 y+r_2 y^2\), the three reads \(0,s,H\) give \(r_1,r_2\) affinely in the unknown true scale. Hence \(\ell_0=2m_0,\ \ell_1=2m_1-4m_0 r_1\); the remaining coefficient equations are
\[
 m_2-2m_0r_2-(2m_1-4m_0r_1)r_1=0,\qquad
 m_3-(2m_1-4m_0r_1)r_2=0.
\]
In all four surviving fields these two scalar polynomials in \(\lambda\) have exact gcd one. No pivot from the lost scale rows is used, and neither the unobserved third D, an actual fourth row, nor a residue test is needed. Therefore there is no true rank-zero candidate over any characteristic-zero extension.

## Replay and boundary

Run `SYMPY_GROUND_TYPES=flint python check_rank_zero.py` with SymPy 1.14 and python-flint 0.8. The replay has no cached coefficients and no compiled kernel. The [candidate Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonBothTwoSDisjointRank.lean) verifies the cleared offset/graph equalities; the entire tableau and elimination proof are paper/exact Python. The nonzero-rank reduction and the disjoint mixed-prefix case remain separate. The general 10–11 stage interval is unchanged.

The standalone exact replay was independently reproduced. The Lean scalar companion is a draft, not kernel-checked for this release.
