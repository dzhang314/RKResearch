# The dormant plateau alias has no right affine pivot loss

**Scope.** In the [sparse plateau-alias chart](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md) with \(q=10,n=12\), both plateau pairs full, and sole dormant physical 9 at \(\zeta=d\), this excludes the entire **right raw affine slope** mask, without assuming a left affine fit. Reflection transfers the result to \(\zeta=a\). The exact width algebra uses characteristic zero with the inherited ordered mixed and geometric guards; there is no unrestricted stage-bound change.

## 1. The simultaneous raw equations and common factor

The four-row right determinant is formed from the three paid reflected moment rows and the **actual** outer equation \([L_7,R_{10}]=0\), in the coordinate \(Y=1-X\). The opposing \(L_7\) direction is measured from its actual off-diagonal with \(R_9\), using the already live left initial slope. The right hull has its true unordered product \(t\), so
\[
 g_0+t g_1=0.
\]
This determinant vanishes on the actual nonzero pool profile, regardless of its rank. Therefore the right raw affine mask \(g_1=0\) also forces \(g_0=0\). With \(\Gamma=\gcd(g_0,g_1)\) and \(e_i=g_i/\Gamma\), treat the cases \(\Gamma=0\) and \(e_0=e_1=0\) separately.

The raw bidegrees are \((15,22),(18,27)\). Deflate only the live power \((d-1)^3\) from \(\Gamma\). Its remaining two simple exact irreducible factors have bidegrees \((2,3),(3,3)\). The replay checks the following exact bivariate divisibilities:

* The \((3,3)\) factor divides the right initial derivative slope \(\rho_0\) against the actual \(L_7\), excluded by the [right initial-slope theorem](ERK11-NONZERO-TEN-TWELVE-PLATEAU-ALIAS-RIGHT-SLOPE-EXIT.md).
* The \((2,3)\) factor divides \(C_1-dH\), with the established true shifted mixed moments. Since the central dormant read \(V_R(9)\) is zero and \(pV_R\) is literally supported only at physical 10, its grade-nine and grade-ten payments give \(Hz=C_1,\ z=c_{10}\), with \(H>0\). Thus the factor would force the **literal** clock collision \(c_{10}=d\). Row 10 is active and is a singleton: the two full plateau pairs already spend both unequal active pairs. It cannot supply a third active copy at \(d\).

No projection through an opposite fitted profile replaces this chronology gate.

## 2. The exact reduced double-zero fields

The reduced bidegrees are \((10,13),(13,18)\). Their two \(d\)-resultants against \(\mathcal D(a,d)\) have degrees 230 and 309. The common monic gcd has degree 54 and irreducible degrees and multiplicities \(1^8,3^2,8^2,12,12\). The linear factor gives \(a=0\), forbidden. For every other factor \(F\), compute the joint gcd of \(\mathcal D,e_0,e_1\) in \(d\) over \(\mathbb Q[a]/F\). It is monic linear in all four cases; the exact second-width evaluation gives:

| Exact factor | Inherited contradiction |
| --- | --- |
| Cubic \(165a^3-180a^2+54a-4\) | \(d=1\), zero right width |
| Degree eight | \(H=x_D=0\) |
| Old left-slope degree twelve | Both left initial derivative slopes zero |
| Other degree twelve | \(x_D=x_N=0\) and zero variance |

Thus every reduced double-zero width fails before any right or left affine reconstruction. The standalone replay builds the inverse-Gram and moment polynomials, checks the raw divisibilities, and computes all reduced width-field gcds exactly. The adjacent Lean scalar lemma proves the alias inference given the actual mixed moment, without an order assumption. The joint elimination and the tableau bridge remain mathematical.

The [standalone exact replay](erk11-plateau-alias-right-affine-exit/replay_erk11_plateau_alias_right_affine_pivot.py) and [Lean scalar gate](../lean/RKCert/ReviewedNative/ERK11RightAffineMaskGate.lean) were independently checked, the latter on all four targeted versions.
