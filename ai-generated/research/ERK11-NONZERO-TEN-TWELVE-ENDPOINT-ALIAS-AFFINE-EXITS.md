# No left or right affine product loss at the endpoint-only dormant center

**Scope.** Use the [ordered central endpoint chart](ERK11-NONZERO-TEN-TWELVE-ENDPOINT-ALIAS-REGULAR-EXIT.md) with \(q=10,n=12\), both active plateau pairs full and sole dormant physical 9 at \(\zeta=0\). The two initial-slope and two fixed-moment masks have already been accounted for. This packet excludes both remaining **raw affine masks** without assuming the opposite affine fit is live. Reflection gives the corresponding exclusions at \(\zeta=1\). The elimination is characteristic zero with the inherited ordered mixed and geometric guards.

## 1. Work with both raw coefficients before any normalization

In each orientation the three paid scalar moment rows plus the actual temporal outer equation give a full determinant \(g_0+t g_1=0\), with true unordered flank parameter \(t\). The actual opposing rows in this endpoint chart are \(R_{11}\) for the left and \(L_9\) for the right. Thus the temporal contacts are \([L_8,R_{11}]=0\) and \([L_9,R_{10}]=0\), respectively. The actual nonzero profile vector earns the determinant even if a fitted product cannot be recovered. On the mask \(g_1=0\) we must also have \(g_0=0\).

Write \(\Gamma=\gcd(g_0,g_1)\) and \(e_i=g_i/\Gamma\) in \(\mathbb Q[a,d]\). The raw simultaneous zero implies either \(\Gamma=0\) or \(e_0=e_1=0\). Treat the two cases separately; the normalized profile is not used on a dead common factor.

## 2. The common-factor cases are literal clock collisions or earlier masks

For the left \(\Gamma\), remove the live factor \(a^3\). The remainder has bidegree \((6,5)\) and exactly two simple irreducible factors. The factor of bidegree \((3,3)\) divides the original left initial slope, already [excluded](ERK11-NONZERO-TEN-TWELVE-ENDPOINT-ALIAS-LEFT-SLOPE-EXIT.md). The factor of bidegree \((3,2)\) divides \(C_2-aH\) exactly. In the actual endpoint chart \(Hx=C_2,\ H\ne0,\ x=c_8\), so this factor forces the literal collision \(c_8=a\). It is impossible since physical 8 is an active singleton and both distinct full plateau pairs already use the two unequal repeated active labels.

For the right \(\Gamma\), remove the live factor \((d-1)^7\). The remainder has bidegree \((12,8)\) and exactly three simple irreducible factors. The \((4,0)\) factor divides the original right initial slope, one \((4,4)\) factor divides the original right fixed moment determinant, and the other divides \(z_N-d z_D\). The first two are earlier [initial](ERK11-NONZERO-TEN-TWELVE-ENDPOINT-ALIAS-RIGHT-SLOPE-EXIT.md) and [moment](ERK11-NONZERO-TEN-TWELVE-ENDPOINT-ALIAS-RIGHT-MOMENT-EXIT.md) exits. The third would give literal \(c_{10}=d\), since \(z_N=z z_D\), \(z_D\ne0\), \(z=c_{10}\). It is excluded by the same singleton census. No proxy polynomial for a fitted outer response replaces these clock guards. All just-stated divisibilities are checked as bivariate polynomial divisions, before considering a finite place.

## 3. No reduced simultaneous zero survives

Use the genuine endpoint diagonal \(\mathcal D(a,d)\). Intersect the exact two \(d\)-resultants of \(\mathcal D\) against \(e_0,e_1\). The table gives their combined projections in \(a\), followed by the exact second-width exits:

| Mask | Individual projection degrees; common degree | Irreducible degrees and powers | Second-width exits |
| --- | --- | --- | --- |
| Left | \(201,268;\ 98\) | \(1^6,4,4,4^5,8^2,12,36\) | \(a=0\); no common \(d\); \(d=0\); right initial zero; \(H=z_N=z_D=0\); \(z_N=z_D=0\); \(z_N=0\). |
| Right | \(198,260;\ 52\) | \(4^3,8^2,12^2\) | Right initial zero; \(H=z_N=z_D=0\); \(z_N=z_D=0\). |

For both masks the right-initial quartic is the same exact \(66a^4-120a^3+72a^2-16a+1\), whose whole \(d\)-fiber has that original slope zero. The two distinct simple left quartics give \(d\)-gcd 1 for \(42a^4-84a^3+56a^2-14a+1\), and a linear \(d\)-gcd with \(d=0\) for \(990a^4-2100a^3+1512a^2-420a+35\). The octic and degree-twelve \(d\)-fields in the table are checked exactly: the three input equations have monic linear gcd in the corresponding exact \(a\)-field, with the specified terminal values. The degree-twelve roots also give zero Gram variance, incompatible with the true same two-support argument.

For the left degree-36 factor, intersect the exact diagonal with \(z_N=0\) over \(\mathbb Q[a]/F\). It gives a monic linear \(d\)-gcd, whose exact root also annihilates **both** reduced affine coefficients. To ensure it is the only common \(d\)-root, use the simple Hensel place \((p,a,d)=(23,2,6)\). The width polynomial keeps full \(d\)-degree eight and the **entire** residue gcd of all three equations is linear. As in the [regular proof](ERK11-NONZERO-TEN-TWELVE-ENDPOINT-ALIAS-REGULAR-EXIT.md#2-exact-regular-projection-and-the-seven-small-branches), two distinct exact common roots would be integral and their monic quadratic product would divide all three residue polynomials with multiplicity, even if the roots specialize to the same element. This is impossible. Thus the actual width would have \(z_N=0\) exactly, and \(c_{10}=0\) contradicts the true shifted contact since \(z_D\ne0\).

There are no surviving common-product or reduced-double-zero branches. All checks are deterministic: from a directory containing the companion replay, with Python and python-flint 0.9.0 installed, run

    PYTHONDONTWRITEBYTECODE=1 python3 -B replay_erk11_endpoint_alias_affine_pivots.py

It constructs both exact resultants and factors, requiring no coefficient checkpoint or random search. One reference run took **18.759 seconds wall time**; time varies by host. The accompanying Lean file checks the two exact cleared clock implications; run the file with each target Lean release. The physical tableau ingress, exact field arithmetic and elimination remain mathematical.

Run the [standalone exact replay](erk11-endpoint-alias-affine-masks-exit/replay_erk11_endpoint_alias_affine_pivots.py). The [Lean scalar companion](../lean/RKCert/ReviewedNative/ERK11EndpointAffineClockGates.lean) was checked on the four supported releases from Lean 4.34.1 through 4.37.0-rc1.
