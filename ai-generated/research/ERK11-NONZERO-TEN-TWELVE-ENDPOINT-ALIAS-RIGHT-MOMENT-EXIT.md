# The endpoint-only dormant center has no right fixed-moment rank loss

**Scope.** Continue the [central endpoint-only ordered ERK11 chart](ERK11-NONZERO-TEN-TWELVE-ENDPOINT-ALIAS-REGULAR-EXIT.md) with \(q=10,n=12\), both full plateau pairs, and sole dormant physical 9 at \(\zeta=0\). After the [initial-slope exits](ERK11-NONZERO-TEN-TWELVE-ENDPOINT-ALIAS-RIGHT-SLOPE-EXIT.md), this excludes the entire **right fixed three-by-three moment determinant** mask. Reflection covers \(\zeta=1\) using the actual mixed pure fronts; no reverse ordinary order-eleven theorem is assumed. The field arithmetic is characteristic zero with the earlier ordered guards.

## 1. The actual right mask

Use \(Y=1-X,\ w=1-d,\ h=w/2\). The opposing row on the right is **actual \(L_9\)**, a live multiple of \(\ell_a\). With the original right initial slope live, it also determines actual \(R_{11}\), which opposes the left fit. Thus the actual outer equations here are \([L_9,R_{10}]=0\) and \([L_8,R_{11}]=0\), respectively. The right fixed determinant \(\Delta_R\) is formed from the three moment columns \(\phi,YB_0,YB_1\), with \(\phi=Y^2(w-Y)\), true unordered calibrated hull \(B_0+t B_1\), and weight \(Y(1-Y)(Y-w)(Y-(1-a))\). The right temporal row is the original \([L_9,R_{10}]=0\), not a synthetic change to the central direction.

After deflating only already live width factors, the \(d\)-resultant of the endpoint diagonal \(\mathcal D\) and \(\Delta_R\) has degree 126 in \(a\), with irreducible degrees and powers \(4,4^5,42,60\). The first quartic \(42a^4-84a^3+56a^2-14a+1\) gives exact \(d\)-gcd 1 after specializing in its quotient field; it is not an actual common width. The quartic of multiplicity five gives the old right initial slope \(\rho_0=0\) identically in \(d\), already excluded. The latter inference does not assume the alternative initial-slope fit remains live.

## 2. The degree-42 factor: use the actual temporal row

Use the simple place \((p,a,d)=(29,9,15)\). For this and the next factor the standalone replay checks a simple root of the monic irreducible \(a\)-factor, integral coefficients, full \(d\)-degree eight of \(\mathcal D\), and a linear **entire** residue gcd of \(\mathcal D,\Delta_R\). The same Hensel ingress as in the [regular endpoint proof](ERK11-NONZERO-TEN-TWELVE-ENDPOINT-ALIAS-REGULAR-EXIT.md#2-exact-regular-projection-and-the-seven-small-branches) applies: every actual \(d\) is integral at a place over this embedding and reduces to the indicated value. The inherited width, true middle-clock and actual-row normalization guards are units there.

For each orientation form the sparse homogeneous four-row system in \((U,W,T,A)\), consisting of the three moments and the actual outer row. The first three columns are independent of the true unordered product \(t\) and the last column is affine in \(t\); its full determinant is \(g_0+t g_1\) even when the three moment-only rows are singular. At the chosen residue place the left moment-only first-three-column minor is live. On the right use moment rows 0 and 1 **and the actual temporal outer row** to obtain a live minor. Then \(A\) cannot vanish in a true nonzero coefficient vector and can be normalized to 1. Both full affine slopes are live at the place; the true products reduce to \(t_L=17,t_R=10\). The recovered first-pool lines in their oriented coordinates are \((0,1),(8,8)\). The necessary physical projectivity determinant \(p_0q_1+p_1(q_0+q_1)\) has nonzero residue 16.

## 3. The degree-60 factor: calibrate from the measured left profile

Use the good place \((19,11,12)\). The full left fit is live there, including its fixed moment pivot, raw affine slope and unordered product. No right fixed or affine pivot is needed. Reflect the left first- and second-pool lines into \(Y\), then choose their relative scale at the actual right singleton \(h=w/2\) so that \(Q(h)=P(h)f_R(h)\), with \(f_R=Y^2(w-Y)/w\) in this coordinate. The reflected response has a single live scale relative to the physical response, so this genuine calibrated singleton determines the new ratio \(Q/P\). All involved evaluations are units at the place.

Put \(x=1-c_{10}\), the right outer clock in \(Y\). In the original outer relation the adjusted primitive model is \(Y(Y-w)E(Y)\), and the response correction satisfies \(B(0)S(Y)=S_0(Y)+t S_1(Y)\), with \(B(0)=tB_1(0)\). The true outer sample \(Q(x)=P(x)F_x^{R}\) gives
\[
 k_0+t k_1=0,\quad
 k_0=Q(x)S_0(x),\quad
 k_1=P(x)x(x-w)E(x)B_1(0)+Q(x)S_1(x).
\]
This is the actual right outer relation **before** the lost moment determinant. At the place the coefficients are \((k_0,k_1)=(2,12)\), giving \(t_R=3\). The genuine distinct right calibrated triple must then have monic hull \(B_0+t_R B_1\) dividing \(Q-P f_R\). Monic division commutes with reduction, even without any field claim about a repeated residue root. Instead the residue remainder is
\[
 5Y^2+16Y+8\ne0 \pmod {19}.
\]
This excludes the last factor without an assumption on the old right affine coefficient. It does not establish any affine loss unrelated to this fixed-moment mask. The tableau and width-field arguments are mathematical; the accompanying Lean verifies the terminal residue arithmetic.

Run the [standalone exact replay](erk11-endpoint-alias-moment-pivots-exit/replay_erk11_endpoint_alias_moment_pivots.py). The [Lean scalar companion](../lean/RKCert/ReviewedNative/ERK11EndpointMomentPivotsGate.lean) was checked on the four supported releases from Lean 4.34.1 through 4.37.0-rc1.
