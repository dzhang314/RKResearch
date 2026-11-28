# The endpoint-only dormant center has no zero right initial slope

**Scope.** In the [central endpoint-only ERK11 chart](ERK11-NONZERO-TEN-TWELVE-ENDPOINT-ALIAS-REGULAR-EXIT.md) with ten nonzero-first-pool active labels, twelve active noncarrier interior rows, both full plateau pairs and sole dormant physical 9 at \(\zeta=0\), this excludes the entire **right raw initial derivative-slope** mask. Reflection gives the corresponding orientation at \(\zeta=1\). The original left derivative fit is not assumed to exist in this mask. The arithmetic is over characteristic zero with the earlier ordered geometric and mixed guards, and no unrestricted stage interval changes.

## 1. Both actual right slopes vanish, leaving a true quartic in the second width

Use the actual central forward direction \(L_9\propto\ell_a\), live since its primitive read is nonzero. Pair against the two right reflected derivative basis rows to obtain \(\rho_0=[\ell_a,D_R^1]\) and \(\rho_1=[\ell_a,D_R^d]\), up to the live common normalization. The actual right boundary is a live multiple of
\[
 (w-d)(y-d)D_R^1-(1-w)(1-y)D_R^d,\qquad (w,y)=(c_{12},c_{11}).
\]
The genuine right extra clocks have \(w,y\ne1\). Thus actual \([L_9,R_{11}]=0\) and the mask \(\rho_0=0\) force \(\rho_1=0\). This step does not try to assign \(R_{11}\) a direction from two zero slopes.

After the live \(a\)-normalization of \(\ell_a\), the first slope \(\rho_0\) is proportional to the irreducible quartic
\[
 F(a)=66a^4-120a^3+72a^2-16a+1 .
\]
In the exact field \(\mathbb Q[a]/F\), the endpoint reciprocal diagonal \(\mathcal D\) and the actual second slope \(\rho_1\) have monic common gcd of degree **four** in \(d\). One exact factor is \(d-1\), a forbidden zero right width. Divide it off exactly. The monic cubic quotient is kept in full, not replaced by a selected \(d\)-root.

At prime 23 the monic \(F\) has simple residue \(a=15\). In that embedding the monic quotient has integral coefficients and reduces to the irreducible cubic
\[
 \bar G(D)=D^3+2D^2+17D+5
\]
in the indeterminate \(D\) for the second width. Thus any actual \(d\ne1\) extends the Hensel embedding and is integral because it solves the monic exact quotient. Its residue is one of the three Frobenius conjugates of a generator of \(\mathbb F_{23}[D]/\bar G\). No original \(d\)-root, lost leading value or additional rational projection is discarded here.

## 2. Recover the actual rows from the other central direction

Use the alternative measured central **\(R_9\)** in the original left fit. Write \(r^{\rm ev}_y\) for the anchored reverse evaluation row at \(y\), distinct from the primitive vector \(r\). With \(S=-z_N V_b(0)\) and \(U=C_1 z_D-Hz_N\) from the true mixed contacts, the live representative is
\[
 \widehat R_9=
  U\mathscr Q(d)\,r^{\rm ev}_0+
  \bigl(J_0 S-U\mathscr Q(0)\bigr)r^{\rm ev}_d .
\]
Here \(\mathscr Q=\bar J V_b\) is the measured reverse primitive model, not the second-pool interpolant. Both \(U,S\) are live in the actual endpoint chart, and are checked as residue units along with \(z_D,z_N,H,J_0\) and the literal alternative clock guards. This row has not been inferred from the vanishing right derivative slopes.

Pair \(D_L^0,D_L^a\) against \(\widehat R_9\) to obtain \(\lambda_0,\lambda_1\). Both are units at the cubic place. Actual \([L_7,R_9]=0\) and the literal left boundary formula give the live measured \(L_7\) direction \(\lambda_1D_L^0-\lambda_0D_L^a\). Now use that **actual \(L_7\)** against the two right derivative basis rows; those two new slopes are also units. They determine the actual right calibrated unordered hull through \([L_7,R_{11}]=0\). The temporal outer contacts used for the left and right fits are now actual \([L_8,R_9]=0\) and \([L_7,R_{10}]=0\), respectively. Both primitive vanishing contacts, the two calibrated triples, and the three paid scalar moments remain valid. No independent reverse order-eleven tableau has been assumed.

With these actual alternative rows, both fixed moment matrices and both raw affine slopes are units at the cubic place. The unique sparse products are, in the residue field,
\[
 t_L=6D^2+16D+21,\qquad t_R=2D+18.
\]
All row scalings and fit denominators used here are checked explicitly. The recovered first-pool lines must agree projectively after reflecting the right one to the physical coordinate. Their required vanishing determinant has residue
\[
 2D^2+15D+1\ne0\quad\bmod\bar G .
\]
Nonzero at one root means nonzero at all its Frobenius conjugates; the computation is over the **entire** cubic residue. This rules out every exact disallowed-pivot candidate, not just a point that reduces to a favorable rational choice. The adjacent Lean file checks the scalar zero-slope implication and a coefficient-wise Bézout identity certifying that the last mark is a unit modulo the cubic. The tableau ingress and exact width/field arithmetic are in the proof and standalone replay.

Run the [standalone exact replay](erk11-endpoint-alias-initial-slopes-exit/replay_erk11_endpoint_alias_initial_slopes.py). The [Lean scalar companion](../lean/RKCert/ReviewedNative/ERK11EndpointInitialSlopesGate.lean) checks on Lean 4.34.1 through 4.37.0-rc1 at the four releases in the replay directory.
