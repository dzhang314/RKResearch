# The neighboring singular cross block has no left affine loss

**Scope.** Continue the [neighboring original right-loss chart](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-RIGHT-SLOPE.md): in the ordered, all-live, fixed-full-pair ERK11 chronology with \(q=10,n=12\), sole dormant physical 9 shares the active singleton \(s=c_8\notin\{0,1,a,d\}\), \(b=1-d\), and \(K_0(a,b)=0\). Use actual \(R_9\) for the left fit and actual \(L_9\) for the right fit. Both corresponding initial slopes and fixed moment pivots are live by the preceding results. This note excludes the **left raw affine loss on \(K_0=0\)**, not other chronologies or the unrestricted stage count. Reflection gives the mirrored result.

## Exact raw four-row equations

The shape of the left singleton hull is \(B=B_0+tB_1\). Normalize its two slopes to \(1,K_{10}\), the ratio forced by the actual \(R_9\) and \(K_0=0\), with original left first slope live. Thus put
\[
 h=a/2,\quad B_0=X(X-a)(X-h),\quad B_1=(X-h)[a-(1-K_{10})X],
 \qquad \phi=X^2(a-X).
\]
This rescaling just reparametrizes \(t\). For the independent outer representer use \(e(X)=[\ell_X,\widehat R]\) in the common \(N\)-normalization, where \(\widehat R=R^\circ\) is the already measured polynomial multiple \(H^3 U b^5R_*\) of the true opposing row direction. It need not be divided by the hull's left first slope: this scales the entire fourth row by a common unit. Form
\[
 E=\frac{a^5e-30\mathscr P e(a)}{X(X-a)},\quad
 S_0=-a E(0)(X-a)(X-h),\quad
 S_1=a\frac{E B_1(0)-E(0)B_1}{X}.
\]
All indicated divisions are polynomial. The first three column polynomials are \( (\phi,XB_0,XB_1)\), and the two alternative last columns are \(B_0,B_1\). The three moment rows are
\[
 \int X^j\omega\,C_\bullet-\rho\,s^j C_\bullet(s),\qquad
 \rho=-\frac{H^6 U\beta'}{\alpha'B_NS},\quad 0\le j\le2 .
\]
The actual \([L_8,R_9]=0\) outer row on these five columns is
\[
 a x(x-a)E(0),\quad xS_0(x),\quad xS_1(x),\quad S_0(x),\quad S_1(x),
 \qquad x=s.
\]
This is obtained from the calibrated pure contact at the literal row 8; the physical row sharing does not identify its state with the dormant row.

Let \(g_0,g_1\) be the two four-by-four determinants on the fixed three columns and the respective alternative fourth columns. The true nonzero shape-coordinate vector is in the kernel when the fourth column is the first plus \(t\) times the second; hence \(g_0+t g_1=0\). If the true left raw affine slope \(g_1\) is zero, both determinants are zero. This necessity does not divide by a fixed moment determinant or use a residue loss as if it were an exact zero.

For each determinant at the uncorrected measure, the outer row has degree at most three in \(x=s\). Terms with two replaced moment rows vanish; each single-replacement term, including its factor \(s^j\), has degree at most nine. Substitute \(s=C_2/H\) and clear uniformly by \(\alpha'B_NS H^3\):
\[
 F_i=\alpha' B_NS\,\operatorname{hom}_{H^3}(\mathrm{base}_i)
       + U\beta'\,\operatorname{hom}_{H^9}(\mathrm{adj}_i).
\]
Here \(\operatorname{hom}_{H^k}(p)=H^k p(C_2/H)\); \(\mathrm{adj}_i\) is the sum of single replacements before including the factor \(-\rho\). These are actual live clearings, and every deflated factor is drawn from the already established width guards. The two raw bidegrees \((68,60),(71,60)\) become \((39,34),(42,34)\). The two exact \(b\)-resultants with \(K_0\) have degrees 219 and 228. Their common \(a\)-gcd has degree 129, with exact irreducible factors of degrees and multiplicities \(12^2,12^2,15,66\). Both degree-twelve fields have whole joint linear \(b\)-gcd with \(U=0\); the degree-fifteen field has whole joint linear \(b\)-gcd with \(C_2-aH=0\), i.e. \(s=a\). All three violate inherited guards.

## The degree-66 width factor

The degree-66 factor happens to occur also at the preceding left moment pivot, but this proof does not infer coincident widths merely from equal \(a\)-polynomials. At the explicit place \((p,a,b)=(41,33,22)\), the exact monic \(a\)-factor retains degree 66 and has simple root 33; \(K_0\) retains \(b\)-degree three and the **whole joint residue \(b\)-gcd of all three polynomials** \(K_0,F_0,F_1\) is \(b+19\). Thus at the chosen \(a\) embedding every candidate \(b\) is integral and reduces to 22. The measured right fit against actual \(L_9\) has all needed denominator units.

Use the same independent true left profile transfer as in the [left moment proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-LEFT-MOMENT-EXIT.md). Reflect the measured right \(P,Q\) into physical coordinates and calibrate their relative scale at the active left \(h=a/2\). The true original outer equation at literal row 8 gives \(k_0+t_{\rm out} k_1=0\), where the hull parameter uses the ordinary unscaled outer-normalization slopes in the replay; \(k_0=Q(s)S_0(s)\) and \(k_1=P(s)s(s-a)E(s)B_1(0)+Q(s)S_1(s)\). Its coefficients reduce to \((2,33)\), forcing \(t_{\rm out}=31\bmod41\) without using the lost affine pivot. The measured three distinct calibrated clocks imply the monic hull must divide \(Q-P X^2(a-X)/a\). Computed residue remainder is \(18X^2+28X+29\), not zero. The [existing scalar Lean source](erk11-neighbor-right-slope-draft/ERK11NeighborKLeftMomentArithmetic.lean) contains exactly these scalar checks; no new Lean diagnostic was needed for this packet. This excludes the final degree-66 width possibility.

The deterministic standalone python-flint 0.9.0 replay uses no external data and completed in 2.878 seconds wall time on the reference host.
