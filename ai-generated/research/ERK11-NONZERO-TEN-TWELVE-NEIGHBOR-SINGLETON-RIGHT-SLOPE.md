# The neighboring right initial loss is a finite chart with a live rotated seed

**Scope.** Continue the [neighboring singleton chart](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-WIDTH-REDUCTION.md), with sole dormant physical 9 at the active singleton \(s=c_8\notin\{0,1,a,d\}\), both full plateau pairs, \(q=10,n=12\), and the inherited all-live, half-clock, both-new order-eleven chronology. The preceding [diagonal-pole exit](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-DIAGONAL-POLE-EXIT.md) gives the true measured \(u,b_9\) and original left slope. This note reduces the original right initial-slope mask to finitely many width pairs and proves the alternative right initial slope against **actual \(L_9\)** live on every such actual candidate. It does not prove the original right mask empty, or close the remaining fixed-moment, affine or regular width conditions. Reflection gives the result for the other neighboring coincidence.

## 1. The true right initial loss is the singular derivative cross block

With the original left slope against \(R_9\) live, measure actual \(L_7\) in the left derivative span. Let \(K\) pair \((D_L^0,D_L^a)\) against \((D_R^1,D_R^d)\), using \(N\) rather than \(210N\) (only directions and zeros here). Then \(K_{00}=1\). If the first right slope against actual \(L_7\) vanishes, the actual seventh-boundary contact \([L_7,R_{11}]=0\) with nonzero true extra product forces the other slope zero. Thus \(\det K=0\), and actual \(L_7\) must be a live multiple of
\[
 D_\circ=D_L^a-K_{10}D_L^0.
\]
The candidate determinant factors exactly as \(a b K_0(a,b)\), with \(b=1-d\) and \(K_0\) irreducible of bidegree \((3,3)\). Both widths are live.

It is useful to keep the actual \([L_7,R_{10}]\) and \([L_7,R_9]\) conditions before discovering their redundancy. Let \(g(X)=[D_\circ,r_X^{\rm ev}]\), in the common \(N\)-normalization. Its right primal representative has zero derivative at 1 by construction and at \(d\) when \(\det K=0\). Thus in that case
\[
 g=\gamma\mathscr Q+(\lambda+\eta X)V,\qquad
 \gamma=g(d)/\mathscr Q(d),
 \quad V=(1-X)^2(X-d)^2 .
\]
For an unconditional polynomial coefficient calculation, take
\[
 L(X)=\frac{b^5 g(X)-30g(d)\mathscr Q(X)}{(1-X)^2(X-d)},
 \qquad
 h(X)=\frac{L(X)-L(d)}{X-d}=h_0+h_1X .
\]
Both divisions are polynomial: the first uses the double anchor at 1 and the plateau subtraction at \(d\). On \(\det K=0\) one has \(L(d)=0\) and \(h=b^5(\lambda+\eta X)\).

Actual \(r_{10}=0\) and \(V_R(10)\ne0\) imply by \([L_7,R_{10}]=0\) that \(h(z)=0\), \(z=c_{10}\). This uses the **actual affine coefficient**, not the possibly zero point model \(V(z)\). Put \(z_D=HI_1-C_2 I_0,\ z_N=HI_2-C_2I_1,\ U=C_1 z_D-H z_N\). The cleared condition is \(h_0z_D+h_1z_N=0\). Actual \([L_7,R_9]=0\), where \(r_9=J_0 B_s^2(s-z)/(C_1-Hz)\) and \(V_R(9)=B_s^2\), gives the other cleared condition
\[
 30g(d)J_0 z_D+h_1 U=0 .
\]
This follows by using \(h(s)=(s-z)h_1\) and canceling the actual \(s-z\ne0\), not an assumed \(\rho_0\).

The replay checks that **both** of these actual width polynomials are exact multiples of \(K_0\), with quotient bidegrees \((5,7)\) and \((7,8)\). They cannot be counted as extra width cuts. Conversely on an actual chart with \(K_0=0\), the two identities imply \([D_\circ,R_9]=0\) using the same live mixed guards. The actual \(L_7\) direction is the unique such derivative direction because its original left slope is live. Thus \(L_7\propto D_\circ\) and its two right slopes are zero. On the actual neighboring chart the original right loss is **exactly** this determinant-zero condition.

## 2. A finite projection on the entire original right-loss curve

Work on \(K_0=0\). Keep original \(R_9\) as left opposing row, and use **actual \(L_9\)** as right opposing row. The actual right seventh-boundary/outer contacts for this choice are \([L_9,R_{11}]=0,\ [L_9,R_{10}]=0\); the left ones remain \([L_7,R_9]=0,\ [L_8,R_9]=0\). These are paid literal rows and do not assume the original right fit live. The measured \(s,z,u,v\) make the rank-one moment correction a rational width function. With the alternate right slope, both fixed moment determinants and both raw affine slopes live, the sparse fits recover two first-pool lines. Their physical projective determinant \(\Pi\) must be zero.

At the coefficient witness \((p,a,b)=(19,2,13)\) on \(K_0\), all named width and fit denominators, both determinants, both affine slopes and both actual-product normalizations are units. The exact residue gives the two oriented first-pool lines \((1,7),(14,14)\) and hence \(\Pi=1\bmod19\), not zero. This is only a coefficient witness, not a tableau reduction.

It proves finiteness **including** the masks of this rotated fit. Represent all the successive rational width expressions by numerator and denominator polynomials over \(\mathbb Z_{(19)}\), using their displayed construction. At the witness the denominators used to define the next pivot are units. Each pivot numerator that is nonzero at the witness, and the final numerator of \(\Pi\), is not divisible by \(K_0\) over \(\mathbb Q[a,b]\): this follows by reduction at the witness and the primitive \(19\)-content of \(K_0\) (for example its constant coefficient is a unit). If an actual candidate first loses one such pivot, its relevant numerator vanishes on \(K_0\); if it loses none, the final \(\Pi\) numerator vanishes. Each of these finitely many pairs of polynomials has a nonzero \(b\)-resultant. The exact \(K_0\) is irreducible and primitive in \(b\), so it has no vertical \(a\)-fiber. Hence every such actual width pair lies in a finite algebraic set. This is a width result, not a claim that unconstrained flank parameters at masks are finite or that all these widths are false.

## 3. The alternate right initial slope is never zero

There is a further actual exit for one mask of the rotated fit. If the first right slope against \(L_9\) vanishes, the other one does too. On \(\det K=0\), take the nonzero right derivative direction
\[
 R_\circ=D_R^d-K_{01}D_R^1
\]
that kills both left derivative rows, and let \(f_\circ(X)=[\ell_X,R_\circ]\) be its left primal representative. Then \(f_\circ=\gamma_*\mathscr P+(\lambda_*+\eta_*X)W\) because both left derivatives vanish. Here \(\gamma_*\ne0\): otherwise the two integrals against \(V,XV\) would kill a nonzero affine polynomial for the positive moment matrix of \(WV\), impossible. These integrals are zero because \(R_\circ\) is a derivative functional at the double-zero anchors of \(V,XV\).

Let \(\mu_s=\int (X-z)^2WV/(s-z)^2>0\) be the true pooled two-node mixed mass at \(s\), and write \(\alpha_9=(C_1-zH)/(s-z)=b_9p_9 B_s^2\). The additional test \((X-z)V\), also killed by \(R_\circ\), gives
\[
 \lambda_*+\eta_*s=-\gamma_*\alpha_9/\mu_s
\]
by true two-site quadrature of the degree-two residual. Now actual alternate double slope zero implies \([L_9,R_\circ]=0\). Evaluating \(f_\circ\) there gives
\[
 p_9=\alpha_9 A_s^2/\mu_s,\qquad b_9 A_s^2B_s^2=\mu_s .
\]
But the actual pooled mass is \(b_8 V_L(8)V_R(8)+b_9 A_s^2B_s^2\). Both \(b_8,V_L(8)\) are live; hence **\(V_R(8)=0\)**. Since \(s\notin\{1,d\}\), the literal square-clock formula says \(\kappa F_8=(1-s)^2(s-d)/b=f_R(s)\). Thus physical 8 supplies a fourth right calibration on this alternate zero-slope branch.

To project it exactly, write
\[
\begin{split}
 S&=C_2 z_D-H z_N,\qquad
 A_N=C_2(C_2-aH),\qquad B_N=(H-C_2)(C_2-dH),\\
 T_z&=z_D^2I_2-2z_Nz_DI_1+z_N^2I_0 .
\end{split}
\]
Here \(T_z\ne0\) by positivity of the true squared-clock integral. The just-earned \(u=p_9/A_s=\alpha_9 A_s/\mu_s\) is \(U A_N S/(H^3 T_z)\). Let \(L^\circ=H^3a^5 L^\perp_s\) and \(R^\circ=H^3 U b^5 R_*\) be the cleared central row parts (different from the derivative direction \(R_\circ\)). Define
\[
 \alpha'=[L^\circ,R^\circ],\quad
 \beta'=30[\ell_a,R^\circ]-a^5b^5 B_NS .
\]
The actual center diagonal and the two alternate slope equations therefore give three polynomial conditions, besides \(K_0=0\):
\[
 \alpha' T_z+\beta' U A_N S=0,\qquad
 [T_z L^\circ+30 U A_N S\ell_a,D_R^1]=0,\qquad
 [T_z L^\circ+30 U A_N S\ell_a,D_R^d]=0 .
\]
All width clearings have actual units, including \(s-z,z_D,H,U\), and no endpoint read for \(z\) is assumed.

The exact resultants of \(K_0\) against the three deflated conditions, in \(b\), have degrees \(144,66,78\); their common gcd in \(a\) has degree 66 with irreducible degrees \(12,12,12,30\). In each degree-twelve exact field the joint \(b\)-gcd is linear and its root gives \(T_z=0\), forbidden. For the degree-thirty factor use the simple place \((p,a,b)=(41,23,32)\). The \(b\)-degree of \(K_0\) remains three and the entire joint \(b\)-gcd is linear there, so every actual \(b\) at that Hensel ingress is integral and reduces to 32. All needed width and **left** fit units are checked. Do not attempt a vanished right fit.

Use the measured left first- and second-pool profiles and the two true right calibrations at the right half-clock \(e=(1+d)/2\) and at \(s=c_8\). They require
\[
 f_R(e)P(e)Q(s)-f_R(s)P(s)Q(e)=0 ,
\]
since the same live response ratio \(\kappa\) applies at both. Instead this has residue 21 modulo 41. Thus the alternative right initial slope against \(L_9\) is **always live** in the actual original right-loss chart. The finite set from §2 still needs its fixed-moment, affine and regular exits.

The deterministic standalone replay uses python-flint 0.9.0 and requires no secondary data (reference wall time 42.551 seconds under contention). The adjacent core Lean checks the scalar derivative block identity, the two-calibration implication and the two independent numerical markers; it does not formalize the tableau and field-place proof.
