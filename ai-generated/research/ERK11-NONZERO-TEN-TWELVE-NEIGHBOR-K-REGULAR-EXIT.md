# The fully pivotable neighboring singular-width curve is empty

**Scope.** Keep the ordered, all-live, half-clock two-carrier \(17\)-stage ERK11 chart with both seventh-front boundaries new, \(q=10,n=12\), the fixed full plateau pairs, and sole dormant physical 9 sharing the active singleton \(s=c_8\notin\{0,1,a,d\}\), \(b=1-d\). Assume the original right initial loss, equivalently \(K_0(a,b)=0\), and use the actual \(R_9\) and rotated actual \(L_9\) opposing rows. Both measured first slopes, both fixed moment pivots, and both raw affine slopes are live by the preceding exits. This note excludes the **remaining fully pivotable case on \(K_0=0\)**, also under reflection. Do not infer the neighboring chart with \(K_0\ne0\) is empty or change the unrestricted stage bound.

## First-pool projectivity and dependence of the second pool

Use the calibrated hulls and three moment rows from the [moment proofs](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-RIGHT-MOMENT-EXIT.md), with the two true temporal outer rows \([L_8,R_9]=0\) and \([L_9,R_{10}]=0\). The left coefficients use slopes \(1,K_{10}\); on the right both slopes are taken against actual \(L_9\), and the right outer and correction clocks remain distinct, as in the [right affine proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-RIGHT-AFFINE-EXIT.md).

In each orientation \(Y\), take the fixed polynomial columns \(\phi,YB_0,YB_1\), and the two alternative columns \(B_0,B_1\). Let \(D\) be the fixed moment determinant, and \(\mathbf c_0,\mathbf c_1\) the two negative Cramer column numerators. All seven moments have the same true normalization: by the rank-one correction, each \(3\times3\) determinant is affine in \(\rho\); clear it uniformly by \(\alpha' B_NS\) and homogenize at \(s\) (or \(1-s\)) with \(H^6\) from \(-\rho\). A common polynomial factor of \(D\) and the six Cramer entries may be removed since \(D\) is live. Homogenize the temporal row separately, then remove a common factor of its entries; the live affine slope proves that factor is live. The resulting \(D,g_0,g_1\) are all live since \(t=-g_0/g_1\ne0\).

Put \((U_*,W_*,T_*)=\mathbf c_0g_1-\mathbf c_1g_0\); the normalized shape coordinates are \((U_f,W_f,T_f)=(U_*,W_*,T_*)/(Dg_1)\). Up to live scales, the two actual shape polynomials are
\[
 \begin{split}
 p(Y)&=g_0 U_*+(-g_1T_*-g_0W_*)(Y-h),\\
 q(Y)&=U_*\phi+W_*YB_0+T_*YB_1+D(g_1B_0-g_0B_1).
 \end{split}
\]
Here \(p\) is \(P/w\) multiplied by \(Dg_1g_0\), and \(q\) is \(Q\) multiplied by \(Dg_1\). Reflect the right polynomials by \(Y=1-X\). The two first-pool lines must be projective; apply their coefficient determinant. The two second-pool shapes must also be projective, but the replay verifies **all ten** of their coefficient minors vanish identically in the exact quotient by \(K_0\) with the \(b\)-leading coefficient inverted. This supplies no independent cut.

Write \(\lambda_K(a)=[b^3]K_0\), proportional to \(30a^3-36a^2+12a-1\). On \(\lambda_K\ne0\), each quotient step uses \(\lambda_K b^3=-\sum_{j<3}[b^j]K_0\,b^j\) over \(\mathbb Q[a,\lambda_K^{-1}]\); all coefficient denominators are tracked as powers of \(\lambda_K\). The first-pool determinant has a representative of bidegree \((1216,2)\) after removing its live denominator \(\lambda_K^{297}\). After allowed width deflations take its \(b\)-resultant with \(K_0\). It has \(a\)-degree 3642, with exact irreducible degree/multiplicity list
\[
 3^9,\ 3^{594},\ 12^3,\ 12^{18},\ 12^{18},\ 15^2,\ 54^2,\
 66^3,\ 87,\ 102^3,\ 105^2,\ 108,\ 318 .
\]
The \(3^{594}\) factor is precisely \(\lambda_K\), already outside this quotient chart. It is checked separately below rather than discarded.

## Guard exits for all but degree 318

The table lists an exact \(a\)-factor of the first-pool norm and the guard whose exact \(b\)-resultant with \(K_0\) is divisible by that factor. At each displayed prime place the exact monic \(a\)-factor retains its full degree and has simple residue. The whole residue gcd in \(b\) of \(K_0\) and the first-pool numerator is the same **linear** polynomial as that of \(K_0\) and the indicated guard. The leading coefficient of \(K_0\) is a unit and its derivative at the common root in the companion normalization is the listed unit. Thus every actual \(b\) is integral, and an exact guard-zero \(K_0\) root also exists by its exact resultant and the full \(b\)-degree. Both exact roots reduce to the same simple root; Hensel uniqueness makes them equal. No guard is discarded because its residue alone was zero.

| \(a\)-factor degree, mult. | Exact lost guard | \((p,a,b)\) | \(\partial_bK_0\) residue |
|---|---|---|---:|
| 3,9 | \(b\) | \(19,12,0\) | 10 |
| 12,3 | \(S\) | \(29,27,2\) | 7 |
| 12,18 | \(J_0\) | \(17,3,2\) | 16 |
| 12,18 | \(z_D\) | \(17,12,11\) | 7 |
| 15,2 | \(C_2-aH\) | \(17,6,4\) | 1 |
| 54,2 | right \(g_0\) | \(17,6,4\) | 1 |
| 66,3 | left \(D\) | \(17,10,4\) | 8 |
| 87,1 | right \(D\) | \(23,18,20\) | 3 |
| 102,3 | right \(D\) | \(19,17,16\) | 1 |
| 105,2 | \(\alpha'\) | \(17,6,4\) | 1 |
| 108,1 | left \(D\) | \(17,6,4\) | 1 |

In particular the degree-105 branch is not a new surviving geometry. Right \(g_0\ne0\) is forced by the genuine product and \(g_1\ne0\), independently of what either reduces to at a bad place.

## The independent degree-318 exit: ordinary left plateau with the ghost correction

Use \((p,a,b)=(29,5,20)\) for degree 318. It has a simple \(a\)-ingress, full \(b\)-degree of \(K_0\), and whole linear joint \(b\)-gcd. All required fitted-width and ordinary-fit denominators are units. This case **passes** the two profile projectivities. Instead take the actual two calibrated three-node hulls \(B_L, B_R\) to form the eight-singleton polynomial
\[
 D_s(X)=-B_L(X)B_R(1-X)(X-s)(X-z).
\]
The physical row 9 is dormant at the same \(s\) as active physical 8, not a second factor of \(D_s\). Use the known same-singleton ghost remainder from the [width](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-WIDTH-REDUCTION.md) and [diagonal-pole](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-DIAGONAL-POLE-EXIT.md) packets. With a shared fitted shape \((P_*,Q_*)\) and unknown actual scale \(\gamma\), it is
\[
 D_s M_{\Omega Q_*}
 -\frac{J_0}{uv}Q_*(s)\frac{D_s}{X-s}
 +\gamma P_*^2 X(X-1)\equiv0\pmod{Q_*},
 \qquad \Omega=X(X-1)(X-a)(X-d).
\]
Here \(M_F(Z)=\int(F(X)-F(Z))/(X-Z)\). A live coefficient of the last remainder measures \(\gamma\), reducing to 5. The replay checks the quartic leading unit and the scale and root inverses. It recovers the paid cubic-response interpolant \(B_\tau\) from \(P B_\tau-Q^2=\lambda D_s\), using the measured root of linear \(P=\gamma P_*\) not in \(D_s\).

There are exactly two physical rows at \(a\). The ordinary mass \(B_a\) follows by the scalar degree-three test
\(\ell_a=\Omega/((X-a)\Omega'(a))\): subtract all eight active singleton weights and **also** the actual dormant \(b_9\ell_a(s)\). At each active singleton \(x\), the needed actual weight is \(P(x)^2/(D'(x)Q(x))\), \(D=(X-a)(X-d)D_s\). The replay computes their sum via the degree-seven coefficient after inversion modulo monic \(D_s\), whose denominator is checked. The true response at the first left plateau row is \(f=-a^2/2\). Thus its two-row moments must satisfy
\[
 (\mu-f\nu)^2-(\nu-f B_a)(\tau-f\mu)=0.
\]
Indeed each bracket is the second row's signed weight times \(g-f\), multiplied respectively by \(g,1,g^2\), where \(g\) is its response. The computed \((B_a,\nu,\mu,\tau,f,\gamma)\) are \((17,15,20,10,2,5)\bmod29\), giving **23**, not zero. This is a true extra plateau/ghost condition, not a renamed second-pool determinant.

## Finite leading-coefficient loss

Finally \(\lambda_K=0\) is an irreducible cubic \(a\)-field. At \((p,a)=(37,11)\) the monic cubic retains degree and has a simple root. The exact \(b\)-degree of \(K_0\) here is two, since its leading cubic coefficient is exactly zero and the quadratic coefficient is a unit. Its whole residue polynomial is proportional to \((b-24)(b-26)\). Both possible residues are integral and checked with actual full fits, not a division by \(\lambda_K\). The oriented first-pool line pairs are \((14,25),(14,35)\) at 24 and \((9,15),(22,8)\) at 26. Their physical projectivities are 13 and 4 modulo 37 respectively. Thus neither finite leading-loss fiber survives.

This proves the regular exact ordered-field exit. The deterministic standalone uses python-flint 0.9.0 and no external coefficient data (reference wall time 49.344 seconds). The proof is an exact mathematical and arithmetic package; no full tableau/field-place Lean formalization is asserted.
